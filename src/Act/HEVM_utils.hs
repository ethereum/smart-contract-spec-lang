{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}


module Act.HEVM_utils where

import Prelude hiding (GT, LT)

import Data.Containers.ListUtils (nubOrd)
import Data.List
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Control.Monad.ST (stToIO, ST)
import Control.Monad.Reader

import Act.Syntax.Annotated
import Act.Syntax.Untyped (makeIface)

import qualified EVM.Types as EVM
import EVM.Types (VM(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial, abstractVM, loadSymVM)
import EVM.Solvers
import qualified EVM.Format as Format
import qualified EVM.Fetch as Fetch
import qualified EVM as EVM
import EVM.FeeSchedule (feeSchedule)
import EVM.Effects

-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])
-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.


showMsg :: App m => String -> m ()
showMsg s = liftIO $ putStrLn s

defaultActConfig :: Config
defaultActConfig = Config
  { dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , abstRefineArith = False
  , abstRefineMem   = False
  , dumpTrace = False
  , numCexFuzz = 0
  , onlyCexFuzz = False
  , decomposeStorage = False
  }

debugActConfig :: Config
debugActConfig = defaultActConfig { dumpQueries = True, dumpExprs = True, dumpEndStates = True, debug = True }

makeCalldata :: Interface -> Calldata
makeCalldata iface@(Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x) = symAbiArg (T.pack x) typ
    makeSig = T.pack $ makeIface iface
    calldatas = fmap mkArg decls
    (cdBuf, _) = combineFragments calldatas (EVM.ConcreteBuf "")
    withSelector = writeSelector cdBuf makeSig
    sizeConstraints
      = (bufLength withSelector EVM..>= cdLen calldatas)
        EVM..&& (bufLength withSelector EVM..< (EVM.Lit (2 ^ (64 :: Integer))))
  in (withSelector, [sizeConstraints])

makeCtrCalldata :: Interface -> Calldata
makeCtrCalldata (Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x) = symAbiArg (T.pack x) typ
    calldatas = fmap mkArg decls
    -- We need to use a concrete buf as a base here because hevm bails when trying to execute with an abstract buf
    -- This is because hevm ends up trying to execute a codecopy with a symbolic size, which is unsupported atm
    -- This is probably unsound, but theres not a lot we can do about it at the moment...
    (cdBuf, props) = combineFragments' calldatas 0 (EVM.ConcreteBuf "")
  in (cdBuf, props)

-- TODO move to HEVM
combineFragments' :: [CalldataFragment] -> EVM.W256 -> EVM.Expr EVM.Buf -> (EVM.Expr EVM.Buf, [EVM.Prop])
combineFragments' fragments start base = go (EVM.Lit start) fragments (base, [])
  where
    go :: EVM.Expr EVM.EWord -> [CalldataFragment] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> (EVM.Expr EVM.Buf, [EVM.Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        St p w -> go (add idx (EVM.Lit 32)) rest (writeWord idx w buf, p <> ps)
        s -> error $ "unsupported cd fragment: " <> show s

checkPartial :: App m => [EVM.Expr EVM.End] -> m ()
checkPartial nodes =
  if (any isPartial nodes) then do
    showMsg ""
    showMsg "WARNING: hevm was only able to partially explore the given contract due to the following issues:"
    showMsg ""
    showMsg . T.unpack . T.unlines . fmap (Format.indent 2 . ("- " <>)) . fmap Format.formatPartial . nubOrd $ (getPartials nodes)
  else pure ()

-- | decompiles the given EVM bytecode into a list of Expr branches
getRuntimeBranches :: App m => SolverGroup -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> Calldata -> Int -> m [EVM.Expr EVM.End]
getRuntimeBranches solvers contracts calldata fresh = do
  prestate <- liftIO $ stToIO $ abstractVM contracts calldata fresh
  expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased prestate runExpr
  let simpl = simplify expr
  let nodes = flattenExpr simpl
  checkPartial nodes
  pure nodes


-- | decompiles the given EVM initcode into a list of Expr branches
getInitcodeBranches :: App m => SolverGroup -> BS.ByteString -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> Calldata -> [EVM.Prop] -> Int -> m [EVM.Expr EVM.End]
getInitcodeBranches solvers initcode contracts calldata precond fresh = do
  initVM <- liftIO $ stToIO $ abstractInitVM initcode contracts calldata precond fresh
  expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
  let simpl = simplify expr
  let nodes = flattenExpr simpl
  checkPartial nodes
  pure nodes

abstractInitVM :: BS.ByteString -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> [EVM.Prop] -> Int -> ST s (EVM.VM EVM.Symbolic s)
abstractInitVM contractCode contracts cd precond fresh = do
  let value = EVM.TxValue
  let code = EVM.InitCode contractCode (fst cd)
  vm <- loadSymVM (EVM.SymAddr "entrypoint", EVM.initialContract code) contracts value cd True fresh
  pure $ vm { constraints = vm.constraints <> precond }

abstractVM :: [(EVM.Expr EVM.EAddr, EVM.Contract)] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> Int -> ST s (EVM.VM EVM.Symbolic s)
abstractVM contracts cd fresh = do
  let value = EVM.TxValue
  let (c, cs) = findInitContract
  loadSymVM c cs value cd False fresh

  where
    findInitContract :: ((EVM.Expr 'EVM.EAddr, EVM.Contract), [(EVM.Expr 'EVM.EAddr, EVM.Contract)])
    findInitContract =
      case partition (\(a, _) -> a == EVM.SymAddr "entrypoint") contracts of
        ([c], cs) -> (c, cs)
        _ -> error $ "Internal error: address entrypoint expected exactly once " <> show contracts


loadSymVM
  :: (EVM.Expr EVM.EAddr, EVM.Contract)
  -> [(EVM.Expr EVM.EAddr, EVM.Contract)]
  -> EVM.Expr EVM.EWord
  -> (EVM.Expr EVM.Buf, [EVM.Prop])
  -> Bool
  -> Int
  -> ST s (EVM.VM EVM.Symbolic s)
loadSymVM (entryaddr, entrycontract) othercontracts callvalue cd create fresh =
  (EVM.makeVm $ EVM.VMOpts
     { contract = entrycontract
     , otherContracts = othercontracts
     , calldata = cd
     , baseState = EVM.AbstractBase
     , value = callvalue
     , priorityFee = 0
     , address = entryaddr
     , caller = EVM.SymAddr "caller"
     , origin = EVM.SymAddr "origin"
     , gas = ()
     , gaslimit = 0xffffffffffffffff
     , number = 0
     , timestamp = EVM.Lit 0
     , coinbase = EVM.SymAddr "coinbase"
     , prevRandao = 42069
     , maxCodeSize = 0xffffffff
     , blockGaslimit = 0
     , gasprice = 0
     , baseFee = 0
     , schedule = feeSchedule
     , chainId = 1
     , create = create
     , txAccessList = mempty
     , allowFFI = False
     , freshAddresses = fresh
     , beaconRoot = 0
     })
