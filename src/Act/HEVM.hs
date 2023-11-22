{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}


module Act.HEVM where

import qualified Data.Map as M
import Data.List
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Lazy.IO as TL
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8 (pack)
import Data.ByteString (ByteString)
import Data.Text.Encoding (encodeUtf8)
import Control.Concurrent.Async
import Control.Monad
import Data.DoubleWord
import Data.Maybe
import System.Exit ( exitFailure )
import Control.Monad.ST (stToIO)

import Act.Syntax.Annotated as Act
import Act.Syntax.Untyped (makeIface)
import Act.Syntax

import EVM.ABI (Sig(..))
import qualified EVM.Types as EVM hiding (Contract(..), FrameState(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial)
import qualified EVM.SymExec as SymExec (EquivResult)
import EVM.SMT (SMTCex(..), assertProps, formatSMT2)
import EVM.Solvers
import qualified EVM.Format as Format
import qualified EVM.Fetch as Fetch

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf
  ExprType 'AContract = EVM.EWord -- address?

type Layout = M.Map Id (M.Map Id (EVM.Expr EVM.EAddr, Integer))

-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])

type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract)

type EquivResult = ProofResult () (T.Text, SMTCex) ()

abstRefineDefault :: EVM.AbstRefineConfig
abstRefineDefault = EVM.AbstRefineConfig False False

ethrunAddress :: EVM.Addr
ethrunAddress = EVM.Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

slotMap :: Store -> Layout
slotMap store =
  M.map (M.map (\(_, slot) -> (initAddr, slot))) store

-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.
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


-- * Act translation

translateActBehvs :: Act -> BS.ByteString -> [(Id, [EVM.Expr EVM.End], Calldata, Sig)]
translateActBehvs (Act store contracts) bytecode =
  let slots = slotMap store in
  concatMap (\(Contract _ behvs) -> translateBehvs slots bytecode behvs) contracts

translateActConstr :: Act -> BS.ByteString -> (Id, [EVM.Expr EVM.End], Calldata, Sig)
translateActConstr (Act store [Contract ctor _]) bytecode = translateConstructor (slotMap store) ctor bytecode
translateActConstr (Act _ _) _ = error "TODO multiple contracts"

translateConstructor :: Layout -> Constructor -> BS.ByteString -> (Id, [EVM.Expr EVM.End], Calldata, Sig)
translateConstructor layout (Constructor cid iface preconds _ _ upds) bytecode =
  (cid, [EVM.Success (snd calldata <> (fmap (toProp layout) preconds)) mempty (EVM.ConcreteBuf bytecode) (updatesToExpr layout cid upds initmap)],
  calldata, ifaceToSig iface)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce = Just 1
                         }
    initmap = M.fromList [(initAddr, initcontract)]

translateBehvs :: Layout -> BS.ByteString -> [Behaviour] -> [(Id, [EVM.Expr EVM.End], Calldata, Sig)]
translateBehvs layout bytecode behvs =
  let groups = (groupBy sameIface behvs) :: [[Behaviour]] in
  fmap (\behvs' -> (behvName behvs', fmap (translateBehv layout bytecode) behvs', behvCalldata behvs', behvSig behvs)) groups
  where

    behvCalldata (Behaviour _ _ iface _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    behvSig (Behaviour _ _ iface _ _ _ _ _:_) = ifaceToSig iface
    behvSig [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviours
    sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
      makeIface iface == makeIface iface'

    behvName (Behaviour _ _ (Interface name _) _ _ _ _ _:_) = name
    behvName [] = error "Internal error: behaviour groups cannot be empty"

ifaceToSig :: Interface -> Sig
ifaceToSig (Interface name args) = Sig (T.pack name) (fmap fromdecl args)
  where
    fromdecl (Decl t _) = t

translateBehv :: Layout -> BS.ByteString -> Behaviour -> EVM.Expr EVM.End
translateBehv layout bytecode (Behaviour _ cid _ preconds caseconds _ upds ret) =
  EVM.Success (fmap (toProp layout) $ preconds <> caseconds) mempty (returnsToExpr layout ret) (updatesToExpr layout cid upds initmap)
  where
    initcontract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.AbstractStore initAddr
                         , EVM.balance = EVM.Balance (EVM.SymAddr "entrypoint")
                         , EVM.nonce = Just 0
                         }
    initmap = M.fromList [(initAddr, initcontract)]

updatesToExpr :: Layout -> Id -> [StorageUpdate] -> ContractMap -> ContractMap
updatesToExpr layout cid upds initmap = foldl (flip $ updateToExpr layout cid) initmap upds

updateToExpr :: Layout -> Id -> StorageUpdate -> ContractMap -> ContractMap
updateToExpr layout cid (Update typ i@(Item _ _ ref) e) cmap =
  case typ of
    SInteger -> M.insert addr (updateStorage (EVM.SStore offset e') contract) cmap
    SBoolean -> M.insert addr (updateStorage (EVM.SStore offset e') contract) cmap
    SByteStr -> error "Bytestrings not supported"
    SContract -> error "Contracts not supported"
  where
    (addr, slot) = getSlot layout cid (idFromItem i)
    offset = offsetFromRef layout slot ref
    e' = toExpr layout e
    contract = fromMaybe (error "Internal error: contract not found") $ M.lookup addr cmap

    updateStorage :: (EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage) -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateStorage upd c'@(EVM.C _ _ _ _) = c' { EVM.storage = upd c'.storage }
    updateStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

returnsToExpr :: Layout -> Maybe TypedExp -> EVM.Expr EVM.Buf
returnsToExpr _ Nothing = EVM.ConcreteBuf ""
returnsToExpr layout (Just r) = typedExpToBuf layout r

offsetFromRef :: Layout -> Integer -> StorageRef -> EVM.Expr EVM.EWord
offsetFromRef _ slot (SVar _ _ _) = EVM.Lit $ fromIntegral slot
offsetFromRef layout slot (SMapping _ _ ixs) =
  foldl (\slot' i -> EVM.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) (EVM.Lit $ fromIntegral slot) ixs
offsetFromRef _ _ (SField _ _ _ _) = error "TODO contracts not supported"

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: Layout -> TypedExp -> EVM.Expr EVM.Buf
typedExpToBuf layout expr =
  case expr of
    TExp styp e -> expToBuf layout styp e

expToBuf :: forall a. Layout -> SType a -> Exp a  -> EVM.Expr EVM.Buf
expToBuf layout styp e =
  case styp of
    SInteger -> EVM.WriteWord (EVM.Lit 0) (toExpr layout e) (EVM.ConcreteBuf "")
    SBoolean -> EVM.WriteWord (EVM.Lit 0) (toExpr layout e) (EVM.ConcreteBuf "")
    SByteStr -> toExpr layout e
    SContract -> error "Internal error: expecting primitive type"

getSlot :: Layout -> Id -> Id -> (EVM.Expr EVM.EAddr, Integer)
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: Layout -> StorageRef -> (EVM.Expr EVM.EAddr, EVM.Expr EVM.EWord)
refOffset layout (SVar _ cid name) =
  let (addr, slot) = getSlot layout cid name in
  (addr, EVM.Lit $ fromIntegral slot)
refOffset layout (SMapping _ ref ixs) =
  let (addr, slot) = refOffset layout ref in
  (addr,
   foldl (\slot' i -> EVM.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) slot ixs)

refOffset _ _ = error "TODO"

ethEnvToWord :: EthEnv -> EVM.Expr EVM.EWord
ethEnvToWord Callvalue = EVM.TxValue
ethEnvToWord Caller = EVM.WAddr $ EVM.SymAddr "caller"
ethEnvToWord Origin = EVM.Origin
ethEnvToWord Blocknumber = EVM.BlockNumber
ethEnvToWord Blockhash = error "TODO" -- TODO argument of EVM.BlockHash ??
ethEnvToWord Chainid = EVM.ChainId
ethEnvToWord Gaslimit = EVM.GasLimit
ethEnvToWord Coinbase = EVM.Coinbase
ethEnvToWord Timestamp = EVM.Timestamp
ethEnvToWord This = error "TODO"
ethEnvToWord Nonce = error "TODO"
ethEnvToWord Calldepth = error "TODO"
ethEnvToWord Difficulty = error "TODO"

ethEnvToBuf :: EthEnv -> EVM.Expr EVM.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: Layout -> Exp ABoolean -> EVM.Prop
toProp layout = \case
  (And _ e1 e2) -> pop2 EVM.PAnd e1 e2
  (Or _ e1 e2) -> pop2 EVM.POr e1 e2
  (Impl _ e1 e2) -> pop2 EVM.PImpl e1 e2
  (Neg _ e1) -> EVM.PNeg (toProp layout e1)
  (Act.LT _ e1 e2) -> op2 EVM.PLT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.PGEq e1 e2
  (Act.GT _ e1 e2) -> op2 EVM.PGT e1 e2
  (LitBool _ b) -> EVM.PBool b
  (Eq _ SInteger e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ SInteger e1 e2) -> EVM.PNeg $ op2 EVM.PEq e1 e2
  (NEq _ SBoolean e1 e2) -> EVM.PNeg $ op2 EVM.PEq e1 e2
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  e@(Var {}) -> error $ "TODO: " <> show e
  e@(TEntry _ Pre _) -> EVM.PEq (toExpr layout e) (EVM.Lit 1)
  e@(TEntry {}) -> error $ "TODO: " <> show e -- EVM.SLoad addr idx
  (InRange _ t e) -> toProp layout (inRange t e)
  where
    op2 :: forall a b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> a) -> Exp b -> Exp b -> a
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)

    pop2 :: forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> a
    pop2 op e1 e2 = op (toProp layout e1) (toProp layout e2)



toExpr :: forall a. Layout -> Exp a -> EVM.Expr (ExprType a)
toExpr layout = \case
  -- booleans
  (And _ e1 e2) -> op2 EVM.And e1 e2
  (Or _ e1 e2) -> op2 EVM.Or e1 e2
  (Impl _ e1 e2) -> op2 (\x y -> EVM.Or (EVM.Not x) y) e1 e2
  (Neg _ e1) -> EVM.Not (toExpr layout e1)
  (Act.LT _ e1 e2) -> op2 EVM.LT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.LEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.GEq e1 e2
  (Act.GT _ e1 e2) -> op2 EVM.GT e1 e2
  (LitBool _ b) -> EVM.Lit (fromIntegral $ fromEnum $ b)
  -- integers
  (Add _ e1 e2) -> op2 EVM.Add e1 e2
  (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
  (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
  (Div _ e1 e2) -> op2 EVM.Div e1 e2
  (Mod _ e1 e2) -> op2 EVM.Mod e1 e2 -- which mod?
  (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
  (LitInt _ n) -> EVM.Lit (fromIntegral n)
  (IntEnv _ env) -> ethEnvToWord env
  -- bounds
  (IntMin _ n) -> EVM.Lit (fromIntegral $ intmin n)
  (IntMax _ n) -> EVM.Lit (fromIntegral $ intmax n)
  (UIntMin _ n) -> EVM.Lit (fromIntegral $ uintmin n)
  (UIntMax _ n) -> EVM.Lit (fromIntegral $ uintmax n)
  (InRange _ t e) -> toExpr layout (inRange t e)
  -- bytestrings
  (Cat _ _ _) -> error "TODO"
  (Slice _ _ _ _) -> error "TODO"
  -- EVM.CopySlice (toExpr start) (EVM.Lit 0) -- src and dst offset
  -- (EVM.Add (EVM.Sub (toExp end) (toExpr start)) (EVM.Lit 0)) -- size
  -- (toExpr bs) (EVM.ConcreteBuf "") -- src and dst
  (ByStr _ str) -> EVM.ConcreteBuf (B8.pack str)
  (ByLit _ bs) -> EVM.ConcreteBuf bs
  (ByEnv _ env) -> ethEnvToBuf env
  -- contracts
  (Create _ _ _) -> error "TODO"
  -- polymorphic
  (Eq _ SInteger e1 e2) -> op2 EVM.Eq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.Eq e1 e2
  (Eq _ _ _ _) -> error "unsupported"

  (NEq _ SInteger e1 e2) -> EVM.Not $ op2 EVM.Eq e1 e2
  (NEq _ SBoolean e1 e2) -> EVM.Not $ op2 EVM.Eq e1 e2
  (NEq _ _ _ _) -> error "unsupported"

  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"

  (Var _ SInteger typ x) ->  -- TODO other types
    fromCalldataFramgment $ symAbiArg (T.pack x) typ
  (Var _ SBoolean typ x) ->
    fromCalldataFramgment $ symAbiArg (T.pack x) typ

  (TEntry _ _ (Item SInteger _ ref)) ->
    let (addr, slot) = refOffset layout ref in
    EVM.SLoad slot (EVM.AbstractStore addr)
  (TEntry _ _ (Item SBoolean _ ref)) ->
    let (addr, slot) = refOffset layout ref in
    EVM.SLoad slot (EVM.AbstractStore addr)
  e ->  error $ "TODO: " <> show e

  where
    op2 :: forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> b
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)

    fromCalldataFramgment :: CalldataFragment -> EVM.Expr EVM.EWord
    fromCalldataFramgment (St _ word) = word
    fromCalldataFramgment _ = error "Internal error: only static types are supported"

inRange :: AbiType -> Exp AInteger -> Exp ABoolean
-- if the type has the type of machine word then check per operation
inRange (AbiUIntType 256) e = checkOp e
inRange (AbiIntType 256) _ = error "TODO signed integers"
-- otherwise insert range bounds
inRange t e = bound t e


checkOp :: Exp AInteger -> Exp ABoolean
checkOp (LitInt _ i) = LitBool nowhere $ i <= (fromIntegral (maxBound :: Word256))
checkOp (Var _ _ _ _)  = LitBool nowhere True
checkOp (TEntry _ _ _)  = LitBool nowhere True
checkOp e@(Add _ e1 _) = LEQ nowhere e1 e -- check for addition overflow
checkOp e@(Sub _ e1 _) = LEQ nowhere e e1
checkOp (Mul _ e1 e2) = Or nowhere (Eq nowhere SInteger e1 (LitInt nowhere 0))
                          (Impl nowhere (NEq nowhere SInteger e1 (LitInt nowhere 0))
                            (Eq nowhere SInteger e2 (Div nowhere (Mul nowhere e1 e2) e1)))
checkOp (Div _ _ _) = LitBool nowhere True
checkOp (Mod _ _ _) = LitBool nowhere True
checkOp (Exp _ _ _) = error "TODO check for exponentiation overflow"
checkOp (IntMin _ _)  = error "Internal error: invalid in range expression"
checkOp (IntMax _ _)  = error "Internal error: invalid in range expression"
checkOp (UIntMin _ _) = error "Internal error: invalid in range expression"
checkOp (UIntMax _ _) = error "Internal error: invalid in range expression"
checkOp (ITE _ _ _ _) = error "Internal error: invalid in range expression"
checkOp (IntEnv _ _) = error "Internal error: invalid in range expression"


-- * Equivalence checking

-- | Wrapper for the equivalenceCheck function of hevm
checkEquiv :: SolverGroup -> VeriOpts -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> IO [EquivResult]
checkEquiv solvers opts l1 l2 =
  fmap toEquivRes <$> equivalenceCheck' solvers l1 l2 opts
  where
    toEquivRes :: SymExec.EquivResult -> EquivResult
    toEquivRes (Cex cex) = Cex ("\x1b[1mThe following input results in different behaviours\x1b[m", cex)
    toEquivRes (Qed a) = Qed a
    toEquivRes (Timeout b) = Timeout b


checkConstructors :: SolverGroup -> VeriOpts -> ByteString -> ByteString -> Act -> IO ()
checkConstructors solvers opts initcode runtimecode act = do
  let (_, actbehvs, calldata, sig) = translateActConstr act runtimecode
  initVM <- stToIO $ abstractVM calldata initcode Nothing True
  expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
  let simpl = if True then (simplify expr) else expr
  let solbehvs = removeFails $ flattenExpr simpl
  putStrLn "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  checkResult calldata (Just sig) =<< checkEquiv solvers opts solbehvs actbehvs
  putStrLn "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  checkResult calldata (Just sig) =<< checkInputSpaces solvers opts solbehvs actbehvs
  where
    removeFails branches = filter isSuccess $ branches


checkBehaviours :: SolverGroup -> VeriOpts -> ByteString -> Act -> IO ()
checkBehaviours solvers opts bytecode act = do
  let actbehvs = translateActBehvs act bytecode
  flip mapM_ actbehvs $ \(name,behvs,calldata,sig) -> do
    solbehvs <- removeFails <$> getBranches solvers bytecode calldata
    putStrLn $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    putStrLn "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    checkResult calldata (Just sig) =<< checkEquiv solvers opts solbehvs behvs
    -- input space exhaustiveness check
    putStrLn "\x1b[1mChecking if the input spaces are the same\x1b[m"
    checkResult calldata (Just sig) =<< checkInputSpaces solvers opts solbehvs behvs
    where
      removeFails branches = filter isSuccess $ branches

-- | Find the input space of an expr list
inputSpace :: [EVM.Expr EVM.End] -> [EVM.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: EVM.Expr EVM.End -> EVM.Prop
    aux (EVM.Success c _ _ _) = EVM.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: SolverGroup -> VeriOpts -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> IO [EquivResult]
checkInputSpaces solvers opts l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2
  let queries = fmap (assertProps abstRefineDefault) [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                                                     , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  when opts.debug $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("input-query-" <> show idx <> ".smt2")
      (formatSMT2 q <> "\n\n(check-sat)")

  results <- mapConcurrently (checkSat solvers) queries
  let results' = case results of
                   [r1, r2] -> [ toVRes "\x1b[1mThe following inputs are accepted by Act but not EVM\x1b[m" r1
                               , toVRes "\x1b[1mThe following inputs are accepted by EVM but not Act\x1b[m" r2 ]
                   _ -> error "Internal error: impossible"

  case all isQed results' of
    True -> pure [Qed ()]
    False -> pure $ filter (/= Qed ()) results'


-- | Checks whether all successful EVM behaviors are withing the
-- interfaces specified by Act
checkAbi :: SolverGroup -> VeriOpts -> Act -> BS.ByteString -> IO ()
checkAbi solver opts act bytecode = do
  putStrLn "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
  let txdata = EVM.AbstractBuf "txdata"
  let selectorProps = assertSelector txdata <$> nubOrd (actSigs act)
  evmBehvs <- getBranches solver bytecode (txdata, [])
  let queries =  fmap (assertProps abstRefineDefault) $ filter (/= []) $ fmap (checkBehv selectorProps) evmBehvs

  when opts.debug $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("abi-query-" <> show idx <> ".smt2")
      (formatSMT2 q <> "\n\n(check-sat)")

  checkResult (txdata, []) Nothing =<< fmap (toVRes msg) <$> mapConcurrently (checkSat solver) queries

  where
    actSig (Behaviour _ _ iface _ _ _ _ _) = T.pack $ makeIface iface
    actSigs (Act _ [(Contract _ behvs)]) = actSig <$> behvs
    -- TODO multiple contracts
    actSigs (Act _ _) = error "TODO multiple contracts"

    checkBehv :: [EVM.Prop] -> EVM.Expr EVM.End -> [EVM.Prop]
    checkBehv assertions (EVM.Success cnstr _ _ _) = assertions <> cnstr
    checkBehv _ (EVM.Failure _ _ _) = []
    checkBehv _ (EVM.Partial _ _ _) = []
    checkBehv _ (EVM.ITE _ _ _) = error "Internal error: HEVM behaviours must be flattened"
    checkBehv _ (EVM.GVar _) = error "Internal error: unepected GVar"

    msg = "\x1b[1mThe following function selector results in behaviors not covered by the Act spec:\x1b[m"

-- | decompiles the given EVM bytecode into a list of Expr branches
getBranches :: SolverGroup -> BS.ByteString -> Calldata -> IO [EVM.Expr EVM.End]
getBranches solvers bs calldata = do
      let bytecode = if BS.null bs then BS.pack [0] else bs
      prestate <- stToIO $ abstractVM calldata bytecode Nothing False
      expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased prestate runExpr
      let simpl = if True then (simplify expr) else expr
      let nodes = flattenExpr simpl

      when (any isPartial nodes) $ do
        putStrLn ""
        putStrLn "WARNING: hevm was only able to partially explore the given contract due to the following issues:"
        putStrLn ""
        TIO.putStrLn . T.unlines . fmap (Format.indent 2 . ("- " <>)) . fmap Format.formatPartial . nubOrd $ (getPartials nodes)

      pure nodes

readSelector :: EVM.Expr EVM.Buf -> EVM.Expr EVM.EWord
readSelector txdata =
    EVM.JoinBytes (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.ReadByte (EVM.Lit 0x0) txdata)
                  (EVM.ReadByte (EVM.Lit 0x1) txdata)
                  (EVM.ReadByte (EVM.Lit 0x2) txdata)
                  (EVM.ReadByte (EVM.Lit 0x3) txdata)


assertSelector ::  EVM.Expr EVM.Buf -> T.Text -> EVM.Prop
assertSelector txdata sig =
  EVM.PNeg (EVM.PEq sel (readSelector txdata))
  where
    sel = EVM.Lit $ fromIntegral $ (EVM.abiKeccak (encodeUtf8 sig)).unFunctionSelector



-- * Utils

toVRes :: T.Text -> CheckSatResult -> EquivResult
toVRes msg res = case res of
  Sat cex -> Cex (msg, cex)
  EVM.Solvers.Unknown -> Timeout ()
  Unsat -> Qed ()
  Error e -> error $ "Internal Error: solver responded with error: " <> show e


checkResult :: Calldata -> Maybe Sig -> [EquivResult] -> IO ()
checkResult calldata sig res =
  case any isCex res of
    False -> do
      putStrLn "\x1b[42mNo discrepancies found\x1b[m"
      when (any isTimeout res) $ do
        putStrLn "But timeout(s) occurred"
        exitFailure
    True -> do
      let cexs = mapMaybe getCex res
      TIO.putStrLn . T.unlines $
        [ "\x1b[41mNot equivalent.\x1b[m"
        , "" , "-----", ""
        ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (\(msg, cex) -> msg <> "\n" <> formatCex (fst calldata) sig cex) cexs)
      exitFailure
