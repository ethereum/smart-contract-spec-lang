{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# Language TypeApplications #-}

{-# LANGUAGE DuplicateRecordFields #-}

module Act.HEVM where

import Prelude hiding (GT, LT)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8 (pack)
import Data.ByteString (ByteString)
import Data.Text.Encoding (encodeUtf8)
import Control.Concurrent.Async
import Control.Monad
import Data.Foldable (sequenceA_, traverse_)
import Data.DoubleWord
import Data.Maybe
import Data.Type.Equality (TestEquality(..))
import Control.Monad.State
import Data.List.NonEmpty qualified as NE
import Data.Validation
import Data.Typeable hiding (typeRep)

import Act.HEVM_utils
import Act.Syntax.Annotated as Act
import Act.Syntax.Untyped (makeIface)
import Act.Syntax
import Act.Error
import qualified Act.Syntax.TimeAgnostic as TA
import Act.Syntax.Timing

import EVM.ABI (Sig(..))
import qualified EVM hiding (bytecode)
import qualified EVM.Types as EVM hiding (FrameState(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial, reachable)
import qualified EVM.SymExec as SymExec (EquivResult, ProofResult(..))
import EVM.SMT (SMTCex(..), assertProps)
import EVM.Solvers
import EVM.Effects
import EVM.Format as Format
import EVM.Traversals

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf

type Layout = M.Map Id (M.Map Id Integer)

type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract, Id)

-- | For each contract in the Act spec, put in a codemap its Act
-- specification, init code, and runtimecode. This is being looked up
-- when we encounter a constructor call.
type CodeMap = M.Map Id (Contract, BS.ByteString, BS.ByteString)

type EquivResult = ProofResult () (T.Text, SMTCex) T.Text T.Text

initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

slotMap :: Store -> Layout
slotMap store =
  M.map (M.map snd) store


-- * Act state monad

data ActEnv = ActEnv
  { codemap :: CodeMap
  , fresh   :: Int
  , layout  :: Layout
  , caddr   :: EVM.Expr EVM.EAddr
  , caller  :: Maybe (EVM.Expr EVM.EAddr)
  }

type ActT m a = StateT ActEnv m a

getCodemap :: Monad m => ActT m CodeMap
getCodemap = do
  env <- get
  pure env.codemap

getFreshIncr :: Monad m => ActT m Int
getFreshIncr = do
  env <- get
  let fresh = env.fresh
  put (env { fresh = fresh + 1 })
  pure (fresh + 1)

getFresh :: Monad m => ActT m Int
getFresh = do
  env <- get
  pure env.fresh

getLayout :: Monad m => ActT m Layout
getLayout = do
  env <- get
  pure env.layout

getCaddr :: Monad m => ActT m (EVM.Expr EVM.EAddr)
getCaddr = do
  env <- get
  pure env.caddr

localCaddr :: Monad m => EVM.Expr EVM.EAddr -> ActT m a -> ActT m a
localCaddr caddr m = do
  env <- get
  let caddr' = env.caddr
  let caller' = env.caller
  put (env { caddr = caddr, caller = Just caddr' })
  res <- m
  env' <- get
  put (env' { caddr = caddr', caller =  caller' })
  pure res

getCaller :: Monad m => ActT m (EVM.Expr EVM.EAddr)
getCaller = do
  env <- get
  case env.caller of
    Just c -> pure c
    Nothing -> pure $ EVM.SymAddr "caller" -- Zoe: not sure what to put here


-- * Act translation

translateConstructor :: Monad m => BS.ByteString -> Constructor -> ContractMap -> ActT m ([EVM.Expr EVM.End], Calldata, Sig, ContractMap)
translateConstructor bytecode (Constructor cid iface _ preconds _ _ upds) cmap = do
  let initmap =  M.insert initAddr (initcontract, cid) cmap
  preconds' <- mapM (toProp initmap) preconds
  cmap' <- applyUpdates initmap initmap upds
  fresh <- getFresh
  let acmap = abstractCmap initAddr cmap'
  pure ([EVM.Success (snd calldata <> preconds' <> symAddrCnstr 1 fresh) mempty (EVM.ConcreteBuf bytecode) (M.map fst cmap')], calldata, ifaceToSig iface, acmap)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code    = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.tStorage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce   = Just 1
                         }

symAddrCnstr :: Int -> Int -> [EVM.Prop]
symAddrCnstr start end = fmap (\i -> EVM.PNeg (EVM.PEq (EVM.WAddr (EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show i))) (EVM.Lit 0))) [start..end]

translateBehvs :: Monad m => ContractMap -> [Behaviour] -> ActT m [(Id, [(EVM.Expr EVM.End, ContractMap)], Calldata, Sig)]
translateBehvs cmap behvs = do
  let groups = (groupBy sameIface behvs) :: [[Behaviour]]
  mapM (\behvs' -> do
           exprs <- mapM (translateBehv cmap) behvs'
           pure (behvName behvs', exprs, behvCalldata behvs', behvSig behvs)) groups
  where
    behvCalldata (Behaviour _ _ iface _ _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    behvSig (Behaviour _ _ iface _ _ _ _ _ _:_) = ifaceToSig iface
    behvSig [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviors
    sameIface (Behaviour _ _ iface  _ _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _ _) =
      makeIface iface == makeIface iface'

    behvName (Behaviour _ _ (Interface name _) _ _ _ _ _ _:_) = name
    behvName [] = error "Internal error: behaviour groups cannot be empty"

ifaceToSig :: Interface -> Sig
ifaceToSig (Interface name args) = Sig (T.pack name) (fmap fromdecl args)
  where
    fromdecl (Decl t _) = t

translateBehv :: Monad m => ContractMap -> Behaviour -> ActT m (EVM.Expr EVM.End, ContractMap)
translateBehv cmap (Behaviour _ _ _ _ preconds caseconds _ upds ret) = do
  fresh <- getFresh
  preconds' <- mapM (toProp cmap) preconds
  caseconds' <- mapM (toProp cmap) caseconds
  ret' <- returnsToExpr cmap ret
  cmap' <- applyUpdates cmap cmap upds
  fresh' <- getFresh
  let acmap = abstractCmap initAddr cmap'
  pure (EVM.Success (preconds' <> caseconds' <> symAddrCnstr (fresh+1) fresh') mempty ret' (M.map fst cmap'), acmap)


applyUpdates :: Monad m => ContractMap -> ContractMap -> [StorageUpdate] -> ActT m ContractMap
applyUpdates readMap writeMap upds = foldM (applyUpdate readMap) writeMap upds

applyUpdate :: Monad m => ContractMap -> ContractMap -> StorageUpdate -> ActT m ContractMap
applyUpdate readMap writeMap (Update typ (Item _ _ ref) e) = do
  caddr' <- baseAddr readMap ref
  offset <- refOffset readMap ref
  let (contract, cid) = fromMaybe (error $ "Internal error: contract not found\n" <> show e) $ M.lookup caddr' writeMap
  case typ of
    SInteger -> case e of
     Create _ _ _ -> do
       fresh <- getFreshIncr
       let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
       writeMap' <- localCaddr freshAddr $ createContract readMap writeMap freshAddr e
       pure $ M.insert caddr' (updateNonce (updateStorage (EVM.SStore offset (EVM.WAddr freshAddr)) contract), cid) writeMap'
     _ -> do
      e' <- toExpr readMap e
      pure $ M.insert caddr' (updateStorage (EVM.SStore offset e') contract, cid) writeMap
    SBoolean -> do
      e' <- toExpr readMap e
      pure $ M.insert caddr' (updateStorage (EVM.SStore offset e') contract, cid) writeMap
    SByteStr -> error "Bytestrings not supported"
  where
    updateStorage :: (EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage) -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateStorage updfun (EVM.C code storage tstorage bal nonce) = EVM.C code (updfun storage) tstorage bal nonce
    updateStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    updateNonce :: EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateNonce (EVM.C code storage tstorage bal (Just n)) = EVM.C code storage tstorage bal (Just (n + 1))
    updateNonce c@(EVM.C _ _ _ _ Nothing) = c
    updateNonce (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

createContract :: Monad m => ContractMap -> ContractMap -> EVM.Expr EVM.EAddr -> Exp AInteger -> ActT m ContractMap
createContract readMap writeMap freshAddr (Create _ cid args) = do
  codemap <- getCodemap
  case M.lookup cid codemap of
    Just (Contract (Constructor _ iface _ _ _ _ upds) _, _, bytecode) -> do
      let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                           , EVM.storage = EVM.ConcreteStore mempty
                           , EVM.tStorage = EVM.ConcreteStore mempty
                           , EVM.balance = EVM.Lit 0
                           , EVM.nonce = Just 1
                           }
      let subst = makeSubstMap iface args

      let upds' = substUpds subst upds
      applyUpdates (M.insert freshAddr (contract, cid) readMap) (M.insert freshAddr (contract, cid) writeMap) upds'
    Nothing -> error "Internal error: constructor not found"
createContract _ _ _ _ = error "Internal error: constructor call expected"

-- | Substitutions

makeSubstMap :: Interface -> [TypedExp] -> M.Map Id TypedExp
makeSubstMap (Interface _ decls) args =
  M.fromList $ zipWith (\(Decl _ x) texp -> (x, texp)) decls args

substUpds :: M.Map Id TypedExp -> [StorageUpdate] -> [StorageUpdate]
substUpds subst upds = fmap (substUpd subst) upds

substUpd :: M.Map Id TypedExp -> StorageUpdate -> StorageUpdate
substUpd subst (Update s item expr) = case substItem subst item of
  ETItem SStorage  i -> Update s i (substExp subst expr)
  ETItem SCalldata _ -> error "Internal error: expecting storage item"

-- | Existential packages to abstract away from reference kinds. Needed to
-- define subtitutions. 
-- Note: it would be nice to have these abstracted in one date type that
-- abstracts the higher-kinded type, but Haskell does not allow partially
-- applied type synonyms
data ETItem t = forall k. ETItem (SRefKind k) (TItem t k)
data ERef = forall k. ERef (SRefKind k) (Ref k)

substItem :: M.Map Id TypedExp -> TItem a k -> ETItem a
substItem subst (Item st vt sref) = case substRef subst sref of
  ERef k ref -> ETItem k (Item st vt ref)

substRef :: M.Map Id TypedExp -> Ref k -> ERef
substRef _ var@(SVar _ _ _) = ERef SStorage var
substRef subst (CVar _ _ x) = case M.lookup x subst of
    Just (TExp _ (TEntry _ _ k (Item _ _ ref))) -> ERef k ref
    Just _ -> error "Internal error: cannot access fields of non-pointer var"
    Nothing -> error "Internal error: ill-formed substitution"
substRef subst (SMapping pn sref args) = case substRef subst sref of
  ERef k ref -> ERef k $ SMapping pn ref (substArgs subst args)
substRef subst (SField pn sref x y) = case substRef subst sref of
  ERef k ref -> ERef k $ SField pn ref x y

substArgs :: M.Map Id TypedExp -> [TypedExp] -> [TypedExp]
substArgs subst exps = fmap (substTExp subst) exps

substTExp :: M.Map Id TypedExp -> TypedExp -> TypedExp
substTExp subst (TExp st expr) = TExp st (substExp subst expr)

substExp :: M.Map Id TypedExp -> Exp a -> Exp a
substExp subst expr = case expr of
  And pn a b -> And pn (substExp subst a) (substExp subst b)
  Or pn a b -> Or pn (substExp subst a) (substExp subst b)
  Impl pn a b -> Impl pn (substExp subst a) (substExp subst b)
  Neg pn a -> Neg pn (substExp subst a)
  LT pn a b -> LT pn (substExp subst a) (substExp subst b)
  LEQ pn a b -> LEQ pn (substExp subst a) (substExp subst b)
  GEQ pn a b -> GEQ pn (substExp subst a) (substExp subst b)
  GT pn a b -> GT pn (substExp subst a) (substExp subst b)
  LitBool _ _ -> expr

  Add pn a b -> Add pn (substExp subst a) (substExp subst b)
  Sub pn a b -> Sub pn (substExp subst a) (substExp subst b)
  Mul pn a b -> Mul pn (substExp subst a) (substExp subst b)
  Div pn a b -> Div pn (substExp subst a) (substExp subst b)
  Mod pn a b -> Mod pn (substExp subst a) (substExp subst b)
  Exp pn a b -> Exp pn (substExp subst a) (substExp subst b)
  LitInt _ _ -> expr
  IntEnv _ _ -> expr

  IntMin _ _ -> expr
  IntMax _ _ -> expr
  UIntMin _ _ -> expr
  UIntMax _ _ -> expr
  InRange pn t a -> InRange pn t (substExp subst a)

  Cat pn a b -> Cat pn (substExp subst a) (substExp subst b)
  Slice pn a b c -> Slice pn (substExp subst a) (substExp subst b) (substExp subst c)
  ByStr _ _ -> expr
  ByLit _ _ -> expr
  ByEnv _ _ -> expr

  Eq pn st a b -> Eq pn st (substExp subst a) (substExp subst b)
  NEq pn st a b -> NEq pn st (substExp subst a) (substExp subst b)

  ITE pn a b c -> ITE pn (substExp subst a) (substExp subst b) (substExp subst c)

  TEntry _ _ SCalldata (Item st _ (CVar _ _ x)) -> case M.lookup x subst of
    Just (TExp st' exp') -> maybe (error "Internal error: type missmatch") (\Refl -> exp') $ testEquality st st'
    Nothing -> error "Internal error: Ill-defined substitution"
  TEntry pn whn _ item -> case substItem subst item of
    ETItem k' item' ->  TEntry pn whn k' item'

  Create pn a b -> Create pn a (substArgs subst b)


returnsToExpr :: Monad m => ContractMap -> Maybe TypedExp -> ActT m (EVM.Expr EVM.Buf)
returnsToExpr _ Nothing = pure $ EVM.ConcreteBuf ""
returnsToExpr cmap (Just r) = typedExpToBuf cmap r

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: Monad m => ContractMap -> TypedExp -> ActT m (EVM.Expr EVM.Buf)
typedExpToBuf cmap expr =
  case expr of
    TExp styp e -> expToBuf cmap styp e

expToBuf :: Monad m => forall a. ContractMap -> SType a -> Exp a  -> ActT m (EVM.Expr EVM.Buf)
expToBuf cmap styp e = do
  case styp of
    SInteger -> do
      e' <- toExpr cmap e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    SBoolean -> do
      e' <- toExpr cmap e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    SByteStr -> toExpr cmap e

getSlot :: Layout -> Id -> Id -> Integer
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: Monad m => ContractMap -> Ref k -> ActT m (EVM.Expr EVM.EWord)
refOffset _ (CVar _ _ _) = error "Internal error: ill-typed entry"
refOffset _ (SVar _ cid name) = do
  layout <- getLayout
  let slot = getSlot layout cid name
  pure $ EVM.Lit (fromIntegral slot)
refOffset cmap (SMapping _ ref ixs) = do
  slot <- refOffset cmap ref
  foldM (\slot' i -> do
            buf <- typedExpToBuf cmap i
            pure (EVM.keccak (buf <> (wordToBuf slot')))) slot ixs
refOffset _ (SField _ _ cid name) = do
  layout <- getLayout
  let slot = getSlot layout cid name
  pure $ EVM.Lit (fromIntegral slot)

baseAddr :: Monad m => ContractMap -> Ref k -> ActT m (EVM.Expr EVM.EAddr)
baseAddr _ (SVar _ _ _) = getCaddr
baseAddr _ (CVar _ _ _) = error "Internal error: ill-typed entry"
baseAddr cmap (SField _ ref _ _) = do
  expr <- refToExp cmap ref 
  case simplify expr of
    EVM.WAddr symaddr -> pure symaddr
    e -> error $ "Internal error: did not find a symbolic address: " <> show e
baseAddr cmap (SMapping _ ref _) = baseAddr cmap ref
-- | TODO delete
-- | find the contract that is stored in the given reference of contract type
refAddr :: Monad m => ContractMap -> Ref Storage -> ActT m (EVM.Expr EVM.EAddr)
refAddr cmap (SVar _ c x) = do
  caddr <- getCaddr
  case M.lookup caddr cmap of
    Just (EVM.C _ storage _ _ _, _) -> do
      layout <- getLayout
      let slot = EVM.Lit $ fromIntegral $ getSlot layout c x
      case simplify (EVM.SLoad slot storage) of
        EVM.WAddr symaddr -> pure symaddr
        e -> error $ "Internal error: did not find a symbolic address: " <> show e
    Just _ -> error "Internal error: unepected GVar "
    Nothing -> error "Internal error: contract not found"
refAddr cmap (SField _ ref c x) = do
  layout <- getLayout
  caddr' <- refAddr cmap ref
  case M.lookup caddr' cmap of
    Just (EVM.C _ storage _ _ _, _) -> do
      let slot = EVM.Lit $ fromIntegral $ getSlot layout c x
      case simplify (EVM.SLoad slot storage) of
        EVM.WAddr symaddr -> pure symaddr
        _ -> error "Internal error: did not find a symbolic address"
    Just _ -> error "Internal error: unepected GVar "
    Nothing -> error "Internal error: contract not found"
refAddr _ (SMapping _ _ _) = error "Internal error: mapping address not suppported"

ethEnvToWord :: Monad m => EthEnv -> ActT m (EVM.Expr EVM.EWord)
ethEnvToWord Callvalue = pure EVM.TxValue
ethEnvToWord Caller = do
  c <- getCaller
  pure $ EVM.WAddr c
ethEnvToWord Origin = pure $ EVM.WAddr (EVM.SymAddr "origin") -- Why not: pure $ EVM.Origin
ethEnvToWord Blocknumber = pure EVM.BlockNumber
ethEnvToWord Blockhash = pure $ EVM.BlockHash $ EVM.Lit 0
ethEnvToWord Chainid = pure EVM.ChainId
ethEnvToWord Gaslimit = pure EVM.GasLimit
ethEnvToWord Coinbase = pure EVM.Coinbase
ethEnvToWord Timestamp = pure EVM.Timestamp
ethEnvToWord This = do
  c <- getCaddr
  pure $ EVM.WAddr c
ethEnvToWord Nonce = error "TODO"
ethEnvToWord Calldepth = error "TODO"
ethEnvToWord Difficulty = error "TODO"

ethEnvToBuf :: EthEnv -> EVM.Expr EVM.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: Monad m => ContractMap -> Exp ABoolean -> ActT m EVM.Prop
toProp cmap = \case
  (And _ e1 e2) -> pop2 EVM.PAnd e1 e2
  (Or _ e1 e2) -> pop2 EVM.POr e1 e2
  (Impl _ e1 e2) -> pop2 EVM.PImpl e1 e2
  (Neg _ e1) -> do
    e1' <- toProp cmap e1
    pure $ EVM.PNeg e1'
  (Act.LT _ e1 e2) -> op2 EVM.PLT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.PGEq e1 e2
  (Act.GT _ e1 e2) -> op2 EVM.PGT e1 e2
  (LitBool _ b) -> pure $ EVM.PBool b
  (Eq _ SInteger e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ SInteger e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ SBoolean e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  (TEntry _ _ _ _) -> error "TODO" -- EVM.SLoad addr idx
  (InRange _ t e) -> toProp cmap (inRange t e)
  where
    op2 :: Monad m => forall a b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> a) -> Exp b -> Exp b -> ActT m a
    op2 op e1 e2 = do
      e1' <- toExpr cmap e1
      e2' <- toExpr cmap e2
      pure $ op e1' e2'

    pop2 :: Monad m => forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> ActT m a
    pop2 op e1 e2 = do
      e1' <- toProp cmap e1
      e2' <- toProp cmap e2
      pure $ op e1' e2'

pattern MAX_UINT :: EVM.W256
pattern MAX_UINT = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

-- TODO: this belongs in HEVM
stripMods :: EVM.Expr a -> EVM.Expr a
stripMods = mapExpr go
  where
    go :: EVM.Expr a -> EVM.Expr a
    go (EVM.Mod a (EVM.Lit MAX_UINT)) = a
    go a = a

toExpr :: forall a m. Monad m => ContractMap -> TA.Exp a Timed -> ActT m (EVM.Expr (ExprType a))
toExpr cmap = liftM stripMods . go
  where
    go :: Monad m => Exp a -> ActT m (EVM.Expr (ExprType a))
    go = \case
      -- booleans
      (And _ e1 e2) -> op2 EVM.And e1 e2
      (Or _ e1 e2) -> op2 EVM.Or e1 e2
      (Impl _ e1 e2) -> op2 (EVM.Or . EVM.Not) e1 e2
      (Neg _ e1) -> do
        e1' <- toExpr cmap e1
        pure $ EVM.Not e1'
      (Act.LT _ e1 e2) -> op2 EVM.LT e1 e2
      (LEQ _ e1 e2) -> op2 EVM.LEq e1 e2
      (GEQ _ e1 e2) -> op2 EVM.GEq e1 e2
      (Act.GT _ e1 e2) -> op2 EVM.GT e1 e2
      (LitBool _ b) -> pure $ EVM.Lit (fromIntegral $ fromEnum b)
      -- integers
      (Add _ e1 e2) -> op2 EVM.Add e1 e2
      (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
      (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
      (Div _ e1 e2) -> op2 EVM.Div e1 e2
      (Mod _ e1 e2) -> op2 EVM.Mod e1 e2 -- which mod?
      (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
      (LitInt _ n) -> pure $ EVM.Lit (fromIntegral n)
      (IntEnv _ env) -> ethEnvToWord env
      -- bounds
      (IntMin _ n) -> pure $ EVM.Lit (fromIntegral $ intmin n)
      (IntMax _ n) -> pure $ EVM.Lit (fromIntegral $ intmax n)
      (UIntMin _ n) -> pure $ EVM.Lit (fromIntegral $ uintmin n)
      (UIntMax _ n) -> pure $ EVM.Lit (fromIntegral $ uintmax n)
      (InRange _ t e) -> toExpr cmap (inRange t e)
      -- bytestrings
      (Cat _ _ _) -> error "TODO"
      (Slice _ _ _ _) -> error "TODO"
      -- EVM.CopySlice (toExpr start) (EVM.Lit 0) -- src and dst offset
      -- (EVM.Add (EVM.Sub (toExp end) (toExpr start)) (EVM.Lit 0)) -- size
      -- (toExpr bs) (EVM.ConcreteBuf "") -- src and dst
      (ByStr _ str) -> pure $  EVM.ConcreteBuf (B8.pack str)
      (ByLit _ bs) -> pure $ EVM.ConcreteBuf bs
      (ByEnv _ env) -> pure $ ethEnvToBuf env
      -- contracts
      (Create _ _ _) -> error "internal error: Create calls not supported in this context"
      -- polymorphic
      (Eq _ SInteger e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ SBoolean e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ _ _ _) -> error "unsupported"

      (NEq _ SInteger e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ SBoolean e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ _ _ _) -> error "unsupported"

      (TEntry _ _ _ (Item SInteger _ ref)) -> refToExp cmap ref

      e@(ITE _ _ _ _) -> error $ "Internal error: expecting flat expression. got: " <> show e

      e ->  error $ "TODO: " <> show e

    op2 :: Monad m => forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> ActT m b
    op2 op e1 e2 = do
      e1' <- toExpr cmap e1
      e2' <- toExpr cmap e2
      pure $ op e1' e2'



refToExp :: forall m k. Monad m => ContractMap -> Ref k -> ActT m (EVM.Expr EVM.EWord)
-- calldata variable
refToExp _ (CVar _ typ x) = pure $ fromCalldataFramgment $ symAbiArg (T.pack x) typ

  where
    fromCalldataFramgment :: CalldataFragment -> EVM.Expr EVM.EWord
    fromCalldataFramgment (St _ word) = word
    fromCalldataFramgment _ = error "Internal error: only static types are supported"

refToExp cmap r = do
  caddr <- baseAddr cmap r
  slot <- refOffset cmap r
  pure $ accessStorage cmap slot caddr

accessStorage :: ContractMap -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EAddr -> EVM.Expr EVM.EWord
accessStorage cmap slot addr = case M.lookup addr cmap of
  Just (EVM.C _ storage _ _ _, _) -> EVM.SLoad slot storage
  Just (EVM.GVar _, _) -> error "Internal error: contract cannot be a global variable"
  Nothing -> error "Internal error: contract not found"


inRange :: AbiType -> Exp AInteger -> Exp ABoolean
-- if the type has the type of machine word then check per operation
inRange (AbiUIntType 256) e = checkOp e
inRange (AbiIntType 256) _ = error "TODO signed integers"
-- otherwise insert range bounds
inRange t e = bound t e


checkOp :: Exp AInteger -> Exp ABoolean
checkOp (LitInt _ i) = LitBool nowhere $ i <= (fromIntegral (maxBound :: Word256))
checkOp (TEntry _ _ _ _)  = LitBool nowhere True
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
checkOp (Create _ _ _) = error "Internal error: invalid in range expression"


-- Equivalence checking

-- | Wrapper for the equivalenceCheck function of hevm
checkEquiv :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkEquiv solvers l1 l2 = do
  res <- equivalenceCheck' solvers l1 l2
  pure $ fmap toEquivRes res
  where
    toEquivRes :: SymExec.EquivResult -> EquivResult
    toEquivRes (Cex cex) = Cex ("\x1b[1mThe following input results in different behaviours\x1b[m", cex)
    toEquivRes (Qed a) = Qed a
    toEquivRes (SymExec.Unknown ()) = SymExec.Unknown ""
    toEquivRes (SymExec.Error b) = SymExec.Error (T.pack b)


-- | Create the initial contract state before analysing a contract
-- | Assumes that all calldata variables have unique names
getInitContractState :: App m => SolverGroup -> Interface -> [Pointer] -> [Exp ABoolean] -> ContractMap -> ActT m (ContractMap, Error String ())
getInitContractState solvers iface pointers preconds cmap = do
  let casts = (\(PointsTo _ x c) -> (x, c)) <$> pointers
  let casts' = groupBy (\x y -> fst x == fst y) casts
  (cmaps, checks) <- unzip <$> mapM getContractState (fmap nub casts')

  let finalmap = M.unions (cmap:cmaps)

  check <- checkAliasing finalmap cmaps
  pure (finalmap, check <* sequenceA_ checks <* checkUniqueAddr (cmap:cmaps))

  where

    getContractState :: App m => [(Id, Id)] -> ActT m (ContractMap, Error String ())
    getContractState [(x, cid)] = do
      let addr = EVM.SymAddr $ T.pack x
      codemap <- getCodemap
      case M.lookup cid codemap of
        Just (Contract (Constructor _ iface' pointers' preconds' _ _ upds) _, _, bytecode) -> do
          (icmap, check) <- getInitContractState solvers iface' pointers' preconds' M.empty
          let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                               , EVM.storage = EVM.ConcreteStore mempty
                               , EVM.tStorage = EVM.ConcreteStore mempty
                               , EVM.balance = EVM.Lit 0
                               , EVM.nonce = Just 1
                               }
          let icmap' = M.insert addr (contract, cid) icmap
          cmap' <- localCaddr addr $ applyUpdates icmap' icmap' upds
          pure (abstractCmap addr cmap', check)
        Nothing -> error $ "Internal error: Contract " <> cid <> " not found\n" <> show codemap
    getContractState [] = error "Internal error: Cast cannot be empty"
    getContractState _ = error "Error: Cannot have different casts to the same address"

    comb :: [a] -> [(a,a)]
    comb xs = [(x,y) | (x:ys) <- tails xs, y <- ys]

    checkAliasing :: App m => ContractMap -> [ContractMap] -> ActT m (Error String ())
    checkAliasing cmap' cmaps = do
      let allkeys = M.foldrWithKey (\k (_, cid) l -> (k, cid):l) [] <$> cmaps
      -- gather all tuples that must be distinct
      let allpairs = concatMap (\(l1, l2) -> (,) <$> l1 <*> l2) $ comb allkeys
      -- gatther all tuples that we know are distinct
      fresh <- getFresh
      let distpairs = (\(a1, a2) -> neqProp (makeSymAddr a1) (makeSymAddr a2)) <$> comb [1..fresh]
      let dquery = EVM.por $ (\((a1, c1),(a2, c2)) ->
                                if c1 == c2 then EVM.PEq (EVM.WAddr a1) (EVM.WAddr a2) else EVM.PBool False) <$> allpairs
      preconds' <- mapM (toProp cmap') preconds
      lift $ checkQueries (dquery:distpairs <> preconds')

    checkQueries :: App m => [EVM.Prop] -> m (Error String ())
    checkQueries queries = do
      conf <- readConfig
      res <- liftIO $ checkSat solvers (assertProps conf queries)
      checkResult (makeCalldata iface) Nothing [toVRes msg res]

    makeSymAddr n = EVM.WAddr (EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show n))
    neqProp a1 a2 = EVM.PNeg (EVM.PEq a1 a2)

    msg = "\x1b[1mThe following addresses cannot be proved distinct:\x1b[m"

    -- currently we check that all symbolic addresses are globaly unique, and fail otherwise
    -- (this is required for aliasing check to be sound when merging graphs
    -- In the future, we should implement an internal renaming of variables to ensure global
    -- uniqueness of symbolic a)ddresses.

    checkUniqueAddr :: [ContractMap] -> Error String ()
    checkUniqueAddr cmaps =
      let pairs = comb cmaps in
      assert (nowhere, "Names of symbolic adresses must be unique") (foldl (\b (c1, c2) -> S.disjoint (M.keysSet c1) (M.keysSet c2) && b) True pairs)

checkConstructors :: App m => SolverGroup -> ByteString -> ByteString -> Contract -> ActT m (Error String ContractMap)
checkConstructors solvers initcode runtimecode (Contract ctor@(Constructor _ iface pointers preconds _ _ _)  _) = do
  -- Construct the initial contract state
  (actinitmap, checks) <- getInitContractState solvers iface pointers preconds M.empty
  let hevminitmap = translateCmap actinitmap
  -- Translate Act constructor to Expr
  fresh <- getFresh
  (actbehvs, calldata, sig, cmap) <- translateConstructor runtimecode ctor actinitmap
  -- Symbolically execute bytecode
  -- TODO check if contrainsts about preexistsing fresh symbolic addresses are necessary
  solbehvs <- lift $ removeFails <$> getInitcodeBranches solvers initcode hevminitmap calldata (symAddrCnstr 1 fresh) fresh

  -- Check equivalence
  lift $ showMsg "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs actbehvs
  lift $ showMsg "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs actbehvs
  pure $ checks *> res1 *> res2 *> Success cmap
  where
    removeFails branches = filter isSuccess branches


checkBehaviours :: forall m. App m => SolverGroup -> Contract -> ContractMap -> ActT m (Error String ())
checkBehaviours solvers (Contract _ behvs) actstorage = do
  let hevmstorage = translateCmap actstorage
  fresh <- getFresh
  actbehvs <- translateBehvs actstorage behvs
  (liftM $ concatError def) $ forM actbehvs $ \(name,actbehv,calldata, sig) -> do
    let (behvs', fcmaps) = unzip actbehv

    solbehvs <- lift $ removeFails <$> getRuntimeBranches solvers hevmstorage calldata fresh
    lift $ showMsg $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    lift $ showMsg "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
    -- input space exhaustiveness check
    lift $ showMsg "\x1b[1mChecking if the input spaces are the same\x1b[m"
    res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
    pure $ traverse_ (checkStoreIsomorphism actstorage) fcmaps *> res1 *> res2

  where
    removeFails branches = filter isSuccess branches
    def = Success ()


translateCmap :: ContractMap -> [(EVM.Expr EVM.EAddr, EVM.Contract)]
translateCmap cmap = (\(addr, (c, _)) -> (addr, toContract c)) <$> M.toList cmap
  where
    toContract :: EVM.Expr EVM.EContract -> EVM.Contract
    toContract (EVM.C code storage tstorage balance nonce) = EVM.Contract
      { EVM.code        = code
      , EVM.storage     = storage
      , EVM.tStorage    = tstorage
      , EVM.origStorage = storage
      , EVM.balance     = balance
      , EVM.nonce       = nonce
      , EVM.codehash    = EVM.hashcode code
      , EVM.opIxMap     = EVM.mkOpIxMap code
      , EVM.codeOps     = EVM.mkCodeOps code
      , EVM.external    = False
      }
    toContract (EVM.GVar _) = error "Internal error: contract cannot be gvar"

-- | Checks there is no alising in a contract state
-- because every symbolic contract address is unique and storage in Act is typed
-- it suffices to check sybtactically that the contract map is a tree.
-- assumes that contracts cannot be stored to symbolic addresses
-- checkValidCmap :: ContractCmap -> Bool
-- checkValidCmap cmap =


abstractCmap :: EVM.Expr EVM.EAddr -> ContractMap -> ContractMap
abstractCmap this cmap =
  pruneContractState this $ M.mapWithKey makeContract cmap
  where
    traverseStorage ::  EVM.Expr EVM.EAddr -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
    traverseStorage addr (EVM.SStore offset (EVM.WAddr symaddr) storage) =
      if M.member symaddr cmap then
        EVM.SStore offset (EVM.WAddr symaddr) (traverseStorage addr storage)
      else traverseStorage addr storage
    traverseStorage addr (EVM.SStore _ _ storage) = traverseStorage addr storage
    traverseStorage addr (EVM.ConcreteStore _) = EVM.AbstractStore addr Nothing
    traverseStorage _ s@(EVM.AbstractStore {}) = s
    traverseStorage _ _ = error "Internal error: unexpected storage shape"

    makeContract :: EVM.Expr EVM.EAddr -> (EVM.Expr EVM.EContract, Id) -> (EVM.Expr EVM.EContract, Id)
    makeContract addr (EVM.C code storage tstorage _ _, cid) =
      (EVM.C code (simplify (traverseStorage addr (simplify storage))) tstorage (EVM.Balance addr) (Just 0), cid)
    makeContract _ (EVM.GVar _, _) = error "Internal error: contract cannot be gvar"

-- | Remove unreachable addresses from a contract map
--   Assumes:
--   1. all stores are to concrete addresses (this is OK, since this is the abstracted map
--      containing only the slots that point to contracts)
--   2. The storage map is simplfied. This means that all contract addresses stored as values
--      are of the form (EVM.WAddr symaddr)
pruneContractState :: EVM.Expr EVM.EAddr -> ContractMap -> ContractMap
pruneContractState entryaddr cmap =
  let reach = reachable entryaddr cmap in
  M.filterWithKey (\k _ -> elem k reach) cmap

  where
    -- Find reachable addresses from given address
    reachable :: EVM.Expr EVM.EAddr -> ContractMap -> [EVM.Expr EVM.EAddr]
    reachable addr cmap' = nub $ go addr []
      where
        -- Note: there state is a tree, no need to mark visisted
        go :: EVM.Expr EVM.EAddr -> [EVM.Expr EVM.EAddr] -> [EVM.Expr EVM.EAddr]
        go addr' acc =
          case M.lookup addr' cmap' of
            Just (EVM.C _ storage _ _ _, _) ->
              let addrs = getAddrs storage in
              foldr go (addr':acc) addrs
            Just (EVM.GVar _, _) -> error "Internal error: contract cannot be gvar"
            Nothing -> error "Internal error: contract not found"

    -- Find addresses mentioned in storage
    getAddrs :: EVM.Expr EVM.Storage -> [EVM.Expr EVM.EAddr]
    getAddrs (EVM.SStore _ (EVM.WAddr symaddr) storage) = symaddr : getAddrs storage
    getAddrs (EVM.SStore _ _ _) = error "Internal error: unexpected storage shape"
    getAddrs (EVM.ConcreteStore _) = error "Internal error: unexpected storage shape"
    getAddrs (EVM.AbstractStore {}) = []
    getAddrs _ = error "Internal error: unexpected storage shape"


-- | Check if two contract maps are isomorphic
-- Perform a breadth first traversal and try to find a bijection between the addresses of the two stores
-- Note that is problem is not as difficult as graph isomorphism since edges are labeld.
-- Assumes that the stores are abstracted, pruned, and simplified.
-- All writes are to a unique concrete slot and the value is a simbolic address. 
checkStoreIsomorphism :: ContractMap -> ContractMap -> Error String ()
checkStoreIsomorphism cmap1 cmap2 = bfs [(idOfAddr initAddr, idOfAddr initAddr)] [] M.empty M.empty
  where
    -- tries to find a bijective renaming between the addresses of the two maps  
    bfs :: [(T.Text, T.Text)]                         -- Queue of the addresses we are exploring (dequeue)
        -> [(T.Text, T.Text)]                         -- Queue of the addresses we are exploring (enueue) 
        -> M.Map T.Text T.Text -> M.Map T.Text T.Text -- Two renamings keeping track of the address bijection
        -> Error String ()
    bfs [] [] _ _  = pure ()
    bfs [] q2 m1 m2 = bfs (reverse q2) [] m1 m2
    bfs ((addr1, addr2):q1) q2  map1 map2 =
      case (M.lookup (EVM.SymAddr addr1) cmap1, M.lookup (EVM.SymAddr addr2) cmap2) of
        (Just (EVM.C _ storage1 _ _ _, _), Just (EVM.C _ storage2 _ _ _, _)) ->
          let addrs1 = sortOn fst $ getAddrs storage1 in
          let addrs2 = sortOn fst $ getAddrs storage2 in
          visit addrs1 addrs2 map1 map2 q2 `bindValidation` (\(renaming1, renaming2, q2') ->
          bfs q1 q2' renaming1 renaming2)
        (_, _) -> error "Internal error: contract not found in map"

    -- assumes that slots are unique because of simplifcation
    visit :: [(Int, EVM.Expr EVM.EAddr)] -> [(Int, EVM.Expr EVM.EAddr)]
          -> M.Map T.Text T.Text -> M.Map T.Text T.Text
          -> [(T.Text, T.Text)]
          -> Error String (M.Map T.Text T.Text, M.Map T.Text T.Text, [(T.Text, T.Text)])
    visit [] [] map1 map2 discovered = pure (map1, map2, discovered)
    visit ((s1, EVM.SymAddr a1):addrs1) ((s2, EVM.SymAddr a2):addrs2) map1 map2 discovered | s1 == s2 =
      case (M.lookup a1 map1, M.lookup a2 map2) of
        (Just a2', Just a1') ->
          if a2 == a2' && a1 == a1' then visit addrs1 addrs2 map1 map2 discovered
          else throw (nowhere, "The shape of the resulting map is not preserved.")
        (Nothing, Nothing) -> visit addrs1 addrs2 (M.insert a1 a2 map1) (M.insert a2 a1 map2) ((a1, a2): discovered)
        (_, _) -> throw (nowhere, "The shape of the resulting map is not preserved.")
    visit _ _ _ _  _ = throw (nowhere, "The shape of the resulting map is not preserved.")

    -- Find addresses mentioned in storage
    getAddrs :: EVM.Expr EVM.Storage -> [(Int, EVM.Expr EVM.EAddr)]
    getAddrs (EVM.SStore (EVM.Lit n) (EVM.WAddr symaddr) storage) = (fromIntegral n, symaddr) : getAddrs storage
    getAddrs (EVM.SStore _ _ _) = error "Internal error: unexpected storage shape"
    getAddrs (EVM.ConcreteStore _) = error "Internal error: unexpected storage shape"
    getAddrs (EVM.AbstractStore {}) = []
    getAddrs _ = error "Internal error: unexpected storage shape"

    idOfAddr :: EVM.Expr EVM.EAddr -> T.Text
    idOfAddr (EVM.SymAddr addr) = addr
    idOfAddr _ = error "Internal error: upecting symbolic address"

-- | Find the input space of an expr list
inputSpace :: [EVM.Expr EVM.End] -> [EVM.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: EVM.Expr EVM.End -> EVM.Prop
    aux (EVM.Success c _ _ _) = EVM.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkInputSpaces solvers l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2
  -- traceM "Solc props: "
  -- traceM $ showProps p1
  -- traceM "Act props: "
  -- traceM $ showProps p2

  conf <- readConfig

  let queries = fmap (assertProps conf) [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                                        , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  results <- liftIO $ mapConcurrently (checkSat solvers) queries
  let results' = case results of
                   [r1, r2] -> [ toVRes "\x1b[1mThe following inputs are accepted by Act but not EVM\x1b[m" r1
                               , toVRes "\x1b[1mThe following inputs are accepted by EVM but not Act\x1b[m" r2 ]
                   _ -> error "Internal error: impossible"

  case all isQed results' of
    True -> pure [Qed ()]
    False -> pure $ filter (/= Qed ()) results'



-- | Checks whether all successful EVM behaviors are within the
--   interfaces specified by Act
checkAbi :: App m => SolverGroup -> Contract -> ContractMap -> m (Error String ())
checkAbi solver contract cmap = do
  showMsg "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
  let hevmstorage = translateCmap cmap
  let txdata = EVM.AbstractBuf "txdata"
  let selectorProps = assertSelector txdata <$> nubOrd (actSigs contract)
  evmBehvs <- getRuntimeBranches solver hevmstorage (txdata, []) 0 -- TODO what freshAddr goes here?
  conf <- readConfig
  let queries =  fmap (assertProps conf) $ filter (/= []) $ fmap (checkBehv selectorProps) evmBehvs
  res <- liftIO $ mapConcurrently (checkSat solver) queries
  checkResult (txdata, []) Nothing (fmap (toVRes msg) res)

  where
    actSig (Behaviour _ _ iface _ _ _ _ _ _) = T.pack $ makeIface iface
    actSigs (Contract _ behvs) = actSig <$> behvs

    checkBehv :: [EVM.Prop] -> EVM.Expr EVM.End -> [EVM.Prop]
    checkBehv assertions (EVM.Success cnstr _ _ _) = assertions <> cnstr
    checkBehv _ (EVM.Failure _ _ _) = []
    checkBehv _ (EVM.Partial _ _ _) = []
    checkBehv _ (EVM.ITE _ _ _) = error "Internal error: HEVM behaviours must be flattened"
    checkBehv _ (EVM.GVar _) = error "Internal error: unepected GVar"

    msg = "\x1b[1mThe following function selector results in behaviors not covered by the Act spec:\x1b[m"

checkContracts :: forall m. App m => SolverGroup -> Store -> M.Map Id (Contract, BS.ByteString, BS.ByteString) -> m (Error String ())
checkContracts solvers store codemap =
  let actenv = ActEnv codemap 0 (slotMap store) (EVM.SymAddr "entrypoint") Nothing in
  liftM (concatError def) $ forM (M.toList codemap) (\(_, (contract, initcode, bytecode)) -> do
    showMsg $ "\x1b[1mChecking contract \x1b[4m" <> nameOfContract contract <> "\x1b[m"
    (res, actenv') <- flip runStateT actenv $ checkConstructors solvers initcode bytecode contract
    case res of
      Success cmap -> do
        (behvs, _) <- flip runStateT actenv' $ checkBehaviours solvers contract cmap
        abi <- checkAbi solvers contract cmap
        pure $ behvs *> abi
      Failure e -> pure $ Failure e)
  where
    def = Success ()


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
    sel = EVM.Lit $ fromIntegral (EVM.abiKeccak (encodeUtf8 sig)).unFunctionSelector


-- * Utils

toVRes :: T.Text -> CheckSatResult -> EquivResult
toVRes msg res = case res of
  Sat cex -> Cex (msg, cex)
  EVM.Solvers.Unknown e -> SymExec.Unknown (T.pack e)
  Unsat -> Qed ()
  EVM.Solvers.Error e -> SymExec.Error (T.pack e)


checkResult :: App m => Calldata -> Maybe Sig -> [EquivResult] -> m (Error String ())
checkResult calldata sig res =
  case any isCex res of
    False ->
      case any isUnknown res || any isError res of
        True -> do
          showMsg "\x1b[41mNo discrepancies found but timeouts or solver errors were encountered. \x1b[m"
          pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")
        False -> do
          showMsg "\x1b[42mNo discrepancies found.\x1b[m "
          pure $ Success ()
    True -> do
      let cexs = mapMaybe getCex res
      showMsg $ T.unpack . T.unlines $ [ "\x1b[41mNot equivalent.\x1b[m", "" , "-----", ""] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (\(msg, cex) -> msg <> "\n" <> formatCex (fst calldata) sig cex) cexs)
      pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")

-- | Pretty prints a list of hevm behaviours for debugging purposes
showBehvs :: [EVM.Expr a] -> String
showBehvs behvs = T.unpack $ T.unlines $ fmap Format.formatExpr behvs

showProps :: [EVM.Prop] -> String
showProps props = T.unpack $ T.unlines $ fmap Format.formatProp props
