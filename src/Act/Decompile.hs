{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}

{-|
Module      : Decompile
Description : Decompile EVM bytecode into Act

This module decompiles EVM bytecode into an Act spec. It operates as follows

1. Symbolically execute the bytecode to produce an EVM.Expr
2. Transform that Expr into one that can be safely represented using Integers
3. Convert that Expr into an Act spec (trusts solc compiler output)
4. Compile the generated Act spec back to Expr and check equivalence (solc compiler output no longer trusted)
-}
module Act.Decompile where

import Prelude hiding (LT, GT)

import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.State.Strict
import Data.ByteString (ByteString)
import Data.List
import Data.List.NonEmpty qualified as NE
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Tuple.Extra
import Data.Typeable

import EVM.ABI (AbiKind(..), abiKind)
import EVM.Fetch qualified as Fetch
import EVM.Format (formatExpr)
import EVM.Solidity hiding (SlotType(..))
import EVM.Solidity qualified as EVM (SlotType(..))
import EVM.Types qualified as EVM
import EVM.Types ((.<=), (.>=), (.==))
import EVM.Solvers (SolverGroup, checkSat, CheckSatResult(..))
import EVM.SymExec hiding (EquivResult)
import EVM.Expr qualified as Expr
import EVM.Traversals (mapExprM)
import GHC.IO hiding (liftIO)
import EVM.SMT
import EVM.Effects

import Act.Syntax.Annotated
import Act.HEVM
import Act.HEVM_utils hiding (abstractVM)
import Act.Enrich (enrich)
import Act.Error
import Act.Traversals

-- Top Level ---------------------------------------------------------------------------------------


decompile :: App m => SolcContract -> SolverGroup -> m (Either Text Act)
decompile contract solvers = do
  spec <- runExceptT $ do
    summary <- ExceptT $ summarize solvers contract
    ExceptT . pure . translate $ summary
  case spec of
    Left e -> pure . Left $ e
    Right s -> do
      valid <- verifyDecompilation solvers contract.creationCode contract.runtimeCode (enrich s)
      case valid of
        Success () -> pure . Right $ s
        Failure es -> pure . Left . T.unlines . NE.toList . fmap (T.pack . snd) $ es


-- Summarization ------------------------------------------------------------------------------------


-- | The result of summarization.
-- Contains metadata describing the abi and storage layout, as well as summaries of all branches in the input program.
data EVMContract = EVMContract
  { name :: Text
  , storageLayout :: Map Text StorageItem
  , runtime :: Map Method (Set (EVM.Expr EVM.End))
  , creation :: (Interface, Set (EVM.Expr EVM.End))
  }
  deriving (Show, Eq)

-- | Decompile the runtime and creation bytecodes into hevm expressions
summarize :: App m => SolverGroup -> SolcContract -> m (Either Text EVMContract)
summarize solvers contract = do
  runExceptT $ do
    ctor <- ExceptT creation
    behvs <- ExceptT runtime
    -- TODO: raise error if we have packed slots
    layout <- ExceptT . pure . toErr "missing storage layout in solc output" $ contract.storageLayout
    pure $ EVMContract
      { name = snd $ T.breakOnEnd ":" contract.contractName
      , storageLayout = layout
      , runtime = behvs
      , creation = ctor
      }
  where
    creation = do
      -- TODO: doesn't this have a 4 byte gap at the front?
      let fragments = fmap (uncurry symAbiArg) contract.constructorInputs
          args = combineFragments' fragments 0 (EVM.ConcreteBuf "")
      initVM <- liftIO $ stToIO $ abstractVM (fst args, []) contract.creationCode Nothing True
      expr <- Expr.simplify <$> interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
      let branches = flattenExpr expr
      if any isPartial branches
      then pure . Left $ "partially explored branches in creation code:\n" <> T.unlines (fmap formatExpr (filter isPartial branches))
      else do
        let sucs = filter Expr.isSuccess . flattenExpr $ expr
        intsafe <- Set.fromList <$> mapM (makeIntSafe solvers) sucs
        pure . Right $ (ctorIface contract.constructorInputs, intsafe)

    runtime = do
      behvs <- fmap Map.elems $ forM contract.abiMap $ \method -> do
        let calldata = first (`writeSelector` method.methodSignature)
                     . (flip combineFragments) (EVM.AbstractBuf "txdata")
                     $ fmap (uncurry symAbiArg) method.inputs
        prestate <- liftIO $ stToIO $ abstractVM (fst calldata, []) contract.runtimeCode Nothing False
        expr <- Expr.simplify <$> interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased prestate runExpr
        let branches = flattenExpr expr
        if any isPartial branches
        then pure . Left $ "partially explored branches in runtime code:\n" <> T.unlines (fmap formatExpr (filter isPartial branches))
        else do
          let sucs = filter Expr.isSuccess . flattenExpr $ expr
          intsafe <- Set.fromList <$> mapM (makeIntSafe solvers) sucs
          pure . Right $ (method, intsafe)
      pure . fmap Map.fromList . sequence $ behvs


-- Arithmetic Safety --------------------------------------------------------------------------------


-- | Transforms an EVM Expr into a form that it can be safely represented using
-- an integer encoding. This basically makes all potential points of wrapping
-- due to under/overflow explicit in the tree. This can certainly be made
-- significantly more efficient and precise (abstract interpretation?), but
-- this rather brute force attempt should be sound for now.
makeIntSafe :: forall m a. App m => SolverGroup -> EVM.Expr a -> m (EVM.Expr a)
makeIntSafe solvers expr = evalStateT (mapExprM go expr) mempty
  where
    -- Walks the expression bottom up and checks (using an smt solver) if overflow is possible for any
    -- arithmetic operations it encounters. Results from child nodes are stored and reused as we move up the tree
    go :: forall b. EVM.Expr b -> StateT (Map (EVM.Expr EVM.EWord) EVM.Prop) m (EVM.Expr b)
    go = \case
      e@(EVM.Add a b) -> binop (EVM.Add a b .>= a) a b e
      e@(EVM.Sub a b) -> binop (EVM.Sub a b .<= a) a b e
      e@(EVM.Mul a b) -> binop (EVM.Div (EVM.Mul a b) b .== a) a b e
      -- we can't encode symbolic exponents in smt, so we just always wrap
      e@(EVM.Exp {}) -> pure (EVM.Mod e (EVM.Lit MAX_UINT))
      -- TODO: It's probably sound to remove the Mod here, but signextend is pretty mysterious so keeping it here for now to be on the safe side.
      e@(EVM.SEx {}) -> pure (EVM.Mod e (EVM.Lit MAX_UINT))
      e -> pure e

    binop :: EVM.Prop -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> StateT (Map (EVM.Expr EVM.EWord) EVM.Prop) m (EVM.Expr EVM.EWord)
    binop safe l r full = do
      s <- get
      let ps = [ fromMaybe (EVM.PBool True) (Map.lookup l s)
               , fromMaybe (EVM.PBool True) (Map.lookup r s)
               , EVM.PNeg safe
               ]
      liftIO (checkSat solvers (assertProps defaultActConfig ps)) >>= \case
        Unsat -> do
          put $ Map.insert full safe s
          pure full
        _ -> pure $ EVM.Mod full (EVM.Lit MAX_UINT)



-- Translation -------------------------------------------------------------------------------------


-- | Translate the summarized bytecode into an act expression
translate :: EVMContract -> Either Text Act
translate c = do
  ctor <- mkConstructor c
  behvs <- mkBehvs c
  let contract = Contract ctor behvs
  let store = mkStore c
  pure $ Act store [contract]

-- | Build an Act Store from a solc storage layout
mkStore :: EVMContract -> Store
mkStore c = Map.singleton (T.unpack c.name) (Map.mapKeys T.unpack $ fmap fromitem c.storageLayout)
  where
    fromitem item = (convslot item.slotType, toInteger item.slot)

-- | Build an act constructor spec from the summarized bytecode
mkConstructor :: EVMContract -> Either Text Constructor
mkConstructor cs
  | Set.size (snd cs.creation) == 1 =
      case head (Set.elems (snd cs.creation)) of
        EVM.Success props _ _ store -> do
          ps <- flattenProps <$> mapM (fromProp (invertLayout cs.storageLayout)) props
          updates <- case Map.toList store of
            [(EVM.SymAddr "entrypoint", contract)] -> do
              let invLayout = invertLayout cs.storageLayout
              partitioned <- decomposeStorage invLayout contract.storage
              let initStorage = addDefaults invLayout partitioned
              mkRewrites cs.name initStorage
            [(_, _)] -> error $ "Internal Error: state contains a single entry for an unexpected contract:\n" <> show store
            [] -> error "Internal Error: unexpected empty state"
            _ -> Left "cannot decompile methods that update storage on other contracts"
          pure $ Constructor
            { _cname = T.unpack cs.name
            , _cinterface = fst cs.creation
            , _cpointers = []
            , _cpreconditions = nub ps
            , _cpostconditions = mempty
            , _invariants = mempty
            , _initialStorage = updates
            }
        _ -> error "Internal Error: mkConstructor called on a non Success branch"
  | otherwise = Left "TODO: decompile constructors with multiple branches"

  where
    addDefaults :: Map (Integer, Integer) (Text, SlotType) -> DistinctStore -> DistinctStore
    addDefaults layout (DistinctStore storage) =
      DistinctStore $ Map.foldr (\(name, typ) s -> case Map.lookup name storage of
                                    Just _ -> s
                                    Nothing -> Map.insert name (LitInt nowhere 0, typ) s) storage layout

-- | Build behaviour specs from the summarized bytecode
mkBehvs :: EVMContract -> Either Text [Behaviour]
mkBehvs c = concatMapM (\(i, bs) -> mapM (mkbehv i) (Set.toList bs)) (Map.toList c.runtime)
  where
    mkbehv :: Method -> EVM.Expr EVM.End -> Either Text Behaviour
    mkbehv method (EVM.Success props _ retBuf store) = do
      pres <- flattenProps <$> mapM (fromProp (invertLayout c.storageLayout)) props
      ret <- case method.output of
        [] -> Right Nothing
        [(_, typ)] -> case abiKind typ of
          Static -> case typ of
            AbiTupleType _ -> Left "cannot decompile methods that return a tuple"
            AbiFunctionType -> Left "cannot decompile methods that return a function pointer"
            _ -> do
              v <- fromWord (invertLayout c.storageLayout) . Expr.readWord (EVM.Lit 0) $ retBuf
              pure . Just . TExp SInteger $ v
          Dynamic -> Left "cannot decompile methods that return dynamically sized types"
        _ -> Left "cannot decompile methods with multiple return types"
      rewrites <- case Map.toList store of
        [(EVM.SymAddr "entrypoint", contract)] -> do
          partitioned <- decomposeStorage (invertLayout c.storageLayout) contract.storage
          mkRewrites c.name partitioned
        [(_, _)] -> error $ "Internal Error: state contains a single entry for an unexpected contract:\n" <> show store
        [] -> error "Internal Error: unexpected empty state"
        _ -> Left "cannot decompile methods that update storage on other contracts"
      pure $ Behaviour
        { _contract = T.unpack c.name
        , _interface = behvIface method
        , _name = T.unpack method.name
        , _pointers = []
        , _preconditions = nub pres
        , _caseconditions = mempty -- TODO: what to do here?
        , _postconditions = mempty
        , _stateUpdates = rewrites
        , _returns = ret
        }
    mkbehv _ _ = error "Internal Error: mkbehv called on a non Success branch"

mkRewrites :: Text -> DistinctStore -> Either Text [StorageUpdate]
mkRewrites cname (DistinctStore writes) = forM (Map.toList writes) $ \(name,(val,typ)) ->
  case typ of
    StorageValue v -> case v of
      PrimitiveType t -> case abiKind t of
        Static -> case t of
          AbiTupleType _ -> Left "cannot decompile methods that write to tuple in storage"
          AbiFunctionType -> Left "cannot decompile methods that store function pointers"
          _ -> do
            pure (Update SInteger (Item SInteger v (SVar nowhere (T.unpack cname) (T.unpack name))) val)
        Dynamic -> Left "cannot decompile methods that store dynamically sized types"
      ContractType {} -> Left "cannot decompile contracts that have contract types in storage"
    StorageMapping {} -> Left "cannot decompile contracts that write to mappings"

newtype DistinctStore = DistinctStore (Map Text (Exp AInteger, SlotType))

-- | Attempts to decompose an input storage expression into a map from provably distinct keys to abstract words
-- currently only supports stores where all writes are to concrete locations
-- supporting writes to symbolic locations will probably require calling an smt solver
decomposeStorage :: Map (Integer, Integer) (Text, SlotType) -> EVM.Expr EVM.Storage -> Either Text DistinctStore
decomposeStorage layout = go mempty
  where
    go :: (Map Text (Exp AInteger, SlotType)) -> EVM.Expr EVM.Storage -> Either Text DistinctStore
    go curr = \case
      EVM.AbstractStore _ _ -> pure $ DistinctStore curr
      EVM.ConcreteStore s -> do
        let s'  = Map.toList (fmap EVM.Lit s)
        new <- foldM checkedInsert curr s'
        pure $ DistinctStore new
      EVM.SStore (EVM.Lit k) v base -> do
        curr' <- checkedInsert curr (k,v)
        go curr' base
      EVM.SStore {} -> Left "cannot decompile contracts with writes to symbolic storage slots"
      EVM.GVar _ -> error "Internal Error: unexpected GVar"

    -- this is safe because:
    --   1. we traverse top down
    --   2. we only consider Lit keys
    checkedInsert :: (Map Text (Exp AInteger, SlotType)) -> (EVM.W256, EVM.Expr EVM.EWord) -> Either Text (Map Text (Exp AInteger, SlotType))
    checkedInsert curr (key, val) =
        case Map.lookup (toInteger key, 0) layout of
          Just (name, typ) ->
            case Map.lookup name curr of
              -- if a key was already written to higher in the write chain, ignore this write
              Just _ -> pure curr
              -- if this is the first time we have seen a key then insert it
              Nothing -> do
                val' <- fromWord layout val
                pure $ Map.insert name (val',typ) curr
          Nothing -> Left $ "write to a storage location that is not mentioned in the solc layout: " <> (T.pack $ show key)

-- | strips away all the extraneous ite noise that the evm bool's introduce
simplify :: forall a . Exp a -> Exp a
simplify e = if (mapTerm go e == e)
             then e
             else simplify (mapTerm go e)
  where
    go (Neg _ (Neg _ p)) = p
    go (Eq _ SInteger (ITE _ a (LitInt _ 1) (LitInt _ 0)) (LitInt _ 1)) = go a
    go (Eq _ SInteger (ITE _ a (LitInt _ 1) (LitInt _ 0)) (LitInt _ 0)) = go (Neg nowhere (go a))
    go (Eq _ SInteger (LitInt _ 1) (ITE _ a (LitInt _ 1) (LitInt _ 0))) = go a
    go (Eq _ SInteger (LitInt _ 0) (ITE _ a (LitInt _ 1) (LitInt _ 0))) = go (Neg nowhere (go a))
    -- TODO perhaps normalize before simplification to make rewrites less verbose and more robust

    -- this is the condition we get for a non overflowing uint multiplication
    --    ~ ((x != 0) & ~ (in_range 256 x))
    -- -> ~ (x != 0) | ~ (~ (in_range 256 x))
    -- -> x == 0 | in_range 256 x
    -- -> in_range 256 x
    go (Neg _ (And _ (Neg _ (Eq _ SInteger a (LitInt _ 0))) (Neg _ (InRange _ (AbiUIntType sz) (Mul _ b c)))))
      | a == b = InRange nowhere (AbiUIntType sz) (Mul nowhere a c)

    go x = x

-- splits conjunctions into separate props
flattenProps :: [Exp ABoolean] -> [Exp ABoolean]
flattenProps = concatMap go
  where
    go :: Exp ABoolean -> [Exp ABoolean]
    go (And _ a b) = [a, b]
    go a = [a]

-- | Convert an HEVM Prop into a boolean Exp
fromProp :: Map (Integer, Integer) (Text, SlotType) -> EVM.Prop -> Either Text (Exp ABoolean)
fromProp l p = simplify <$> go p
  where
    go (EVM.PEq (a :: EVM.Expr t) b) = case eqT @t @EVM.EWord of
         Nothing -> Left $ "cannot decompile props comparing equality of non word terms: " <> T.pack (show p)
         Just Refl -> liftM2 (Eq nowhere SInteger) (fromWord l a) (fromWord l b)
    go (EVM.PLT a b) = liftM2 (LT nowhere) (fromWord l a) (fromWord l b)
    go (EVM.PGT a b) = liftM2 (GT nowhere) (fromWord l a) (fromWord l b)
    go (EVM.PGEq a b) = liftM2 (GEQ nowhere) (fromWord l a) (fromWord l b)
    go (EVM.PLEq a b) = liftM2 (LEQ nowhere) (fromWord l a) (fromWord l b)
    go (EVM.PNeg a) = fmap (Neg nowhere) (go a)
    go (EVM.PAnd a b) = liftM2 (And nowhere) (go a) (go b)
    go (EVM.POr a b) = liftM2 (Or nowhere) (go a) (go b)
    go (EVM.PImpl a b) = liftM2 (Impl nowhere) (go a) (go b)
    go (EVM.PBool a) = pure $ LitBool nowhere a

-- | Convert an HEVM word into an integer Exp
fromWord :: Map (Integer, Integer) (Text, SlotType) -> EVM.Expr EVM.EWord -> Either Text (Exp AInteger)
fromWord layout w = simplify <$> go w
  where
    err e = Left $ "unable to convert to integer: " <> T.pack (show e) <> "\nouter expression: " <> T.pack (show w)
    evmbool c = ITE nowhere c (LitInt nowhere 1) (LitInt nowhere 0)

    -- identifiers
    go :: EVM.Expr EVM.EWord -> Either Text (Exp AInteger)
    go (EVM.Lit a) = Right $ LitInt nowhere (toInteger a)
    -- TODO: get the actual abi type from the compiler output
    go (EVM.Var a) = Right $ _Var Pre (AbiBytesType 32) (T.unpack a)
    go (EVM.TxValue) = Right $ IntEnv nowhere Callvalue

    -- overflow checks

    -- x + y
    -- ~x < y -> MAX_UINT - x < y -> MAX_UINT < x + y (i.e. overflow)
    go (EVM.LT (EVM.Not a) b) = do
         a' <- go a
         b' <- go b
         pure $ evmbool (Neg nowhere $ InRange nowhere (AbiUIntType 256) (Add nowhere a' b'))
    -- x * y
    -- x > 0 && MAX_UINT / x < y -> x > 0 && MAX_UINT < x * y (i.e. overflow)
    go (EVM.And (EVM.IsZero (EVM.IsZero a)) (EVM.LT (EVM.Div (EVM.Lit MAX_UINT) b) c))
      | a == b = do
        a' <- go a
        c' <- go c
        pure $ evmbool $ And nowhere (Neg nowhere (Eq nowhere SInteger a' (LitInt nowhere 0))) (Neg nowhere $ InRange nowhere (AbiUIntType 256) (Mul nowhere a' c'))
    -- a == 0 || (a * b) / a == b
    go (EVM.Or (EVM.IsZero a) (EVM.Eq b (EVM.Div (EVM.Mod (EVM.Mul c d) (EVM.Lit MAX_UINT)) e)))
      | a == c
      , a == e
      , b == d = do
        a' <- go a
        b' <- go b
        pure . evmbool $ InRange nowhere (AbiUIntType 256) (Mul nowhere a' b')


    -- SLT (max(a, length txdata) - 4) b == 0  if a - 4 = b
    -- sideconditions: a - 4 < (2 ^ 256)/2 and b < (2 ^ 256)/2 so that both numbers are positive in two's complement. Otherwise SLT might not have the intended semantics.
    -- For example SLT 42 2^255 == 0, because in two's complement 2^255  represents - 2 ^ 255
    -- Note that we already have (length txdata) <= 2 ^ 64. These restrictions could be relaxed further, but it is not needed for our intended use
    go (EVM.SLT (EVM.Mod (EVM.Add (EVM.Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc) (EVM.Max (EVM.Lit a) (EVM.BufLength (EVM.AbstractBuf "txdata")))) (EVM.Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) (EVM.Lit b)) | (a - 4 == b) && (a - 4) < 2^(255 :: Integer) && b < 2^(255 :: Integer)= pure (LitInt nowhere 0)

    -- booleans

    go (EVM.LT a b) = do
         a' <- go a
         b' <- go b
         Right $ evmbool (LT nowhere a' b')
    go (EVM.IsZero a) = do
         a' <- go a
         Right $ evmbool (Eq nowhere SInteger a' (LitInt nowhere 0))

    -- arithmetic

    go (EVM.Add a b) = liftM2 (Add nowhere) (go a) (go b)
    go (EVM.Sub a b) = liftM2 (Sub nowhere) (go a) (go b)
    go (EVM.Div a b) = liftM2 (Div nowhere) (go a) (go b)
    go (EVM.Mul a b) = liftM2 (Mul nowhere) (go a) (go b)
    go (EVM.Mod a b) = liftM2 (Mod nowhere) (go a) (go b)

    -- storage

    -- read from the prestore with a concrete index
    go (EVM.SLoad (EVM.Lit idx) (EVM.AbstractStore _ _)) =
         case Map.lookup (toInteger idx, 0) layout of
           Nothing -> Left "read from a storage location that is not present in the solc layout"
           Just (nm, tp) -> case tp of
             -- TODO: get lookup contract name by address
             StorageValue t@(PrimitiveType _) -> Right $ TEntry nowhere Pre SStorage (Item SInteger t (SVar nowhere (T.unpack "Basic") (T.unpack nm)))
             _ -> Left $ "unable to handle storage reads for variables of type: " <> T.pack (show tp)

    go e = err e


-- Verification ------------------------------------------------------------------------------------


-- | Verify that the decompiled spec is equivalent to the input bytecodes
-- This compiles the generated act spec back down to an Expr and then checks that the two are equivalent
verifyDecompilation :: App m => SolverGroup -> ByteString -> ByteString -> Act -> m (Error String ())
verifyDecompilation solvers creation runtime (Act store spec) = do
  let cmap = case spec of
               [con@(Contract cnstr _)] ->
                 Map.insert (_cname cnstr) (con, creation, runtime) mempty
               _ -> error "TODO multiple contracts"
  checkContracts solvers store cmap

-- Helpers -----------------------------------------------------------------------------------------


toErr :: Text -> Maybe a -> Either Text a
toErr _ (Just a) = Right a
toErr msg Nothing = Left msg

ctorIface :: [(Text, AbiType)] -> Interface
ctorIface args = Interface "constructor" (fmap (\(n, t) -> Decl t (T.unpack n)) args)

behvIface :: Method -> Interface
behvIface method = Interface (T.unpack method.name) (fmap (\(n, t) -> Decl t (T.unpack n)) method.inputs)

convslot :: EVM.SlotType -> SlotType
convslot (EVM.StorageMapping a b) = StorageMapping (fmap PrimitiveType a) (PrimitiveType b)
convslot (EVM.StorageValue a) = StorageValue (PrimitiveType a)

invertLayout :: Map Text StorageItem -> Map (Integer, Integer) (Text, SlotType)
invertLayout = Map.fromList . fmap go . Map.toList
  where
    go :: (Text, StorageItem) -> ((Integer, Integer), (Text, SlotType))
    go (n, i) = ((toInteger i.slot, toInteger i.offset), (n, convslot i.slotType))
