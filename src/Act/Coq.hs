{-
 -
 - coq backend for act
 -
 - unsupported features:
 - + bytestrings
 - + external storage
 - + specifications for multiple contracts
 -
 -}

{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# Language DataKinds #-}


module Act.Coq where

import Prelude hiding (GT, LT)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict    as M
import qualified Data.List.NonEmpty as NE
import qualified Data.Text          as T
import Data.List (groupBy)
import Control.Monad.State

import EVM.ABI
import Act.Syntax
import Act.Syntax.Annotated

type Fresh = State Int

header :: T.Text
header = T.unlines
  [ "(* --- GENERATED BY ACT --- *)\n"
  , "Require Import Coq.ZArith.ZArith."
  , "Require Import ActLib.ActLib."
  , "Require Coq.Strings.String.\n"
  , "Module " <> strMod <> " := Coq.Strings.String."
  , "Open Scope Z_scope.\n"
  ]

-- | produce a coq representation of a specification
coq :: Act -> T.Text
coq (Act store contracts) =
  header <> (T.intercalate "\n\n" $ contractCode store <$> contracts)

contractCode :: Store -> Contract -> T.Text
contractCode store (Contract ctor@Constructor{..} behvs) = T.unlines $
  [ "Module " <> T.pack _cname <> ".\n" ]
  <> [ stateRecord ]
  <> [ base store ctor ]
  <> (concat (evalSeq (transition store) <$> groups behvs))
  <> (filter ((/=) "") $ concat (evalSeq retVal <$> groups behvs))
  <> [ reachable ctor (groups behvs) ]
  <> [ "End " <> T.pack _cname <> "." ]
  where
    groups = groupBy (\b b' -> _name b == _name b')

    stateRecord = T.unlines
      [ "Record " <> stateType <> " : Set := " <> stateConstructor
      , "{ " <> T.intercalate ("\n" <> "; ") (map decl (M.toList store'))
      , "}."
      ]

    decl (n, (s, _)) = (T.pack n) <> " : " <> slotType s

    store' = contractStore _cname store

-- | inductive definition of reachable states
reachable :: Constructor -> [[Behaviour]] -> T.Text
reachable constructor behvs = inductive
  reachableType "" (stateType <> " -> " <> stateType <> " -> Prop") body where
  body = (baseCase constructor) : concat (evalSeq reachableStep <$> behvs)

-- | non-recursive constructor for the reachable relation
baseCase :: Constructor -> T.Text
baseCase (Constructor name i@(Interface _ decls) conds _ _ _ ) =
  T.pack name <> baseSuffix <> " : " <> universal <> "\n" <> constructorBody
  where
    baseval = parens $ T.pack name <> " " <> envVar <> " " <> arguments i
    constructorBody = (indent 2) . implication . concat $
      [ coqprop <$> conds
      , [reachableType <> " " <> baseval <> " " <> baseval]
      ]
    universal =
      "forall " <> envDecl <> " " <>
      (if null decls
       then ""
       else interface i) <> ","

-- | recursive constructor for the reachable relation
reachableStep :: Behaviour -> Fresh T.Text
reachableStep (Behaviour name _ i conds cases _ _ _) =
  fresh name >>= continuation where
  continuation name' =
    return $ name'
      <> stepSuffix <> " : forall "
      <> envDecl <> " "
      <> parens (baseVar <> " " <> stateVar <> " : " <> stateType) <> " "
      <> interface i <> ",\n"
      <> constructorBody where

    constructorBody = (indent 2) . implication $
      [ reachableType <> " " <> baseVar <> " " <> stateVar ]
      <> (coqprop <$> cases ++ conds)
      <> [ reachableType <> " " <> baseVar <> " "
           <> parens (name' <> " " <> envVar <> " " <> stateVar <> " " <> arguments i)
         ]


-- | definition of a base state
base :: Store -> Constructor -> T.Text
base store (Constructor name i _ _ _ updates) =
  definition (T.pack name) (envDecl <> " " <> interface i) $
    stateval store name (\_ t -> defaultSlotValue t) updates

transition :: Store -> Behaviour -> Fresh T.Text
transition store (Behaviour name cname i _ _ _ rewrites _) = do
  name' <- fresh name
  return $ definition name' (envDecl <> " " <> stateDecl <> " " <> interface i) $
    stateval store cname (\ref _ -> storageRef ref) rewrites

-- | inductive definition of a return claim
-- ignores claims that do not specify a return value
retVal :: Behaviour -> Fresh T.Text
retVal (Behaviour name _ i conds cases _ _ (Just r)) =
  fresh name >>= continuation where
  continuation name' = return $ inductive
    (name' <> returnSuffix)
    (envDecl <> " " <> stateDecl <> " " <> interface i)
    (returnType r <> " -> Prop")
    [retname <> introSuffix <> " :\n" <> body] where


    retname = name' <> returnSuffix
    body = indent 2 . implication . concat $
      [ coqprop <$> conds ++ cases
      , [retname <> " " <> envVar <> " " <> stateVar <> " " <> arguments i <> " " <> typedexp r]
      ]

retVal _ = return ""

-- | produce a state value from a list of storage updates
-- 'handler' defines what to do in cases where a given name isn't updated
stateval :: Store -> Id -> (StorageRef -> SlotType -> T.Text) -> [StorageUpdate] -> T.Text
stateval store contract handler updates = T.unwords $ stateConstructor : fmap (\(n, (t, _)) -> updateVar store updates handler (SVar nowhere contract n) t) (M.toList store')
  where
    store' = contractStore contract store

contractStore :: Id -> Store -> Map Id (SlotType, Integer)
contractStore contract store = case M.lookup contract store of
  Just s -> s
  Nothing -> error "Internal error: cannot find constructor in store"


-- | Check is an update update a specific strage reference
eqRef :: StorageRef -> StorageUpdate -> Bool
eqRef ref (Update _ (Item _ _ ref') _) = ref == ref'

-- | Check if an update updates a location that has a given storage
-- reference as a base
baseRef :: StorageRef -> StorageUpdate -> Bool
baseRef baseref (Update _ (Item _ _ ref) _) = hasBase ref
  where
    hasBase (SVar _ _ _) = False
    hasBase (SMapping _ ref' _) = ref' == baseref || hasBase ref'
    hasBase (SField _ ref' _ _) = ref' == baseref || hasBase ref'


updateVar :: Store -> [StorageUpdate] -> (StorageRef -> SlotType -> T.Text) -> StorageRef -> SlotType -> T.Text
updateVar store updates handler focus t@(StorageValue (ContractType cid)) =
  case (constructorUpdates, fieldUpdates) of
    -- Only some fields are updated
    ([], updates'@(_:_)) -> parens $ T.unwords $ (T.pack cid <> "." <> stateConstructor) : fmap (\(n, (t', _)) -> updateVar store  updates' handler (focus' n) t') (M.toList store')
    -- No fields are updated, whole contract may be updated with some call to the constructor
    (updates', []) -> foldl (\ _ (Update _ _ e) -> coqexp e) (handler focus t) updates'
    -- The contract is updated with constructor call and field accessing. Unsupported.
    (_:_, _:_) -> error "Cannot handle multiple updates to contract variable"
  where
    focus' x = SField nowhere focus cid x
    store' = contractStore cid store

    fieldUpdates = filter (baseRef focus) updates
    constructorUpdates = filter (eqRef focus) updates

updateVar _ updates handler focus t@(StorageValue (PrimitiveType _)) =
  foldl updatedVal (handler focus t) (filter (eqRef focus) updates)
    where
      updatedVal _ (Update SByteStr _ _) = error "bytestrings not supported"
      updatedVal _ (Update _ _ e) = coqexp e

updateVar _ updates handler focus t@(StorageMapping xs _) = parens $
  lambda n <> foldl updatedMap prestate (filter (baseRef focus) updates)
    where
      prestate = parens $ handler focus t <> " " <> lambdaArgs n
      n = length xs

      updatedMap _ (Update SByteStr _ _) = error "bytestrings not supported"
      updatedMap prestate' (Update _ item e) =
        let ixs = ixsFromItem item in -- This will not work if the domain is a contract type
        "if " <> boolScope (T.intercalate " && " (map cond (zip ixs ([0..] :: [Int]))))
        <> " then " <> coqexp e
        <> " else " <> prestate'

      cond (TExp argType arg, i) = parens $ anon <> T.pack (show i) <> eqsym argType <> coqexp arg

      lambda i = if i >= 0 then "fun " <> lambdaArgs i <> " => " else ""

      lambdaArgs i = T.unwords $ map (\a -> anon <> T.pack (show a)) ([0..i-1] :: [Int])

      eqsym :: SType a -> T.Text
      eqsym argType = case argType of
        SInteger -> " =? "
        SBoolean -> " =?? "
        SByteStr -> error "bytestrings not supported"
        SContract -> error "contracts cannot be mapping arguments"


-- | produce a block of declarations from an interface
interface :: Interface -> T.Text
interface (Interface _ decls) =
  T.unwords $ map decl decls where
  decl (Decl t name) = parens $ T.pack name <> " : " <> abiType t

arguments :: Interface -> T.Text
arguments (Interface _ decls) =
  T.unwords $ map (\(Decl _ name) -> T.pack name) decls

-- | coq syntax for a slot type
slotType :: SlotType -> T.Text
slotType (StorageMapping xs t) =
  T.intercalate " -> " (map valueType (NE.toList xs ++ [t]))
slotType (StorageValue val) = valueType val

valueType :: ValueType -> T.Text
valueType (PrimitiveType t) = abiType t
valueType (ContractType cid) = T.pack cid <> "." <> "State" -- the type of a contract is its state record

-- | coq syntax for an abi type
abiType :: AbiType -> T.Text
abiType (AbiUIntType _) = "Z"
abiType (AbiIntType _) = "Z"
abiType AbiAddressType = "address"
abiType AbiStringType = strMod <> ".string"
abiType a = error $ show a

-- | coq syntax for a return type
returnType :: TypedExp -> T.Text
returnType (TExp SInteger _) = "Z"
returnType (TExp SBoolean _) = "bool"
returnType (TExp SByteStr _) = error "bytestrings not supported"
returnType (TExp SContract _) = error "Internal error: return type cannot be contract"

-- | default value for a given type
-- this is used in cases where a value is not set in the constructor
defaultSlotValue :: SlotType -> T.Text
defaultSlotValue (StorageMapping xs t) = parens $
  "fun "
  <> T.unwords (replicate (length (NE.toList xs)) "_")
  <> " => "
  <> defaultVal t
defaultSlotValue (StorageValue t) = defaultVal t

defaultVal :: ValueType -> T.Text
defaultVal (PrimitiveType t) = abiVal t
defaultVal (ContractType _) = error "Contracts must be explicitly initialized"

abiVal :: AbiType -> T.Text
abiVal (AbiUIntType _) = "0"
abiVal (AbiIntType _) = "0"
abiVal AbiAddressType = "0"
abiVal AbiStringType = strMod <> ".EmptyString"
abiVal _ = error "TODO: missing default values"

-- | coq syntax for an expression
coqexp :: Exp a -> T.Text

-- booleans
coqexp (LitBool _ True)  = "true"
coqexp (LitBool _ False) = "false"
coqexp (Var _ SBoolean _ name)  = T.pack name
coqexp (And _ e1 e2)  = parens $ "andb "   <> coqexp e1 <> " " <> coqexp e2
coqexp (Or _ e1 e2)   = parens $ "orb"     <> coqexp e1 <> " " <> coqexp e2
coqexp (Impl _ e1 e2) = parens $ "implb"   <> coqexp e1 <> " " <> coqexp e2
coqexp (Eq _ _ e1 e2)   = parens $ coqexp e1  <> " =? " <> coqexp e2
coqexp (NEq _ _ e1 e2)  = parens $ "negb " <> parens (coqexp e1  <> " =? " <> coqexp e2)
coqexp (Neg _ e)      = parens $ "negb " <> coqexp e
coqexp (LT _ e1 e2)   = parens $ coqexp e1 <> " <? "  <> coqexp e2
coqexp (LEQ _ e1 e2)  = parens $ coqexp e1 <> " <=? " <> coqexp e2
coqexp (GT _ e1 e2)   = parens $ coqexp e2 <> " <? "  <> coqexp e1
coqexp (GEQ _ e1 e2)  = parens $ coqexp e2 <> " <=? " <> coqexp e1

-- integers
coqexp (LitInt _ i) = T.pack $ show i
coqexp (Var _ SInteger _ name) = T.pack name
coqexp (Add _ e1 e2) = parens $ coqexp e1 <> " + " <> coqexp e2
coqexp (Sub _ e1 e2) = parens $ coqexp e1 <> " - " <> coqexp e2
coqexp (Mul _ e1 e2) = parens $ coqexp e1 <> " * " <> coqexp e2
coqexp (Div _ e1 e2) = parens $ coqexp e1 <> " / " <> coqexp e2
coqexp (Mod _ e1 e2) = parens $ "Z.modulo " <> coqexp e1 <> coqexp e2
coqexp (Exp _ e1 e2) = parens $ coqexp e1 <> " ^ " <> coqexp e2
coqexp (IntMin _ n)  = parens $ "INT_MIN "  <> T.pack (show n)
coqexp (IntMax _ n)  = parens $ "INT_MAX "  <> T.pack (show n)
coqexp (UIntMin _ n) = parens $ "UINT_MIN " <> T.pack (show n)
coqexp (UIntMax _ n) = parens $ "UINT_MAX " <> T.pack (show n)

coqexp (InRange _ t e) = coqexp (bound t e)

-- polymorphic
coqexp (TEntry _ w e) = entry e w
coqexp (ITE _ b e1 e2) = parens $ "if "
                               <> coqexp b
                               <> " then "
                               <> coqexp e1
                               <> " else "
                               <> coqexp e2

-- environment values
-- Relies on the assumption that Coq record fields have the same name
-- as the corresponding Haskell constructor
coqexp (IntEnv _ envVal) = parens $ T.pack (show envVal) <> " " <> envVar
-- Contracts
coqexp (Var _ SContract _ name) = T.pack name
coqexp (Create _ cid args) = parens $ T.pack cid <> "." <> T.pack cid <> " " <> envVar <> " " <> coqargs args
-- unsupported
coqexp (AsContract _ _ _) = error "contract casting not supported"
coqexp Cat {} = error "bytestrings not supported"
coqexp Slice {} = error "bytestrings not supported"
coqexp (Var _ SByteStr _ _) = error "bytestrings not supported"
coqexp ByStr {} = error "bytestrings not supported"
coqexp ByLit {} = error "bytestrings not supported"
coqexp ByEnv {} = error "bytestrings not supported"

-- | coq syntax for a proposition
coqprop :: Exp a -> T.Text
coqprop (LitBool _ True)  = "True"
coqprop (LitBool _ False) = "False"
coqprop (And _ e1 e2)  = parens $ coqprop e1 <> " /\\ " <> coqprop e2
coqprop (Or _ e1 e2)   = parens $ coqprop e1 <> " \\/ " <> coqprop e2
coqprop (Impl _ e1 e2) = parens $ coqprop e1 <> " -> " <> coqprop e2
coqprop (Neg _ e)      = parens $ "not " <> coqprop e
coqprop (Eq _ _ e1 e2)   = parens $ coqexp e1 <> " = "  <> coqexp e2
coqprop (NEq _ _ e1 e2)  = parens $ coqexp e1 <> " <> " <> coqexp e2
coqprop (LT _ e1 e2)   = parens $ coqexp e1 <> " < "  <> coqexp e2
coqprop (LEQ _ e1 e2)  = parens $ coqexp e1 <> " <= " <> coqexp e2
coqprop (GT _ e1 e2)   = parens $ coqexp e1 <> " > "  <> coqexp e2
coqprop (GEQ _ e1 e2)  = parens $ coqexp e1 <> " >= " <> coqexp e2
coqprop (InRange _ t e) = coqprop (bound t e)
coqprop e = error "ill formed proposition: " <> T.pack (show e)

-- | coq syntax for a typed expression
typedexp :: TypedExp -> T.Text
typedexp (TExp _ e) = coqexp e

entry :: TStorageItem a -> When -> T.Text
entry (Item SByteStr _ _) _ = error "bytestrings not supported"
entry _ Post = error "TODO: missing support for poststate references in coq backend"
entry (Item _ _ ref) _ = storageRef ref

storageRef :: StorageRef -> T.Text
storageRef (SVar _ _ name) = parens $ T.pack name <> " " <> stateVar
storageRef (SMapping _ ref ixs) = parens $ storageRef ref <> " " <> coqargs ixs
storageRef (SField _ ref cid name) = parens $ T.pack cid <> "." <> T.pack name <> " " <> storageRef ref

-- | coq syntax for a list of arguments
coqargs :: [TypedExp] -> T.Text
coqargs es = T.unwords (map typedexp es)

fresh :: Id -> Fresh T.Text
fresh name = state $ \s -> (T.pack (name <> show s), s + 1)

evalSeq :: Traversable t => (a -> Fresh b) -> t a -> t b
evalSeq f xs = evalState (sequence (f <$> xs)) 0

--- text manipulation ---

definition :: T.Text -> T.Text -> T.Text -> T.Text
definition name args value = T.unlines
  [ "Definition " <> name <> " " <> args <> " :="
  , value
  , "."
  ]

inductive :: T.Text -> T.Text -> T.Text -> [T.Text] -> T.Text
inductive name args indices constructors = T.unlines
  [ "Inductive " <> name <> " " <> args <> " : " <> indices <> " :="
  , (T.unlines $ ("| " <>) <$> constructors) <> "."
  ]

-- | multiline implication
implication :: [T.Text] -> T.Text
implication xs = "   " <> T.intercalate "\n-> " xs

-- | wrap text in parentheses
parens :: T.Text -> T.Text
parens s = "(" <> s <> ")"

boolScope :: T.Text -> T.Text
boolScope s = "(" <> s <> ")%bool"

indent :: Int -> T.Text -> T.Text
indent n = T.unlines . fmap (T.replicate n " " <>) . T.lines

--- constants ---

-- | string module name
strMod :: T.Text
strMod  = "Str"

-- | base state name
baseVar :: T.Text
baseVar = "BASE"

stateType :: T.Text
stateType = "State"

stateVar :: T.Text
stateVar = "STATE"

stateDecl :: T.Text
stateDecl = parens $ stateVar <> " : " <> stateType

stateConstructor :: T.Text
stateConstructor = "state"

returnSuffix :: T.Text
returnSuffix = "_ret"

baseSuffix :: T.Text
baseSuffix = "_base"

stepSuffix :: T.Text
stepSuffix = "_step"

introSuffix :: T.Text
introSuffix = "_intro"

reachableType :: T.Text
reachableType = "reachable"

envType :: T.Text
envType = "Env"

envVar :: T.Text
envVar = "ENV"

envDecl :: T.Text
envDecl = parens $ envVar <> " : " <> envType

anon :: T.Text
anon = "_binding_"
