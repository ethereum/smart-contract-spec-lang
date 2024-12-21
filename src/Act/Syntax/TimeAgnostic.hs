{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}

{-|
Module      : Syntax.TimeAgnostic
Description : AST data types where implicit timings may or may not have been made explicit.

This module only exists to increase code reuse; the types defined here won't
be used directly, but will be instantiated with different timing parameters
at different steps in the AST refinement process. This way we don't have to
update mirrored types, instances and functions in lockstep.

Some terms in here are always 'Timed'. This indicates that their timing must
*always* be explicit. For the rest, all timings must be implicit in source files
(i.e. 'Untimed'), but will be made explicit (i.e. 'Timed') during refinement.
-}

module Act.Syntax.TimeAgnostic (module Act.Syntax.TimeAgnostic) where

import Control.Applicative (empty)
import Prelude hiding (GT, LT)

import Data.Aeson
import Data.Aeson.Types
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.List (genericTake,genericDrop)
import Data.Map.Strict (Map)
import Data.String (fromString)
import Data.Text (pack)
import Data.Vector (fromList)
import Data.Singletons
import Data.Kind
import Data.Type.Equality (TestEquality(..), (:~:)(..))

-- Reexports

import Act.Parse          as Act.Syntax.TimeAgnostic (nowhere)
import Act.Syntax.Types   as Act.Syntax.TimeAgnostic
import Act.Syntax.Timing  as Act.Syntax.TimeAgnostic
import Act.Syntax.Untyped as Act.Syntax.TimeAgnostic (Id, Pn, Interface(..), EthEnv(..), Decl(..), SlotType(..), ValueType(..), Pointer(..))

-- AST post typechecking
data Act t = Act Store [Contract t]
deriving instance Show (InvariantPred t) => Show (Act t)
deriving instance Eq   (InvariantPred t) => Eq   (Act t)

data Contract t = Contract (Constructor t) [Behaviour t]
deriving instance Show (InvariantPred t) => Show (Contract t)
deriving instance Eq   (InvariantPred t) => Eq   (Contract t)

-- For each contract, it stores the type of a storage variables and
-- the order in which they are declared
type Store = Map Id (Map Id (SlotType, Integer))

-- | Represents a contract level invariant along with some associated metadata.
-- The invariant is defined in the context of the constructor, but must also be
-- checked against each behaviour in the contract, and thus may reference variables
-- that are not present in a given behaviour (constructor args, or storage
-- variables that are not referenced in the behaviour), so we additionally
-- attach some constraints over the variables referenced by the predicate in
-- the `_ipreconditions` and `_istoragebounds` fields. These fields are
-- seperated as the constraints derived from the types of the storage
-- references must be treated differently in the constructor specific queries
-- (as the storage variables have no prestate in the constructor...), wheras
-- the constraints derived from the types of the environment variables and
-- calldata args (stored in _ipreconditions) have a uniform semantics over both
-- the constructor and behaviour claims.
data Invariant t = Invariant
  { _icontract :: Id
  , _ipreconditions :: [Exp ABoolean t]
  , _istoragebounds :: [Exp ABoolean t]
  , _predicate :: InvariantPred t
  }
deriving instance Show (InvariantPred t) => Show (Invariant t)
deriving instance Eq   (InvariantPred t) => Eq   (Invariant t)

-- | Invariant predicates are either a single predicate without explicit timing or
-- two predicates which explicitly reference the pre- and the post-state, respectively.
-- Furthermore, if we know the predicate type we can always deduce the timing, not
-- only vice versa.
type family InvariantPred (t :: Timing) = (pred :: Type) | pred -> t where
  InvariantPred Untimed = Exp ABoolean Untimed
  InvariantPred Timed   = (Exp ABoolean Timed, Exp ABoolean Timed)

data Constructor t = Constructor
  { _cname :: Id
  , _cinterface :: Interface
  , _cpointers :: [Pointer]
  , _cpreconditions :: [Exp ABoolean t]
  , _cpostconditions :: [Exp ABoolean Timed]
  , _invariants :: [Invariant t]
  , _initialStorage :: [StorageUpdate t]
  }
deriving instance Show (InvariantPred t) => Show (Constructor t)
deriving instance Eq   (InvariantPred t) => Eq   (Constructor t)


data Behaviour t = Behaviour
  { _name :: Id
  , _contract :: Id
  , _interface :: Interface
  , _pointers :: [Pointer]
  , _preconditions :: [Exp ABoolean t] -- if preconditions are not satisfied execution is reverted
  , _caseconditions :: [Exp ABoolean t] -- if preconditions are satisfied and a case condition is not, some other instance of the bahaviour should apply
  , _postconditions :: [Exp ABoolean Timed]
  , _stateUpdates :: [StorageUpdate t]
  , _returns :: Maybe (TypedExp Timed)
  } deriving (Show, Eq)


data StorageUpdate (t :: Timing) where
  Update :: SType a -> TItem a Storage t -> Exp a t -> StorageUpdate t
deriving instance Show (StorageUpdate t)

instance Eq (StorageUpdate t) where
  Update SType i1 e1 == Update SType i2 e2 = eqS' i1 i2 && eqS e1 e2

_Update :: SingI a => TItem a Storage t -> Exp a t -> StorageUpdate t
_Update item expr = Update sing item expr

data StorageLocation (t :: Timing) where
  Loc :: SType a -> TItem a Storage t -> StorageLocation t
deriving instance Show (StorageLocation t)

_Loc :: TItem a Storage t -> StorageLocation t
_Loc item@(Item s _ _) = Loc s item

instance Eq (StorageLocation t) where
  Loc SType i1 == Loc SType i2 = eqS' i1 i2


-- | Distinguish the type of Refs to calladata variables and storage
data RefKind = Storage | Calldata
  deriving (Show, Eq)
  
data SRefKind (k :: RefKind) where
  SStorage  :: SRefKind Storage
  SCalldata :: SRefKind Calldata
  
type instance Sing = SRefKind

instance Show (SRefKind a) where
  show = \case
    SStorage -> "SSTorage"
    SCalldata -> "SCalldata"

instance TestEquality SRefKind where
  testEquality SStorage SStorage = Just Refl
  testEquality SCalldata SCalldata = Just Refl
  testEquality _ _ = Nothing

-- | Helper pattern to retrieve the 'SingI' instances of the type represented by
-- an 'SKind'.
pattern SRefKind :: () => (SingI a) => SRefKind a
pattern SRefKind <- Sing
{-# COMPLETE SRefKind #-}

-- | Compare equality of two Items parametrized by different RefKinds.
eqKind :: forall (a :: RefKind) (b :: RefKind) f t t'. (SingI a, SingI b, Eq (f t a t')) => f t a t' -> f t b t' -> Bool
eqKind fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | Reference to an item in storage or a variable. It can be either a
-- storage or calldata variable, a map lookup, or a field selector.
-- annotated with two identifiers: the contract that they belong to
-- and their name.
data Ref (k :: RefKind) (t :: Timing) where
  CVar :: Pn -> AbiType -> Id -> Ref Calldata t     -- Calldata variable
  SVar :: Pn -> Id -> Id -> Ref Storage t           -- Storage variable. First Id is the contract the var belogs to
  SMapping :: Pn -> Ref k t -> [TypedExp t] -> Ref k t
  SField :: Pn -> Ref k t -> Id -> Id -> Ref k t    -- first Id is the contract the field belogs to
deriving instance Show (Ref k t)

instance Eq (Ref k t) where
  CVar _ at x      == CVar _ at' x'      = at == at' && x == x'
  SVar _ c x       == SVar _ c' x'       = c == c' && x == x'
  SMapping _ r ixs == SMapping _ r' ixs' = r == r' && ixs == ixs'
  SField _ r c x   == SField _ r' c' x'  = r == r' && c == c' && x == x'
  _                == _                  = False

-- | Item is a reference together with its Act type. The type is
-- parametrized on a timing `t`, a type `a`, and the reference kind
-- `k`. `t` can be either `Timed` or `Untimed` and indicates whether
-- any indices that reference items in storage explicitly refer to the
-- pre-/post-state, or not. `a` is the type of the item that is
-- referenced. Items are also annotated with the original ValueType
-- that carries more precise type information (e.g., the exact
-- contract type).
data TItem (a :: ActType) (k :: RefKind) (t :: Timing) where
  Item :: SType a -> ValueType -> Ref k t -> TItem a k t
deriving instance Show (TItem a k t)
deriving instance Eq (TItem a k t)

_Item :: SingI a => ValueType -> Ref k t -> TItem a k t
_Item = Item sing

-- | Expressions for which the return type is known.
data TypedExp t
  = forall a. TExp (SType a) (Exp a t)
deriving instance Show (TypedExp t)

instance Eq (TypedExp t) where
  TExp SType e1 == TExp SType e2 = eqS e1 e2

_TExp :: SingI a => Exp a t -> TypedExp t
_TExp expr = TExp sing expr

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp a t` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.
data Exp (a :: ActType) (t :: Timing) where
  -- booleans
  And  :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Or   :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Impl :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Neg :: Pn -> Exp ABoolean t -> Exp ABoolean t
  LT :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  LEQ :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  GEQ :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  GT :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  LitBool :: Pn -> Bool -> Exp ABoolean t
  -- integers
  Add :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Sub :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Mul :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Div :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Mod :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Exp :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  LitInt :: Pn -> Integer -> Exp AInteger t
  IntEnv :: Pn -> EthEnv -> Exp AInteger t
  -- bounds
  IntMin :: Pn -> Int -> Exp AInteger t
  IntMax :: Pn -> Int -> Exp AInteger t
  UIntMin :: Pn -> Int -> Exp AInteger t
  UIntMax :: Pn -> Int -> Exp AInteger t
  InRange :: Pn -> AbiType -> Exp AInteger t -> Exp ABoolean t
  -- bytestrings
  Cat :: Pn -> Exp AByteStr t -> Exp AByteStr t -> Exp AByteStr t
  Slice :: Pn -> Exp AByteStr t -> Exp AInteger t -> Exp AInteger t -> Exp AByteStr t
  ByStr :: Pn -> String -> Exp AByteStr t
  ByLit :: Pn -> ByteString -> Exp AByteStr t
  ByEnv :: Pn -> EthEnv -> Exp AByteStr t
  -- contracts
  Create   :: Pn -> Id -> [TypedExp t] -> Exp AInteger t
  -- polymorphic
  Eq  :: Pn -> SType a -> Exp a t -> Exp a t -> Exp ABoolean t
  NEq :: Pn -> SType a -> Exp a t -> Exp a t -> Exp ABoolean t
  ITE :: Pn -> Exp ABoolean t -> Exp a t -> Exp a t -> Exp a t
  TEntry :: Pn -> Time t -> SRefKind k -> TItem a k t -> Exp a t
  -- Note: we could use a singleton types to avoid separating Entry and Var 
deriving instance Show (Exp a t)

-- Equality modulo source file position.
instance Eq (Exp a t) where
  And _ a b == And _ c d = a == c && b == d
  Or _ a b == Or _ c d = a == c && b == d
  Impl _ a b == Impl _ c d = a == c && b == d
  Neg _ a == Neg _ b = a == b
  LT _ a b == LT _ c d = a == c && b == d
  LEQ _ a b == LEQ _ c d = a == c && b == d
  GEQ _ a b == GEQ _ c d = a == c && b == d
  GT _ a b == GT _ c d = a == c && b == d
  LitBool _ a == LitBool _ b = a == b

  Add _ a b == Add _ c d = a == c && b == d
  Sub _ a b == Sub _ c d = a == c && b == d
  Mul _ a b == Mul _ c d = a == c && b == d
  Div _ a b == Div _ c d = a == c && b == d
  Mod _ a b == Mod _ c d = a == c && b == d
  Exp _ a b == Exp _ c d = a == c && b == d
  LitInt _ a == LitInt _ b = a == b
  IntEnv _ a == IntEnv _ b = a == b

  IntMin _ a == IntMin _ b = a == b
  IntMax _ a == IntMax _ b = a == b
  UIntMin _ a == UIntMin _ b = a == b
  UIntMax _ a == UIntMax _ b = a == b
  InRange _ a b == InRange _ c d  = a == c && b == d

  Cat _ a b == Cat _ c d = a == c && b == d
  Slice _ a b c == Slice _ d e f = a == d && b == e && c == f
  ByStr _ a == ByStr _ b = a == b
  ByLit _ a == ByLit _ b = a == b
  ByEnv _ a == ByEnv _ b = a == b

  Eq _ SType a b == Eq _ SType c d = eqS a c && eqS b d
  NEq _ SType a b == NEq _ SType c d = eqS a c && eqS b d

  ITE _ a b c == ITE _ d e f = a == d && b == e && c == f
  TEntry _ a SRefKind t == TEntry _ b SRefKind u = a == b && eqKind t u
  Create _ a b == Create _ c d = a == c && b == d

  _ == _ = False


instance Semigroup (Exp ABoolean t) where
  a <> b = And nowhere a b

instance Monoid (Exp ABoolean t) where
  mempty = LitBool nowhere True

instance Timable StorageLocation where
  setTime time (Loc t item) = Loc t $ setTime time item

instance Timable TypedExp where
  setTime time (TExp t expr) = TExp t $ setTime time expr

instance Timable (Exp a) where
  setTime time expr = case expr of
    -- booleans
    And p x y -> And p (go x) (go y)
    Or   p x y -> Or p (go x) (go y)
    Impl p x y -> Impl p (go x) (go y)
    Neg p x -> Neg p(go x)
    LT p x y -> LT p (go x) (go y)
    LEQ p x y -> LEQ p (go x) (go y)
    GEQ p x y -> GEQ p (go x) (go y)
    GT p x y -> GT p (go x) (go y)
    LitBool p x -> LitBool p x
    -- integers
    Add p x y -> Add p (go x) (go y)
    Sub p x y -> Sub p (go x) (go y)
    Mul p x y -> Mul p (go x) (go y)
    Div p x y -> Div p (go x) (go y)
    Mod p x y -> Mod p (go x) (go y)
    Exp p x y -> Exp p (go x) (go y)
    LitInt p x -> LitInt p x
    IntEnv p x -> IntEnv p x
    -- bounds
    IntMin p x -> IntMin p x
    IntMax p x -> IntMax p x
    UIntMin p x -> UIntMin p x
    UIntMax p x -> UIntMax p x
    InRange p b e -> InRange p b (go e)

    -- bytestrings
    Cat p x y -> Cat p (go x) (go y)
    Slice p x y z -> Slice p (go x) (go y) (go z)
    ByStr p x -> ByStr p x
    ByLit p x -> ByLit p x
    ByEnv p x -> ByEnv p x
    -- contracts
    Create p x y -> Create p x (go <$> y)

    -- polymorphic
    Eq  p s x y -> Eq p s (go x) (go y)
    NEq p s x y -> NEq p s (go x) (go y)
    ITE p x y z -> ITE p (go x) (go y) (go z)
    TEntry p _ k item -> TEntry p time k (go item)
    where
      go :: Timable c => c Untimed -> c Timed
      go = setTime time


instance Timable (TItem a k) where
   setTime time (Item t vt ref) = Item t vt $ setTime time ref

instance Timable (Ref k) where
  setTime time (SMapping p e ixs) = SMapping p (setTime time e) (setTime time <$> ixs)
  setTime time (SField p e c x) = SField p (setTime time e) c x
  setTime _ (SVar p c x) = SVar p c x
  setTime _ (CVar p c x) = CVar p c x


------------------------
-- * JSON instances * --
------------------------

-- TODO dual instances are ugly! But at least it works for now.
-- It was difficult to construct a function with type:
-- `InvPredicate t -> Either (Exp Bool Timed,Exp Bool Timed) (Exp Bool Untimed)`
instance ToJSON (Act Timed) where
  toJSON (Act storages contracts) = object [ "kind" .= String "Act"
                                           , "store" .= storeJSON storages
                                           , "contracts" .= toJSON contracts ]

instance ToJSON (Act Untimed) where
  toJSON (Act storages contracts) = object [ "kind" .= String "Act"
                                           , "store" .= storeJSON storages
                                           , "contracts" .= toJSON contracts ]

instance ToJSON (Contract Timed) where
  toJSON (Contract ctor behv) = object [ "kind" .= String "Contract"
                                       , "constructor" .= toJSON ctor
                                       , "behaviours" .= toJSON behv ]

instance ToJSON (Contract Untimed) where
  toJSON (Contract ctor behv) = object [ "kind" .= String "Contract"
                                       , "constructor" .= toJSON ctor
                                       , "behaviours" .= toJSON behv ]


storeJSON :: Store -> Value
storeJSON storages = object [ "kind" .= String "Storages"
                            , "storages" .= toJSON storages]

instance ToJSON (Constructor Timed) where
  toJSON Constructor{..} = object [ "kind" .= String "Constructor"
                                  , "contract" .= _cname
                                  , "interface" .= toJSON _cinterface
                                  , "pointers" .= toJSON _cpointers
                                  , "preConditions" .= toJSON _cpreconditions
                                  , "postConditions" .= toJSON _cpostconditions
                                  , "invariants" .= listValue (\i@Invariant{..} -> invariantJSON i _predicate) _invariants
                                  , "initialStorage" .= toJSON _initialStorage  ]

instance ToJSON (Constructor Untimed) where
  toJSON Constructor{..} = object [ "kind" .= String "Constructor"
                                  , "contract" .= _cname
                                  , "interface" .= toJSON _cinterface
                                  , "pointers" .= toJSON _cpointers
                                  , "preConditions" .= toJSON _cpreconditions
                                  , "postConditions" .= toJSON _cpostconditions
                                  , "invariants" .= listValue (\i@Invariant{..} -> invariantJSON i _predicate) _invariants
                                  , "storage" .= toJSON _initialStorage  ]

instance ToJSON (Behaviour t) where
  toJSON Behaviour{..} = object [ "kind" .= String "Behaviour"
                                , "name" .= _name
                                , "contract" .= _contract
                                , "interface" .= toJSON _interface
                                , "pointers" .= toJSON _pointers
                                , "preConditions" .= toJSON _preconditions
                                , "case" .= toJSON _caseconditions
                                , "postConditions" .= toJSON _postconditions
                                , "stateUpdates" .= toJSON _stateUpdates
                                , "returns" .= toJSON _returns ]

instance ToJSON Interface where
  toJSON (Interface x decls) = object [ "kind" .= String "Interface"
                                      , "id" .=  pack (show x)
                                      , "args" .= toJSON decls
                                      ]

instance ToJSON Decl where
  toJSON (Decl abitype x) = object [ "kind" .= String "Declaration"
                                   , "id" .= pack (show x)
                                   , "abitype" .= toJSON abitype
                                   ]

instance ToJSON Pointer where
  toJSON (PointsTo _ x c) = object [ "kind" .= String "PointsTo"
                                   , "var" .= x
                                   , "contract" .= c ]

invariantJSON :: ToJSON pred => Invariant t -> pred -> Value
invariantJSON Invariant{..} predicate = object [ "kind" .= String "Invariant"
                                               , "predicate" .= toJSON predicate
                                               , "preconditions" .= toJSON _ipreconditions
                                               , "storagebounds" .= toJSON _istoragebounds
                                               , "contract" .= _icontract ]

instance ToJSON (StorageLocation t) where
  toJSON (Loc _ a) = object [ "location" .= toJSON a ]

instance ToJSON (StorageUpdate t) where
  toJSON (Update _ a b) = object [ "location" .= toJSON a ,"value" .= toJSON b ]

instance ToJSON (TItem a k t) where
  toJSON (Item t _ a) = object [ "item" .= toJSON a
                               , "type" .=  show t
                               ]

instance ToJSON (Ref k t) where
  toJSON (SVar _ c x) = object [ "kind" .= pack "SVar"
                               , "svar" .=  pack x
                               , "contract" .= pack c ]
  toJSON (CVar _ at x) = object [ "kind" .= pack "Var"
                                  , "var" .=  pack x
                                  , "abitype" .=  toJSON at ]                                  
  toJSON (SMapping _ e xs) = mapping e xs
  toJSON (SField _ e c x) = field e c x


mapping :: (ToJSON a1, ToJSON a2) => a1 -> a2 -> Value
mapping a b = object [ "kind"      .= pack "Mapping"
                     , "indexes"   .= toJSON b
                     , "reference" .= toJSON a]

field :: (ToJSON a1) => a1 -> Id -> Id -> Value
field a c x = object [ "kind"      .= pack "Field"
                     , "field"     .= pack x
                     , "contract"  .= pack c
                     , "reference" .= toJSON a
                     ]


instance ToJSON (TypedExp t) where
  toJSON (TExp typ a) = object [ "kind"       .= pack "TypedExpr"
                               , "type"       .= pack (show typ)
                               , "expression" .= toJSON a ]

instance ToJSON (Exp a t) where
  toJSON (Add _ a b) = symbol "+" a b
  toJSON (Sub _ a b) = symbol "-" a b
  toJSON (Exp _ a b) = symbol "^" a b
  toJSON (Mul _ a b) = symbol "*" a b
  toJSON (Div _ a b) = symbol "/" a b
  toJSON (LitInt _ a) = object [ "literal" .= pack (show a)
                               , "type" .= pack "int" ]
  toJSON (IntMin _ a) = object [ "literal" .= pack (show $ intmin a)
                               , "type" .= pack "int" ]
  toJSON (IntMax _ a) = object [ "literal" .= pack (show $ intmax a)
                               , "type" .= pack "int" ]
  toJSON (UIntMin _ a) = object [ "literal" .= pack (show $ uintmin a)
                                , "type" .= pack "int" ]
  toJSON (UIntMax _ a) = object [ "literal" .= pack (show $ uintmax a)
                                , "type" .= pack "int" ]
  toJSON (InRange _ a b) = object [ "symbol"   .= pack "inrange"
                                  , "arity"    .= Data.Aeson.Types.Number 2
                                  , "args"     .= Array (fromList [toJSON a, toJSON b]) ]
  toJSON (IntEnv _ a) = object [ "ethEnv" .= pack (show a)
                               , "type" .= pack "int" ]
  toJSON (ITE _ a b c) = object [ "symbol"   .= pack "ite"
                                , "arity"    .= Data.Aeson.Types.Number 3
                                , "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c]) ]
  toJSON (And _ a b)  = symbol "and" a b
  toJSON (Or _ a b)   = symbol "or" a b
  toJSON (LT _ a b)   = symbol "<" a b
  toJSON (GT _ a b)   = symbol ">" a b
  toJSON (Impl _ a b) = symbol "=>" a b
  toJSON (NEq _ _ a b)  = symbol "=/=" a b
  toJSON (Eq _ _ a b)   = symbol "==" a b
  toJSON (LEQ _ a b)  = symbol "<=" a b
  toJSON (GEQ _ a b)  = symbol ">=" a b
  toJSON (LitBool _ a) = object [ "literal" .= pack (show a)
                                , "type" .= pack "bool" ]
  toJSON (Neg _ a) = object [ "symbol"   .= pack "not"
                            , "arity"    .= Data.Aeson.Types.Number 1
                            , "args"     .= Array (fromList [toJSON a]) ]

  toJSON (Cat _ a b) = symbol "cat" a b
  toJSON (Slice _ s a b) = object [ "symbol" .= pack "slice"
                                  , "arity"  .= Data.Aeson.Types.Number 3
                                  , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b]) ]
  toJSON (ByStr _ a) = object [ "bytestring" .= toJSON a
                              , "type" .= pack "bool" ]
  toJSON (ByLit _ a) = object [ "literal" .= pack (show a)
                              , "type" .= pack "bytestring" ]
  toJSON (ByEnv _ a) = object [ "ethEnv" .= pack (show a)
                              , "type" .= pack "bytestring" ]
  toJSON (TEntry _ t _ a) = object [ "entry"  .= toJSON a
                                   , "timing" .= show t ]
  toJSON (Create _ f xs) = object [ "symbol" .= pack "create"
                                  , "arity"  .= Data.Aeson.Types.Number 2
                                  , "args"   .= Array (fromList [object [ "fun" .=  String (pack f) ], toJSON xs]) ]

  toJSON v = error $ "todo: json ast for: " <> show v



symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [ "symbol"   .= pack s
                      , "arity"    .= Data.Aeson.Types.Number 2
                      , "args"     .= Array (fromList [toJSON a, toJSON b]) ]

-- | Simplifies concrete expressions into literals.
-- Returns `Nothing` if the expression contains symbols.
eval :: Exp a t -> Maybe (TypeOf a)
eval e = case e of
  And  _ a b    -> [a' && b' | a' <- eval a, b' <- eval b]
  Or   _ a b    -> [a' || b' | a' <- eval a, b' <- eval b]
  Impl _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  Neg  _ a      -> not <$> eval a
  LT   _ a b    -> [a' <  b' | a' <- eval a, b' <- eval b]
  LEQ  _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  GT   _ a b    -> [a' >  b' | a' <- eval a, b' <- eval b]
  GEQ  _ a b    -> [a' >= b' | a' <- eval a, b' <- eval b]
  LitBool _ a   -> pure a

  Add _ a b     -> [a' + b'     | a' <- eval a, b' <- eval b]
  Sub _ a b     -> [a' - b'     | a' <- eval a, b' <- eval b]
  Mul _ a b     -> [a' * b'     | a' <- eval a, b' <- eval b]
  Div _ a b     -> [a' `div` b' | a' <- eval a, b' <- eval b]
  Mod _ a b     -> [a' `mod` b' | a' <- eval a, b' <- eval b]
  Exp _ a b     -> [a' ^ b'     | a' <- eval a, b' <- eval b]
  LitInt  _ a   -> pure a
  IntMin  _ a   -> pure $ intmin  a
  IntMax  _ a   -> pure $ intmax  a
  UIntMin _ a   -> pure $ uintmin a
  UIntMax _ a   -> pure $ uintmax a
  InRange _ _ _ -> error "TODO eval in range"

  Cat _ s t     -> [s' <> t' | s' <- eval s, t' <- eval t]
  Slice _ s a b -> [BS.pack . genericDrop a' . genericTake b' $ s'
                            | s' <- BS.unpack <$> eval s
                            , a' <- eval a
                            , b' <- eval b]
  ByStr _ s     -> pure . fromString $ s
  ByLit _ s     -> pure s

  -- TODO better way to write these?
  Eq _ SInteger x y -> [ x' == y' | x' <- eval x, y' <- eval y]
  Eq _ SBoolean x y -> [ x' == y' | x' <- eval x, y' <- eval y]
  Eq _ SByteStr x y -> [ x' == y' | x' <- eval x, y' <- eval y]

  NEq _ SInteger x y -> [ x' /= y' | x' <- eval x, y' <- eval y]
  NEq _ SBoolean x y -> [ x' /= y' | x' <- eval x, y' <- eval y]
  NEq _ SByteStr x y -> [ x' /= y' | x' <- eval x, y' <- eval y]

  ITE _ a b c   -> eval a >>= \cond -> if cond then eval b else eval c

  Create _ _ _ -> error "eval of contracts not supported"
  _              -> empty

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1

_Var :: SingI a => Time t -> AbiType -> Id -> Exp a t
_Var tm at x = TEntry nowhere tm SCalldata (Item sing (PrimitiveType at) (CVar nowhere at x))
