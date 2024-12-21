{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Act.Syntax where

import Prelude hiding (LT, GT)

import Data.List hiding (singleton)
import Data.Map (Map,empty,insertWith,unionsWith,unionWith,singleton)

import Act.Syntax.TimeAgnostic as Agnostic
import qualified Act.Syntax.Annotated as Annotated
import qualified Act.Syntax.Typed as Typed
import           Act.Syntax.Untyped hiding (Contract)
import qualified Act.Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------

-- | Invariant predicates can always be expressed as a single expression.
invExp :: Annotated.InvariantPred -> Annotated.Exp ABoolean
invExp = uncurry (<>)

locsFromBehaviour :: Annotated.Behaviour -> [Annotated.StorageLocation]
locsFromBehaviour (Behaviour _ _ _ _ preconds cases postconds rewrites returns) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp cases
  <> concatMap locsFromExp postconds
  <> concatMap locsFromUpdate rewrites
  <> maybe [] locsFromTypedExp returns

locsFromConstructor :: Annotated.Constructor -> [Annotated.StorageLocation]
locsFromConstructor (Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromInvariant inv
  <> concatMap locsFromUpdate initialStorage

locsFromInvariant :: Annotated.Invariant -> [Annotated.StorageLocation]
locsFromInvariant (Invariant _ pre bounds (predpre, predpost)) =
  concatMap locsFromExp pre <>  concatMap locsFromExp bounds <>
  locsFromExp predpre <> locsFromExp predpost

------------------------------------
-- * Extract from any typed AST * --
------------------------------------

nameOfContract :: Contract t -> Id
nameOfContract (Contract (Constructor cname _ _ _ _ _ _) _) = cname

behvsFromAct :: Agnostic.Act t -> [Behaviour t]
behvsFromAct (Act _ contracts) = behvsFromContracts contracts

behvsFromContracts :: [Contract t] -> [Behaviour t]
behvsFromContracts contracts = concatMap (\(Contract _ b) -> b) contracts

constrFromContracts :: [Contract t] -> [Constructor t]
constrFromContracts contracts = fmap (\(Contract c _) -> c) contracts

locsFromUpdate :: StorageUpdate t -> [StorageLocation t]
locsFromUpdate update = nub $ case update of
  (Update _ item e) -> locsFromItem SStorage item <> locsFromExp e

locFromUpdate :: StorageUpdate t -> StorageLocation t
locFromUpdate (Update _ item _) = _Loc item

locsFromItem :: SRefKind k -> TItem a k t -> [StorageLocation t]
locsFromItem SCalldata item = concatMap locsFromTypedExp (ixsFromItem item)
locsFromItem SStorage item = _Loc item : concatMap locsFromTypedExp (ixsFromItem item)

locsFromTypedExp :: TypedExp t -> [StorageLocation t]
locsFromTypedExp (TExp _ e) = locsFromExp e

locsFromExp :: Exp a t -> [StorageLocation t]
locsFromExp = nub . go
  where
    go :: Exp a t -> [StorageLocation t]
    go e = case e of
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      Cat _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      IntMin {}  -> []
      IntMax {}  -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      LitBool {} -> []
      IntEnv {} -> []
      ByEnv {} -> []
      Create _ _ es -> concatMap locsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      TEntry _ _ k a -> locsFromItem k a

createsFromExp :: Exp a t -> [Id]
createsFromExp = nub . go
  where
    go :: Exp a t -> [Id]
    go e = case e of
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      Cat _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      IntMin {}  -> []
      IntMax {}  -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      LitBool {} -> []
      IntEnv {} -> []
      ByEnv {} -> []
      Create _ f es -> [f] <> concatMap createsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      TEntry _ _ _ a -> createsFromItem a

createsFromItem :: TItem k a t -> [Id]
createsFromItem item = concatMap createsFromTypedExp (ixsFromItem item)

createsFromTypedExp :: TypedExp t -> [Id]
createsFromTypedExp (TExp _ e) = createsFromExp e

createsFromContract :: Typed.Contract -> [Id]
createsFromContract (Contract constr behvs) =
  createsFromConstructor constr <> concatMap createsFromBehaviour behvs

createsFromConstructor :: Typed.Constructor -> [Id]
createsFromConstructor (Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap createsFromExp pre
  <> concatMap createsFromExp post
  <> concatMap createsFromInvariant inv
  <> concatMap createsFromUpdate initialStorage

createsFromInvariant :: Typed.Invariant -> [Id]
createsFromInvariant (Invariant _ pre bounds ipred) =
  concatMap createsFromExp pre <>  concatMap createsFromExp bounds <> createsFromExp ipred

createsFromUpdate :: StorageUpdate t ->[Id]
createsFromUpdate update = nub $ case update of
  Update _ item e -> createsFromItem item <> createsFromExp e

createsFromBehaviour :: Behaviour t -> [Id]
createsFromBehaviour (Behaviour _ _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap createsFromExp preconds
  <> concatMap createsFromExp postconds
  <> concatMap createsFromUpdate rewrites
  <> maybe [] createsFromTypedExp returns


pointersFromContract :: Typed.Contract -> [Id]
pointersFromContract (Contract constr behvs) =
  nub $ pointersFromConstructor constr <> concatMap pointersFromBehaviour behvs

pointersFromConstructor :: Typed.Constructor -> [Id]
pointersFromConstructor (Constructor _ _ ptrs _ _ _ _) =
  map (\(PointsTo _ _ c) -> c) ptrs

pointersFromBehaviour :: Behaviour t -> [Id]
pointersFromBehaviour (Behaviour _ _ _ ptrs _ _ _ _ _) =
  map (\(PointsTo _ _ c) -> c) ptrs

ethEnvFromBehaviour :: Behaviour t -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds cases postconds rewrites returns) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromExp cases
  <> concatMap ethEnvFromExp postconds
  <> concatMap ethEnvFromUpdate rewrites
  <> maybe [] ethEnvFromTypedExp returns

ethEnvFromConstructor :: Annotated.Constructor -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromInvariant inv
  <> concatMap ethEnvFromUpdate initialStorage

ethEnvFromInvariant :: Annotated.Invariant -> [EthEnv]
ethEnvFromInvariant (Invariant _ pre bounds (predpre, predpost)) =
  concatMap ethEnvFromExp pre <>  concatMap ethEnvFromExp bounds <>
  ethEnvFromExp predpre <> ethEnvFromExp predpost

ethEnvFromUpdate :: StorageUpdate t -> [EthEnv]
ethEnvFromUpdate rewrite = case rewrite of
  Update _ item e -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TItem k a t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (TExp _ e) = ethEnvFromExp e

ethEnvFromExp :: Exp a t -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a t -> [EthEnv]
    go e = case e of
      And   _ a b   -> go a <> go b
      Or    _ a b   -> go a <> go b
      Impl  _ a b   -> go a <> go b
      Eq    _ _ a b   -> go a <> go b
      LT    _ a b   -> go a <> go b
      LEQ   _ a b   -> go a <> go b
      GT    _ a b   -> go a <> go b
      GEQ   _ a b   -> go a <> go b
      NEq   _ _ a b   -> go a <> go b
      Neg   _ a     -> go a
      Add   _ a b   -> go a <> go b
      Sub   _ a b   -> go a <> go b
      Mul   _ a b   -> go a <> go b
      Div   _ a b   -> go a <> go b
      Mod   _ a b   -> go a <> go b
      Exp   _ a b   -> go a <> go b
      Cat   _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ITE   _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      LitBool {} -> []
      IntMin {} -> []
      IntMax {} -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      IntEnv _ a -> [a]
      ByEnv _ a -> [a]
      Create _ _ ixs -> concatMap ethEnvFromTypedExp ixs
      TEntry _ _ _ a -> ethEnvFromItem a

idFromItem :: TItem k a t -> Id
idFromItem (Item _ _ ref) = idFromRef ref

idFromRef :: Ref k t -> Id
idFromRef (SVar _ _ x) = x
idFromRef (CVar _ _ x) = x
idFromRef (SMapping _ e _) = idFromRef e
idFromRef (SField _ e _ _) = idFromRef e

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (Update _ item _) = idFromItem item

idFromLocation :: StorageLocation t -> Id
idFromLocation (Loc _ item) = idFromItem item

ixsFromItem :: TItem k a t -> [TypedExp t]
ixsFromItem (Item _ _ item) = ixsFromRef item

ixsFromRef :: Ref k t -> [TypedExp t]
ixsFromRef (SVar _ _ _) = []
ixsFromRef (CVar _ _ _) = []
ixsFromRef (SMapping _ ref ixs) = ixs ++ ixsFromRef ref
ixsFromRef (SField _ ref _ _) = ixsFromRef ref

ixsFromLocation :: StorageLocation t -> [TypedExp t]
ixsFromLocation (Loc _ item) = ixsFromItem item

ixsFromUpdate :: StorageUpdate t -> [TypedExp t]
ixsFromUpdate (Update _ item _) = ixsFromItem item

itemType :: TItem k a t -> ActType
itemType (Item t _ _) = actType t

isMapping :: StorageLocation t -> Bool
isMapping = not . null . ixsFromLocation

posnFromExp :: Exp a t -> Pn
posnFromExp e = case e of
  And p _ _ -> p
  Or p _ _ -> p
  Impl p _ _ -> p
  Neg p _ -> p
  LT p _ _ -> p
  LEQ p _ _ -> p
  GEQ p _ _ -> p
  GT p _ _ -> p
  LitBool p _ -> p
  -- integers
  Add p _ _ -> p
  Sub p _ _ -> p
  Mul p _ _ -> p
  Div p _ _ -> p
  Mod p _ _ -> p
  Exp p _ _ -> p
  LitInt p _ -> p
  IntEnv p _ -> p
  -- bounds
  IntMin p _ -> p
  IntMax p _ -> p
  UIntMin p _ -> p
  UIntMax p _ -> p
  InRange p _ _ -> p

  -- bytestrings
  Cat p _ _ -> p
  Slice p _ _ _ -> p
  ByStr p _ -> p
  ByLit p _ -> p
  ByEnv p _ -> p
  -- contracts
  Create p _ _ -> p

  -- polymorphic
  Eq  p _ _ _ -> p
  NEq p _ _ _ -> p
  ITE p _ _ _ -> p
  TEntry p _ _ _ -> p
--------------------------------------
-- * Extraction from untyped ASTs * --
--------------------------------------

nameFromStorage :: Untyped.Storage -> Id
nameFromStorage (Untyped.Rewrite e _) = nameFromEntry e

nameFromEntry :: Entry -> Id
nameFromEntry (EVar _ x) = x
nameFromEntry (EMapping _ e _) = nameFromEntry e
nameFromEntry (EField _ e _) = nameFromEntry e

nameFromBehv :: Annotated.Behaviour -> Id
nameFromBehv (Behaviour _ _ (Interface ifaceName _) _ _ _ _ _ _) = ifaceName

getPosEntry :: Entry -> Pn
getPosEntry (EVar pn _) = pn
getPosEntry (EMapping pn _ _) = pn
getPosEntry (EField pn _ _) = pn

getPosn :: Expr -> Pn
getPosn expr = case expr of
    EAnd pn  _ _ -> pn
    EOr pn _ _ -> pn
    ENot pn _ -> pn
    EImpl pn _ _ -> pn
    EEq pn _ _ -> pn
    ENeq pn _ _ -> pn
    ELEQ pn _ _ -> pn
    ELT pn _ _ -> pn
    EGEQ pn _ _ -> pn
    EGT pn _ _ -> pn
    EAdd pn _ _ -> pn
    ESub pn _ _ -> pn
    EITE pn _ _ _ -> pn
    EMul pn _ _ -> pn
    EDiv pn _ _ -> pn
    EMod pn _ _ -> pn
    EExp pn _ _ -> pn
    ECreate pn _ _ -> pn
    EUTEntry e -> getPosEntry e
    EPreEntry e -> getPosEntry e
    EPostEntry e -> getPosEntry e
    ListConst e -> getPosn e
    ECat pn _ _ -> pn
    ESlice pn _ _ _ -> pn
    ENewaddr pn _ _ -> pn
    ENewaddr2 pn _ _ _ -> pn
    BYHash pn _ -> pn
    BYAbiE pn _ -> pn
    StringLit pn _ -> pn
    WildExp pn -> pn
    EnvExp pn _ -> pn
    IntLit pn _ -> pn
    BoolLit pn _ -> pn
    EInRange pn _ _ -> pn

posFromDef :: Defn -> Pn
posFromDef (Defn e _) = getPosn e

-- | Returns all the identifiers used in an expression,
-- as well all of the positions they're used in.
idFromRewrites :: Expr -> Map Id [Pn]
idFromRewrites e = case e of
  EAnd _ a b        -> idFromRewrites' [a,b]
  EOr _ a b         -> idFromRewrites' [a,b]
  ENot _ a          -> idFromRewrites a
  EImpl _ a b       -> idFromRewrites' [a,b]
  EEq _ a b         -> idFromRewrites' [a,b]
  ENeq _ a b        -> idFromRewrites' [a,b]
  ELEQ _ a b        -> idFromRewrites' [a,b]
  ELT _ a b         -> idFromRewrites' [a,b]
  EGEQ _ a b        -> idFromRewrites' [a,b]
  EGT _ a b         -> idFromRewrites' [a,b]
  EAdd _ a b        -> idFromRewrites' [a,b]
  ESub _ a b        -> idFromRewrites' [a,b]
  EITE _ a b c      -> idFromRewrites' [a,b,c]
  EMul _ a b        -> idFromRewrites' [a,b]
  EDiv _ a b        -> idFromRewrites' [a,b]
  EMod _ a b        -> idFromRewrites' [a,b]
  EExp _ a b        -> idFromRewrites' [a,b]
  EUTEntry en       -> idFromEntry en
  EPreEntry en      -> idFromEntry en
  EPostEntry en     -> idFromEntry en
  ECreate p x es    -> insertWith (<>) x [p] $ idFromRewrites' es
  ListConst a       -> idFromRewrites a
  ECat _ a b        -> idFromRewrites' [a,b]
  ESlice _ a b c    -> idFromRewrites' [a,b,c]
  ENewaddr _ a b    -> idFromRewrites' [a,b]
  ENewaddr2 _ a b c -> idFromRewrites' [a,b,c]
  BYHash _ a        -> idFromRewrites a
  BYAbiE _ a        -> idFromRewrites a
  StringLit {}      -> empty
  WildExp {}        -> empty
  EnvExp {}         -> empty
  IntLit {}         -> empty
  BoolLit {}        -> empty
  EInRange _ _ a    -> idFromRewrites a
  where
    idFromRewrites' = unionsWith (<>) . fmap idFromRewrites

    idFromEntry :: Entry -> Map Id [Pn]
    idFromEntry (EVar p x) = singleton x [p]
    idFromEntry (EMapping _ en xs) = unionWith (<>) (idFromEntry en) (idFromRewrites' xs)
    idFromEntry (EField _ en _) = idFromEntry en

-- | True iff the case is a wildcard.
isWild :: Case -> Bool
isWild (Case _ (WildExp _) _) = True
isWild _                      = False

bound :: AbiType -> Exp AInteger t -> Exp ABoolean t
bound typ e = And nowhere (LEQ nowhere (lowerBound typ) e) $ LEQ nowhere e (upperBound typ)

lowerBound :: forall t. AbiType -> Exp AInteger t
lowerBound (AbiIntType a) = IntMin nowhere a
-- todo: other negatives?
lowerBound _ = LitInt nowhere 0

-- todo, the rest
upperBound :: forall t. AbiType -> Exp AInteger t
upperBound (AbiUIntType  n) = UIntMax nowhere n
upperBound (AbiIntType   n) = IntMax nowhere n
upperBound AbiAddressType   = UIntMax nowhere 160
upperBound (AbiBytesType n) = UIntMax nowhere (8 * n)
upperBound typ = error $ "upperBound not implemented for " ++ show typ
