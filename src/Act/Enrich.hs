{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Act.Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)

import Act.Syntax
import Act.Syntax.Annotated
import Act.Type (defaultStore)

-- | Adds extra preconditions to non constructor behaviours based on the types of their variables
enrich :: Act -> Act
enrich (Act store contracts) = Act store (enrichContract <$> contracts)
  where
    enrichContract (Contract ctors behvs) = Contract (enrichConstructor ctors) (enrichBehaviour <$> behvs)

-- |Adds type bounds for calldata , environment vars, and external storage vars as preconditions
enrichConstructor :: Constructor -> Constructor
enrichConstructor ctor@(Constructor _ (Interface _ decls) _ pre _ invs _) =
  ctor { _cpreconditions = pre'
       , _invariants = invs' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
      invs' = enrichInvariant ctor <$> invs

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
enrichBehaviour :: Behaviour -> Behaviour
enrichBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases _ stateUpdates _) =
  behv { _preconditions = pre' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds stateUpdates
             <> mkStorageBoundsLoc (concatMap locsFromExp (pre <> cases))
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

-- | Adds type bounds for calldata, environment vars, and storage vars
enrichInvariant :: Constructor -> Invariant -> Invariant
enrichInvariant (Constructor _ (Interface _ decls) _ _ _ _ _) inv@(Invariant _ preconds storagebounds (predicate,_)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBoundsLoc (locsFromExp predicate)

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = case lookup e defaultStore of
      Just AInteger -> Just $ bound (toAbiType e) (IntEnv nowhere e)
      _ -> Nothing

    toAbiType :: EthEnv -> AbiType
    toAbiType env = case env of
      Caller -> AbiAddressType
      Callvalue -> AbiUIntType 256
      Calldepth -> AbiUIntType 10
      Origin -> AbiAddressType
      Blockhash -> AbiBytesType 32
      Blocknumber -> AbiUIntType 256
      Difficulty -> AbiUIntType 256
      Chainid -> AbiUIntType 256
      Gaslimit -> AbiUIntType 256
      Coinbase -> AbiAddressType
      Timestamp -> AbiUIntType 256
      This -> AbiAddressType
      Nonce -> AbiUIntType 256

-- | extracts bounds from the AbiTypes of Integer values in storage
mkStorageBounds :: [StorageUpdate] -> [Exp ABoolean]
mkStorageBounds refs = concatMap mkBound refs
  where
    mkBound :: StorageUpdate -> [Exp ABoolean]
    mkBound (Update SInteger item _) = [fromItem item]
    mkBound _ = []

-- TODO why only Pre items here?
fromItem :: TItem AInteger Storage -> Exp ABoolean
fromItem item@(Item _ (PrimitiveType vt) _) = bound vt (TEntry nowhere Pre SStorage item)
fromItem (Item _ (ContractType _) _) = LitBool nowhere True

mkStorageBoundsLoc :: [StorageLocation] -> [Exp ABoolean]
mkStorageBoundsLoc refs = concatMap mkBound refs
  where
    mkBound :: StorageLocation -> [Exp ABoolean]
    mkBound (Loc SInteger item) = [fromItem item]
    mkBound _ = []

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case fromAbiType typ of
  AInteger -> [bound typ (_Var Pre typ name)]
  _ -> []
