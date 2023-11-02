{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)

import Syntax
import Syntax.Annotated
import Syntax.Timing
import Type (defaultStore)

import Debug.Trace

-- | Adds extra preconditions to non constructor behaviours based on the types of their variables
enrich :: Act -> Act
enrich (Act store contracts) = Act store (enrichContract <$> contracts)
  where
    enrichContract (Contract ctors behvs) = Contract (enrichConstructor ctors) (enrichBehaviour <$> behvs)

-- |Adds type bounds for calldata , environment vars, and external storage vars as preconditions
enrichConstructor :: Constructor -> Constructor
enrichConstructor ctor@(Constructor _ (Interface _ decls) pre _ invs rewrites) =
  trace "Pre" $
  traceShow pre $ 
  trace "Pre'" $
  traceShow pre' $
  trace "Rewrites"
  traceShow rewrites
  ctor { _cpreconditions = pre'
       , _invariants = invs' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds rewrites [Post]
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
      invs' = enrichInvariant ctor <$> invs

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
enrichBehaviour :: Behaviour -> Behaviour
enrichBehaviour behv@(Behaviour _ _ (Interface _ decls) pre cases _ stateUpdates _) =
  behv { _preconditions = pre' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds stateUpdates [Pre, Post]
             <> mkStorageBoundsLoc (concatMap locsFromExp (pre <> cases)) [Pre, Post]
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

-- | Adds type bounds for calldata, environment vars, and storage vars
enrichInvariant :: Constructor -> Invariant -> Invariant
enrichInvariant (Constructor _ (Interface _ decls) _ _ _ _) inv@(Invariant _ preconds storagebounds (predicate,_)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBoundsLoc (locsFromExp predicate) [Pre, Post]

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
mkStorageBounds :: [StorageUpdate] -> [Time Timed] -> [Exp ABoolean]
mkStorageBounds refs times = concatMap mkBound refs
  where
    mkBound :: StorageUpdate -> [Exp ABoolean]
    mkBound (Update SInteger item _) = fromItem item times
    mkBound _ = []

-- TODO why only Pre items here?
fromItem :: TStorageItem AInteger -> [Time Timed] -> [Exp ABoolean]
fromItem item@(Item _ (PrimitiveType vt) _) times = map (\t -> bound vt (TEntry nowhere t item)) times
fromItem (Item _ (ContractType _) _) _ = [LitBool nowhere True]

mkStorageBoundsLoc :: [StorageLocation] -> [Time Timed] -> [Exp ABoolean]
mkStorageBoundsLoc refs times = concatMap mkBound refs
  where
    mkBound :: StorageLocation -> [Exp ABoolean]
    mkBound (Loc SInteger item) = fromItem item times
    mkBound _ = []

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case fromAbiType typ of
  AInteger -> [bound typ (_Var typ name)]
  _ -> []
