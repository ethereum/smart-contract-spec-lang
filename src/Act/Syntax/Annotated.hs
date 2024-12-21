{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Syntax.Annotated
Description : AST data types where all implicit timings have been made explicit.
-}
module Act.Syntax.Annotated (module Act.Syntax.Annotated) where

import qualified Act.Syntax.TimeAgnostic as Agnostic
import Act.Syntax.TimeAgnostic (Timing(..),setPre,setPost)

-- Reexports
import Act.Syntax.TimeAgnostic as Act.Syntax.Annotated hiding (Timing(..),Timable(..),Time,Neither,Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,StorageLocation,TItem,Exp,TypedExp,Ref)
import Act.Syntax.TimeAgnostic as Act.Syntax.Annotated (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour, pattern Exp)


-- We shadow all timing-agnostic AST types with explicitly timed versions.
type Act             = Agnostic.Act             Timed
type Contract        = Agnostic.Contract        Timed
type Invariant       = Agnostic.Invariant       Timed
type InvariantPred   = Agnostic.InvariantPred   Timed
type Constructor     = Agnostic.Constructor     Timed
type Behaviour       = Agnostic.Behaviour       Timed
type StorageUpdate   = Agnostic.StorageUpdate   Timed
type StorageLocation = Agnostic.StorageLocation Timed
type Ref           k = Agnostic.Ref           k Timed
type TItem       k a = Agnostic.TItem       k a Timed
type Exp           a = Agnostic.Exp           a Timed
type TypedExp        = Agnostic.TypedExp        Timed

------------------------------------------
-- * How to make all timings explicit * --
------------------------------------------

instance Annotatable Agnostic.Act where
  annotate (Agnostic.Act store act) = Agnostic.Act store $ fmap annotate act

instance Annotatable Agnostic.Contract where
  annotate (Agnostic.Contract ctor behv) = Agnostic.Contract (annotate ctor) (fmap annotate behv)

instance Annotatable Agnostic.Invariant where
  annotate inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds
    , _predicate      = (setPre _predicate, setPost _predicate)
    }

instance Annotatable Agnostic.Constructor where
  annotate ctor@Constructor{..} = ctor
    { _cpreconditions = setPre <$> _cpreconditions
    , _initialStorage = annotate <$> _initialStorage
    , _invariants  = annotate <$> _invariants
    }

instance Annotatable Agnostic.Behaviour where
  annotate behv@Behaviour{..} = behv
    { _preconditions = setPre <$> _preconditions
    , _caseconditions = setPre <$> _caseconditions
    , _stateUpdates  = annotate <$> _stateUpdates
    }

instance Annotatable Agnostic.StorageUpdate where
  -- The timing in items only refers to the timing of mapping indices of a
  -- storage update. Hence, it should be Pre
  annotate (Update typ item expr) = Update typ (setPre item) (setPre expr)
