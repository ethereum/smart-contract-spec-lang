{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Error
Description : An instantiation of 'Validation' with our error type.

This specializes 'Data.Validation.Validation' to keep its errors in a 'NonEmpty' list
and keep track of a 'Pn' for every error it logs. There is also some infrastructure
around modified chaining/branching behaviours.
-}

module Act.Error (module Act.Error) where

import Data.List (find)
import Data.List.NonEmpty as NE
import Data.Validation as Act.Error

import Act.Syntax.Untyped (Pn)

-- Reexport NonEmpty so that we can use `-XOverloadedLists` without thinking.
import Data.List.NonEmpty as Act.Error (NonEmpty)

type Error e = Validation (NonEmpty (Pn,e))

throw :: (Pn,e) -> Error e a
throw msg = Failure [msg]

assert :: (Pn, e) -> Bool -> Error e ()
assert err b = if b then pure () else throw err

foldValidation :: (b -> a -> Error err b) -> b -> [a] -> Error err b
foldValidation _ b [] = pure b
foldValidation f b (a:as) = f b a `bindValidation` \b' -> foldValidation f b' as

infixr 1 <==<, >==>

-- Like 'Control.Monad.(>=>)' but allows us to chain error-prone
-- computations even without a @Monad@ instance.
(>==>) :: (a -> Error e b) -> (b -> Error e c) -> a -> Error e c
f >==> g = \x -> f x `bindValidation` g

(<==<) :: (b -> Error e c) -> (a -> Error e b) -> a -> Error e c
(<==<) = flip (>==>)

-- | Runs through a list of error-prone computations and returns the first
-- successful one, with the definition of "success" expanded to include
-- failures which did not generate any error at the supplied position.
notAtPosn :: Pn -> [Error e a] -> Maybe (Error e a)
notAtPosn p = find valid
  where
    valid (Success _)    = True
    valid (Failure errs) = all ((p /=) . fst) errs

-- | Try to find a succesfull computation in a list, and if it fails
-- it returns a default computation
findSuccess :: Error e a -> [Error e a] -> Error e a
findSuccess d comp = case find valid comp of
                       Just a -> a
                       Nothing -> foldl (*>) d comp
  where
    valid (Success _) = True
    valid _ = False


concatError ::  Error e a -> [Error e a] -> Error e a
concatError def = \case
  [] -> def
  x:xs -> foldl (*>) x xs
