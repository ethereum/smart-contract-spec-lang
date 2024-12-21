{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}

module Act.Consistency (
  checkCases
) where


import Prelude hiding (GT, LT)

import Data.List
import Prettyprinter
import System.Exit (exitFailure)
import Data.Maybe

import Act.Syntax
import Act.Syntax.Annotated
import Act.SMT as SMT
import Act.Syntax.Untyped (makeIface)
import Act.Print

import qualified EVM.Solvers as Solvers

-- TODO this is duplicated in hevm Keccak.hs but not exported
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Checks non-overlapping cases,
-- For every pair of case conditions we assert that they are true
-- simultaneously. The query must be unsat.
mkNonoverlapAssertion :: [Exp ABoolean] -> Exp ABoolean
mkNonoverlapAssertion caseconds =
  mkOr $ (\(x, y) -> And nowhere x y) <$> combine caseconds
  where
    mkOr [] = LitBool nowhere False
    mkOr (c:cs) = Or nowhere c (mkOr cs)

-- | Checks exhaustiveness of cases.
-- We assert that none of the case conditions are true at the same
-- time. The query must be unsat.
mkExhaustiveAssertion :: [Exp ABoolean] -> Exp ABoolean
mkExhaustiveAssertion caseconds =
  foldl mkAnd (LitBool nowhere True) caseconds
  where
    mkAnd r c = And nowhere (Neg nowhere c) r

-- | Create a query for cases
mkCaseQuery :: ([Exp ABoolean] -> Exp ABoolean) -> [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkCaseQuery props behvs@((Behaviour _ _ (Interface ifaceName decls) _ preconds _ _ _ _):_) =
  (ifaceName, mkSMT, getModel)
  where
    locs = nub $ concatMap locsFromExp (preconds <> caseconds)
    env = concatMap ethEnvFromBehaviour behvs
    pres = mkAssert ifaceName <$> preconds
    caseconds = concatMap _caseconditions behvs

    mkSMT = SMTExp
      { _storage = concatMap (declareStorage [Pre]) locs
      , _calldata = declareArg ifaceName <$> decls
      , _environment = declareEthEnv <$> env
      , _assertions = (mkAssert ifaceName $ props caseconds) : pres
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) locs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }
mkCaseQuery _ [] = error "Internal error: behaviours cannot be empty"

-- | Checks nonoverlapping and exhaustiveness of cases
checkCases :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkCases (Act _ contracts) solver' smttimeout debug = do
  let groups = concatMap (\(Contract _ behvs) -> groupBy sameIface behvs) contracts
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
  solver <- spawnSolver config
  let qs = mkCaseQuery mkNonoverlapAssertion <$> groups
  r <- flip mapM qs (\(name, q, getModel) -> do
                        res <- checkSat solver getModel q
                        pure (name, res))
  mapM_ (checkRes "nonoverlapping") r
  let qs' = mkCaseQuery mkExhaustiveAssertion <$> groups
  r' <- flip mapM qs' (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res))
  mapM_ (checkRes "exhaustive") r'

    where

      sameIface (Behaviour _ _ iface _ _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _ _) =
        makeIface iface == makeIface iface'

      checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
      checkRes check (name, res) =
        case res of
          Sat model -> failMsg ("Cases are not " <> check <> " for behavior " <> name <> ".") (prettyAnsi model)
          Unsat -> pure ()
          Unknown -> errorMsg $ "Solver timeour. Cannot prove that cases are " <> check <> " for behavior " <> name <> "."
          SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that cases are " <>  check <> " for behavior " <> name <> "."

      failMsg str model = render (red (pretty str) <> line <> model <> line) >> exitFailure
      errorMsg str = render (pretty str <> line) >> exitFailure
