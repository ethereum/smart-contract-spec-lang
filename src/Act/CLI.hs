{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Act.CLI (main, compile, proceed, prettyErrs) where

import Data.Aeson hiding (Bool, Number, json, Success)
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr)
import Data.Text (unpack)
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Prettyprinter hiding (annotate, line')
import GHC.Conc
import GHC.Natural
import Options.Generic

import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.ByteString as BS
import Data.ByteString (ByteString)

import Control.Monad
import Control.Lens.Getter

import Act.Error
import Act.Lex (lexer, AlexPosn(..))
import Act.Parse
import Act.Syntax.Annotated
import Act.Enrich
import Act.SMT as SMT
import Act.Type
import Act.Coq hiding (indent)
import Act.HEVM
import Act.HEVM_utils
import Act.Consistency
import Act.Print
import Act.Decompile

import qualified EVM.Solvers as Solvers
import EVM.Solidity
import EVM.Effects

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Prove           { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Coq             { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | HEVM            { spec       :: w ::: String               <?> "Path to spec"
                    , sol        :: w ::: Maybe String         <?> "Path to .sol"
                    , code       :: w ::: Maybe ByteString     <?> "Runtime code"
                    , initcode   :: w ::: Maybe ByteString     <?> "Initial code"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }
  | Decompile       { solFile    :: w ::: String               <?> "Path to .sol"
                    , contract   :: w ::: String               <?> "Contract name"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }
 deriving (Generic)

deriving instance ParseField [(Id, String)]
instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)


-----------------------
-- *** Dispatch *** ---
-----------------------


main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      Lex f -> lex' f
      Parse f -> parse' f
      Type f solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        type' f solver'' smttimeout' debug'
      Prove file' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        prove file' solver'' smttimeout' debug'
      Coq f solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        coq' f solver'' smttimeout' debug'
      HEVM spec' sol' code' initcode' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        hevm spec' sol' code' initcode' solver'' smttimeout' debug'
      Decompile sol' contract' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        decompile' sol' (Text.pack contract') solver'' smttimeout' debug'


---------------------------------
-- *** CLI implementation *** ---
---------------------------------


lex' :: FilePath -> IO ()
lex' f = do
  contents <- readFile f
  print $ lexer contents

parse' :: FilePath -> IO ()
parse' f = do
  contents <- readFile f
  validation (prettyErrs contents) print (parse $ lexer contents)

type' :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
type' f solver' smttimeout' debug' = do
  contents <- readFile f
  proceed contents (enrich <$> compile contents) $ \claims -> do
    checkCases claims solver' smttimeout' debug'
    B.putStrLn $ encode claims

parseSolver :: Maybe Text -> IO Solvers.Solver
parseSolver s = case s of
                  Nothing -> pure Solvers.CVC5
                  Just s' -> case Text.unpack s' of
                              "z3" -> pure Solvers.Z3
                              "cvc5" -> pure Solvers.CVC5
                              input -> render (text $ "unrecognised solver: " <> Text.pack input) >> exitFailure

prove :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
prove file' solver' smttimeout' debug' = do
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout') debug'
  contents <- readFile file'
  proceed contents (enrich <$> compile contents) $ \claims -> do
    checkCases claims solver' smttimeout' debug'
    let
      catModels results = [m | Sat m <- results]
      catErrors results = [e | e@SMT.Error {} <- results]
      catUnknowns results = [u | u@SMT.Unknown {} <- results]

      (<->) :: DocAnsi -> [DocAnsi] -> DocAnsi
      x <-> y = x <$$> line <> (indent 2 . vsep $ y)

      failMsg :: [SMT.SMTResult] -> DocAnsi
      failMsg results
        | not . null . catUnknowns $ results
            = text "could not be proven due to a" <+> (yellow . text $ "solver timeout")
        | not . null . catErrors $ results
            = (red . text $ "failed") <+> "due to solver errors:" <-> ((fmap viaShow) . catErrors $ results)
        | otherwise
            = (red . text $ "violated") <> colon <-> (fmap prettyAnsi . catModels $ results)

      passMsg :: DocAnsi
      passMsg = (green . text $ "holds") <+> (bold . text $ "∎")

      accumulateResults :: (Bool, DocAnsi) -> (Query, [SMT.SMTResult]) -> (Bool, DocAnsi)
      accumulateResults (status, report) (query, results) = (status && holds, report <$$> msg <$$> smt)
        where
          holds = all isPass results
          msg = identifier query <+> if holds then passMsg else failMsg results
          smt = if debug' then line <> getSMT query else emptyDoc

    solverInstance <- spawnSolver config
    pcResults <- mapM (runQuery solverInstance) (mkPostconditionQueries claims)
    invResults <- mapM (runQuery solverInstance) (mkInvariantQueries claims)
    stopSolver solverInstance

    let
      invTitle = line <> (underline . bold . text $ "Invariants:") <> line
      invOutput = foldl' accumulateResults (True, emptyDoc) invResults

      pcTitle = line <> (underline . bold . text $ "Postconditions:") <> line
      pcOutput = foldl' accumulateResults (True, emptyDoc) pcResults

    render $ vsep
      [ ifExists invResults invTitle
      , indent 2 $ snd invOutput
      , ifExists pcResults pcTitle
      , indent 2 $ snd pcOutput
      ]

    unless (fst invOutput && fst pcOutput) exitFailure


coq' :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
coq' f solver' smttimeout' debug' = do
  contents <- readFile f
  proceed contents (enrich <$> compile contents) $ \claims -> do
    checkCases claims solver' smttimeout' debug'
    TIO.putStr $ coq claims

decompile' :: FilePath -> Text -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
decompile' solFile' cid solver' timeout debug' = do
  let config = if debug' then debugActConfig else defaultActConfig
  cores <- fmap fromIntegral getNumProcessors
  json <- solc Solidity =<< TIO.readFile solFile'
  let (Contracts contracts, _, _) = fromJust $ readStdJSON json
  case Map.lookup ("hevm.sol:" <> cid) contracts of
    Nothing -> do
      putStrLn "compilation failed"
      exitFailure
    Just c -> do
      res <- runEnv (Env config) $ Solvers.withSolvers solver' cores 1 (naturalFromInteger <$> timeout) $ \solvers -> decompile c solvers
      case res of
        Left e -> do
          TIO.putStrLn e
          exitFailure
        Right s -> do
          putStrLn (prettyAct s)


hevm :: FilePath -> Maybe FilePath -> Maybe ByteString -> Maybe ByteString -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
hevm actspec sol' code' initcode' solver' timeout debug' = do
  let config = if debug' then debugActConfig else defaultActConfig
  cores <- liftM fromIntegral getNumProcessors
  specContents <- readFile actspec
  proceed specContents (enrich <$> compile specContents) $ \ (Act store contracts) -> do
    cmap <- createContractMap contracts
    res <- runEnv (Env config) $ Solvers.withSolvers solver' cores 1 (naturalFromInteger <$> timeout) $ \solvers ->
      checkContracts solvers store cmap
    case res of
      Success _ -> pure ()
      Failure err -> prettyErrs "" err
  where
    createContractMap :: [Contract] -> IO (Map Id (Contract, BS.ByteString, BS.ByteString))
    createContractMap contracts = do
      foldM (\cmap spec'@(Contract cnstr _) -> do
                let cid =  _cname cnstr
                (initcode'', runtimecode') <- getBytecode cid -- TODO do not reread the file each time
                pure $ Map.insert cid (spec', initcode'', runtimecode') cmap
            ) mempty contracts

    getBytecode :: Id -> IO (BS.ByteString, BS.ByteString)
    getBytecode cid =
      case (sol', code', initcode') of
        (Just f, Nothing, Nothing) -> do
          solContents  <- TIO.readFile f
          bytecodes (Text.pack cid) solContents
        (Nothing, Just _, Just _) -> render (text "Only Solidity file supported") >> exitFailure -- pure (i, c)
        (Nothing, Nothing, _) -> render (text "No runtime code is given" <> line) >> exitFailure
        (Nothing, _, Nothing) -> render (text "No initial code is given" <> line) >> exitFailure
        (Just _, Just _, _) -> render (text "Both Solidity file and runtime code are given. Please specify only one." <> line) >> exitFailure
        (Just _, _, Just _) -> render (text "Both Solidity file and initial code are given. Please specify only one." <> line) >> exitFailure


bytecodes :: Text -> Text -> IO (BS.ByteString, BS.ByteString)
bytecodes cid src = do
  json <- solc Solidity src
  let (Contracts sol', _, _) = fromJust $ readStdJSON json
  let err = error $ "Cannot find Solidity contract " <> Text.unpack cid
  pure ((fromMaybe err . Map.lookup ("hevm.sol" <> ":" <> cid) $ sol').creationCode,
        (fromMaybe err . Map.lookup ("hevm.sol" <> ":" <> cid) $ sol').runtimeCode)



-------------------
-- *** Util *** ---
-------------------

-- | Fail on error, or proceed with continuation
proceed :: Validate err => String -> err (NonEmpty (Pn, String)) a -> (a -> IO ()) -> IO ()
proceed contents comp continue = validation (prettyErrs contents) continue (comp ^. revalidate)

compile :: String -> Error String Act
compile = pure . annotate <==< typecheck <==< parse . lexer

prettyErrs :: Traversable t => String -> t (Pn, String) -> IO ()
prettyErrs contents errs = mapM_ prettyErr errs >> exitFailure
  where
  prettyErr (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
  prettyErr (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    hPutStrLn stderr msg
  prettyErr (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ msg <> ":"
    hPutStrLn stderr $ show line' <> " | " <> head cxt
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    where
      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs
