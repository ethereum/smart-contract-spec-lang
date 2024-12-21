{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Decompile where

import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import EVM.Solidity
import EVM.Solvers
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe
import Data.String.Here
import Data.Text (Text)
import Data.Text.IO qualified as T
import Data.Validation

import Act.Decompile
import Act.Print
import Act.CLI
import Act.HEVM_utils

import qualified EVM.Solvers as Solvers
import EVM.Effects

decompilerTests :: TestTree
decompilerTests = testGroup "decompiler"
   -- TODO allow empty behaviours in source Act
  [ expectFail $ testCase "noop" $ checkDecompilation "C" [i|
      contract C {
        function f() public {}
      }
      |]
  , testCase "implicit constructor" $ checkDecompilation "C" [i|
      contract C {
        uint x;
        function f(uint v) public {
          x = v;
        }
      }
      |]
  , testCase "simple storage write" $ checkDecompilation "C" [i|
      contract C {
        uint x = 0;
        function f(uint v) public {
          x = v;
        }
      }
      |]
  , testCase "checked addition" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(uint x, uint y) public returns (uint) {
          return x + y;
        }
      }
      |]
  , testCase "checked subtraction" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(uint x, uint y) public returns (uint) {
          return x - y;
        }
      }
      |]
  , testCase "checked multiplication" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(uint x, uint y) public returns (uint) {
          return x * y;
        }
      }
      |]
  , testCase "checked division" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(uint x, uint y) public returns (uint) {
          return x / y;
        }
      }
      |]
  , testCase "writing a complex expression to storage" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(uint x, uint y) public returns (uint) {
          uint z = (x + y) * (x - y) / (x * y);
          v = z;
          return z;
        }
      }
      |]
  , expectFail $ testCase "branching" $ checkDecompilation "C" [i|
      contract C {
        uint v = 0;
        function f(bool b, uint x, uint y) public returns (uint) {
          if (b) {
            return x;
          } else {
            return y;
          }
        }
      }
      |]
  ]

checkDecompilation :: Text -> Text -> Assertion
checkDecompilation contract src = do
  json <- solc Solidity src
  let (Contracts sol, _, _) = fromJust $ readStdJSON json
  let c = fromJust $ Map.lookup ("hevm.sol:" <> contract) sol
  runEnv (Env defaultActConfig) (Solvers.withSolvers CVC5 1 1 (Just 100000000) (decompile c)) >>= \case
    Left es -> do
      T.putStrLn es
      assertBool "decompilation should succeed" False
    Right s -> do
      case compile (prettyAct s) of
        Failure es -> do
          prettyErrs (prettyAct s) (NE.toList es)
          assertBool "decompiled output does not typecheck" False
        Success _ -> do
          assertBool "" True
