{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Prelude hiding (GT, LT)
import Test.Tasty
import Test.Tasty.QuickCheck (Gen, arbitrary, testProperty, Property, (===), counterexample, whenFail)
import Test.QuickCheck.Instances.ByteString()
import Test.QuickCheck.GenT
import Test.QuickCheck.Monadic

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Data.Map (fromList)

import Act.CLI (compile)
import Act.Error
import Act.Print (prettyBehaviour, prettyAct)
import Act.SMT
import Act.Syntax.Annotated

import Text.Pretty.Simple
import Data.Text.Lazy as T (unpack)

import Decompile

import Debug.Trace

-- Transformer stack to keep track of whether we are to generate expressions
-- with exponentiation or not (for compatibility with SMT).
type ExpoGen a = GenT (Reader Bool) a

noExponents, withExponents :: ExpoGen a -> Gen a
noExponents   = fmap (`runReader` False) . runGenT
withExponents = fmap (`runReader` True)  . runGenT


-- *** Test Cases *** --

main :: IO ()
main = defaultMain $ testGroup "act"
  [ decompilerTests
  , testGroup "frontend"
      {-
         Generates a random behaviour, prints it, runs it through the frontend
         (lex -> parse -> type), and then checks that the typechecked output matches the
         generated behaviour.

         If the generated behaviour contains some preconditions, then the structure of the
         fail spec is also checked.
      -}
      [ testProperty "roundtrip" . withExponents $ do
          behv@(Behaviour _ contract _ _ _ _ _ _ _) <- sized genBehv
          let actual = compile $ prettyBehaviour behv
              expected = Act (defaultStore contract) [Contract (defaultCtor contract) [behv]]
          return $ case actual of
            Success a ->
              let err_str = "Actual:\n" <> prettyAct a <> show a <> "Expected:\n" <> prettyAct expected <> show expected in
              whenFail (putStrLn err_str) $ a === expected
            Failure err -> counterexample ("Internal error: compilation of Act failed\n" <> show err <> "\n") False
      ]

  , testGroup "smt"
      [ testProperty "generated smt is well typed (z3)" . noExponents $ typeCheckSMT Z3
      --, testProperty "generated smt is well typed (cvc4)" . noExponents $ typeCheckSMT CVC4 -- This test is too sloooowwww :(
      ]
  ]


defaultStore :: Id -> Store
defaultStore c = fromList [(c,mempty)]

defaultCtor :: Id -> Constructor
defaultCtor c = Constructor { _cname = c
                            , _cinterface = Interface c []
                            , _cpointers = []
                            , _cpreconditions = []
                            , _cpostconditions = []
                            , _invariants = []
                            , _initialStorage = []}


typeCheckSMT :: Solver -> GenT (Reader Bool) Property
typeCheckSMT solver = do
  behv <- genBehv 3
  let smtconf = SMTConfig solver 1 False
      smt = mkPostconditionQueriesBehv behv
  pure . monadicIO . run $ runQueries smtconf smt
    where
      runQueries smtconf queries = do
        solverInstance <- spawnSolver smtconf
        all isNothing <$> mapM (askSMT solverInstance) queries

      askSMT solverInstance query = sendLines solverInstance ("(reset)" : (lines . show . getSMT $ query))


-- *** QuickCheck Generators *** --


data Names = Names { _ints :: [(String, AbiType)]
                   , _bools :: [(String, AbiType)]
                   , _bytes :: [(String, AbiType)]
                   } deriving (Show)

{-
   Generates a random behaviour given a mode and a size.

   Concrete behaviours contain no variables and take no arguments.
   Symbolic behaviours take arguments in the interface and reference them in their expressions.

   Storage conditions are currently not generated.
-}
genBehv :: Int -> ExpoGen Behaviour
genBehv n = do
  name <- ident
  contract <- ident
  ifname <- ident
  abiNames <- genNames
  preconditions <- listOf $ genExpBool abiNames n
  returns <- Just <$> genTypedExp abiNames n
  postconditions <- listOf $ genExpBool abiNames n
  let iface = Interface ifname (mkDecls abiNames)
  return Behaviour { _name = name
                   , _contract = contract
                   , _interface = iface
                   , _pointers = []
                   , _preconditions = preconditions
                   , _caseconditions = [LitBool nowhere True]
                   , _postconditions = postconditions
                   , _stateUpdates = []
                   , _returns = returns
                   }


mkDecls :: Names -> [Decl]
mkDecls (Names ints bools bytes) = mkDecl <$> names
  where
    mkDecl (n, typ) = Decl typ n
    names = ints ++ bools ++ bytes


genType :: ActType -> ExpoGen AbiType
genType typ = case typ of
  AInteger -> oneof [ AbiUIntType <$> validIntSize
                    , AbiIntType <$> validIntSize
                    , return AbiAddressType
                    , AbiBytesType <$> validBytesSize
                    ]
  ABoolean -> return AbiBoolType
  AByteStr -> return AbiStringType
                   --, return AbiBytesDynamicType -- TODO: needs frontend support
  where
    validIntSize = elements [ x | x <- [8..256], x `mod` 8 == 0 ]
    validBytesSize = elements [1..32]


genTypedExp :: Names -> Int -> ExpoGen TypedExp
genTypedExp names n = oneof
  [ _TExp <$> genExpInt names n
  , _TExp <$> genExpBool names n
  , _TExp <$> genExpBytes names n
  ]


-- TODO: literals, cat slice, ITE, storage, ByStr
genExpBytes :: Names -> Int -> ExpoGen (Exp AByteStr)
genExpBytes names _ = selectVar SByteStr names

-- TODO: ITE, storage
genExpBool :: Names -> Int -> ExpoGen (Exp ABoolean)
genExpBool names 0 = oneof
  [ selectVar SBoolean names
  , LitBool nowhere <$> liftGen arbitrary
  ]
genExpBool names n = oneof
  [ liftM2 (And nowhere) subExpBool subExpBool
  , liftM2 (Or nowhere) subExpBool subExpBool
  , liftM2 (Impl nowhere) subExpBool subExpBool
  , liftM2 (Eq nowhere SInteger) subExpInt subExpInt
  , liftM2 (Eq nowhere SBoolean) subExpBool subExpBool
  , liftM2 (Eq nowhere SByteStr) subExpBytes subExpBytes
  , liftM2 (NEq nowhere SInteger) subExpInt subExpInt
  , liftM2 (LT nowhere) subExpInt subExpInt
  , liftM2 (LEQ nowhere) subExpInt subExpInt
  , liftM2 (GEQ nowhere) subExpInt subExpInt
  , liftM2 (GT nowhere) subExpInt subExpInt
  , Neg nowhere <$> subExpBool
  ]
  where subExpBool = genExpBool names (n `div` 2)
        subExpBytes = genExpBytes names (n `div` 2)
        subExpInt = genExpInt names (n `div` 2)


-- TODO: storage
genExpInt :: Names -> Int -> ExpoGen (Exp AInteger)
genExpInt names 0 = oneof
  [ LitInt nowhere <$> liftGen arbitrary
  , selectVar SInteger names
  , return $ IntEnv nowhere Caller
  , return $ IntEnv nowhere Callvalue
  , return $ IntEnv nowhere Calldepth
  , return $ IntEnv nowhere Origin
  , return $ IntEnv nowhere Blocknumber
  , return $ IntEnv nowhere Difficulty
  , return $ IntEnv nowhere Chainid
  , return $ IntEnv nowhere Gaslimit
  , return $ IntEnv nowhere Coinbase
  , return $ IntEnv nowhere Timestamp
  , return $ IntEnv nowhere This
  , return $ IntEnv nowhere Nonce
  ]
genExpInt names n = do
  expo <- lift ask
  oneof $
    (if expo
      then ((liftM2 (Exp nowhere) subExpInt subExpInt):)
      else id)
        [ liftM2 (Add nowhere) subExpInt subExpInt
        , liftM2 (Sub nowhere) subExpInt subExpInt
        , liftM2 (Mul nowhere) subExpInt subExpInt
        , liftM2 (Div nowhere) subExpInt subExpInt
        , liftM2 (Mod nowhere) subExpInt subExpInt
        , liftM3 (ITE nowhere) subExpBool subExpInt subExpInt
        ]
  where subExpInt = genExpInt names (n `div` 2)
        subExpBool = genExpBool names (n `div` 2)


selectVar :: SType a -> Names -> ExpoGen (Exp a)
selectVar typ (Names ints bools bytes) = do
  let names = case typ of
                SInteger -> ints
                SBoolean -> bools
                SByteStr -> bytes
  idx <- elements [0..((length names)-1)]
  let (x, at) = names!!idx
  return $ TEntry nowhere Pre SCalldata (Item typ (PrimitiveType at) (CVar nowhere at x))

-- | Generates a record type containing identifier names.
-- Ensures each generated name appears once only.
-- Names are seperated by type to ensure that e.g. an int expression does not reference a bool
genNames :: ExpoGen Names
genNames = mkNames <$> (addType =<< (split <$> unique))
  where
    mkNames :: [[(String, AbiType)]] -> Names
    mkNames cs = Names { _ints = cs!!0
                       , _bools = cs!!1
                       , _bytes = cs!!2
                       }

    unique :: ExpoGen [String]
    unique = (Set.toList . Set.fromList <$> (listOf1 ident))
                `suchThat` (\l -> (length l) > 3)

    split :: Show a => [a] -> [[a]]
    split l = go (length l `div` 3) l
      where
        go _ [] = []
        go n xs = ys : go n zs
          where (ys,zs) = splitAt n xs

    addType :: Show a => [[a]] -> ExpoGen [[(a, AbiType)]]
    addType (ints:bools:bytes:_) = do
        ints' <- mapM (genVarType AInteger) ints
        bools' <- mapM (genVarType ABoolean) bools
        bytes' <- mapM (genVarType AByteStr) bytes
        return [ints', bools', bytes']
    addType l = error $ "Internal error: Expecting list with exactly three elements " <> show l

    genVarType typ x = do
      t <- genType typ
      return (x, t)

ident :: ExpoGen String
ident = liftM2 (<>) (listOf1 (elements chars)) (listOf (elements $ chars <> digits))
          `suchThat` (`notElem` reserved)
  where
    chars = ['a'..'z'] <> ['A'..'Z']
    digits = ['0'..'9']
    reserved = -- TODO: add uintX intX and bytesX type names
      [ "behaviour", "of", "interface", "creates", "case", "returns", "storage", "noop", "iff"
      , "and", "not", "or", "true", "false", "mapping", "ensures", "invariants", "if", "then"
      , "else", "at", "uint", "int", "bytes", "address", "bool", "string", "newAddr", "create" ]


-- ** Debugging Utils ** --


traceb :: Behaviour -> Behaviour
traceb b = trace (prettyBehaviour b) b

tracec :: String -> Act -> Act
tracec msg cs = trace ("\n" <> msg <> "\n\n" <> unpack (pShow cs)) cs

trace' :: Show a => a -> a
trace' x = trace (show x) x
