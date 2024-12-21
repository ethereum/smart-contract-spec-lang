{
module Act.Parse (module Act.Parse, showposn) where
import Prelude hiding (EQ, GT, LT)
import Data.Validation
import EVM.ABI
import qualified Data.List.NonEmpty as NonEmpty
import Act.Lex
import Act.Syntax.Untyped
import Act.Error
}

%name parse
%monad { Error String } { bindValidation } { pure }
%tokentype { Lexeme }
%error { parseError }

%token

  -- reserved word
  'constructor'               { L CONSTRUCTOR _ }
  'behaviour'                 { L BEHAVIOUR _ }
  'of'                        { L OF _ }
  'interface'                 { L INTERFACE _ }
  'creates'                   { L CREATES _ }
  'case'                      { L CASE _ }
  'returns'                   { L RETURNS _ }
  'storage'                   { L STORAGE _ }
  'noop'                      { L NOOP _ }
  'iff in range'              { L IFFINRANGE _ }
  'inRange'                   { L INRANGE _ }
  'iff'                       { L IFF _ }
  'pointers'                  { L POINTERS _ }
  'and'                       { L AND _ }
  'not'                       { L NOT _ }
  'or'                        { L OR _ }
  'true'                      { L TRUE _ }
  'false'                     { L FALSE _ }
  'create'                    { L CREATE _ }
  'as'                        { L AS _ }
  'mapping'                   { L MAPPING _ }
  'ensures'                   { L ENSURES _ }
  'invariants'                { L INVARIANTS _ }
  'if'                        { L IF _ }
  'then'                      { L THEN _ }
  'else'                      { L ELSE _ }
  'at'                        { L AT _ }
  'pre'                       { L PRE _ }
  'post'                      { L POST _ }

  -- builtin types
  'uint'                      { L (UINT $$) _ }
  'int'                       { L (INT $$) _ }
  'bytes'                     { L (BYTES $$) _ }
  'address'                   { L ADDRESS _ }
  'bool'                      { L BOOL _ }
  'string'                    { L STRING _ }

  -- builtin functions
  'newAddr'                   { L NEWADDR _ }

  -- environment variables
  'CALLER'                    { L CALLER _ }
  'CALLVALUE'                 { L CALLVALUE _ }
  'CALLDEPTH'                 { L CALLDEPTH _ }
  'ORIGIN'                    { L ORIGIN _ }
  'BLOCKHASH'                 { L BLOCKHASH _ }
  'BLOCKNUMBER'               { L BLOCKNUMBER _ }
  'DIFFICULTY'                { L DIFFICULTY _ }
  'CHAINID'                   { L CHAINID _ }
  'GASLIMIT'                  { L GASLIMIT _ }
  'COINBASE'                  { L COINBASE _ }
  'TIMESTAMP'                 { L TIMESTAMP _ }
  'THIS'                      { L THIS _ }
  'NONCE'                     { L NONCE _ }


  -- symbols
  ':='                        { L ASSIGN _ }
  '=>'                        { L ARROW _ }
  '|->'                       { L POINTSTO _ }
  '=='                        { L EQEQ _ }
  '=/='                       { L NEQ _ }
  '>='                        { L GE _ }
  '<='                        { L LE _ }
  '++'                        { L CAT _ }
  '..'                        { L SLICE _ }
  '('                         { L LPAREN _ }
  ')'                         { L RPAREN _ }
  '['                         { L LBRACK _ }
  ']'                         { L RBRACK _ }
  '='                         { L EQ _ }
  '>'                         { L GT _ }
  '<'                         { L LT _ }
  ':'                         { L COLON _ }
  '+'                         { L PLUS _ }
  '-'                         { L MINUS _ }
  '*'                         { L STAR _ }
  '/'                         { L SLASH _ }
  '%'                         { L MOD _ }
  '^'                         { L CARET _ }
  '_'                         { L SCORE _ }
  '.'                         { L DOT _ }
  ','                         { L COMMA _ }

  id                          { L (ID _) _ }

  ilit                        { L (ILIT _) _ }

{- --- associativity and precedence ---
boolean operations have universally lower precedence than numeric
operations

no operators are right associative

some examples:
`a == b and not c == d` should parse as `(a == b) and (not (c == d))`
`a * b ^ c % d` should parse as `a * ((b ^ c) % d)`

-}

%nonassoc '[' ']' '.'

-- boolean
%nonassoc '=>'
%left 'and' 'or'
%nonassoc 'not'
%left '==' '=/='
%nonassoc '<=' '<' '>=' '>'

-- numeric
%left '+' '-'
%left '*' '/'
%nonassoc '%'
%left '^'

-- bytestrings
%left '++'

%%

ACT : list(Contract)                                  { Main $1 }


-- parameterized productions --

pair(a,b) : a b                                       { ($1,$2) }

seplist(x, sep) : {- empty -}                         { []      }
                | x                                   { [$1]    }
                | x sep seplist(x, sep)               { $1 : $3 }

nonempty(x) : x                                       { [$1]    }
            | x nonempty(x)                           { $1 : $2 }

list(x) : {- empty -}                                 { []      }
        | x list(x)                                   { $1 : $2 }

optblock(label, x) : label nonempty(x)                { $2 }
                   | {- empty -}                      { [] }

-- rules --

Contract : Constructor list(Transition)              { Contract $1 $2 }
         | nonempty(Transition)                      { Contract (emptyConstructor $ head $1) $1 }

Transition : 'behaviour' id 'of' id
             Interface
             Pointers
             list(Precondition)
             Cases
             Ensures                                  { Transition (posn $1) (name $2) (name $4)
                                                        $5 $6 $7 $8 $9 }

Constructor : 'constructor' 'of' id
              CInterface
              Pointers
              list(Precondition)
              Creation
              Ensures
              Invariants                              { Definition (posn $3) (name $3)
                                                         $4 $5 $6 $7 $8 $9 }

Ensures : optblock('ensures', Expr)                   { $1 }

Invariants : optblock('invariants', Expr)             { $1 }

Pointers : optblock('pointers', Pointer)              { $1 }

Interface : 'interface' id '(' seplist(Decl, ',') ')' { Interface (name $2) $4 }

CInterface : 'interface' 'constructor' '(' seplist(Decl, ',') ')' { Interface "constructor" $4 }

Pointer : id '|->' id                                 { PointsTo (posn $2) (name $1) (name $3) }

Cases : Post                                          { Direct $1 }
      | nonempty(Case)                                { Branches $1 }

Case : 'case' Expr ':' Post                           { Case (posn $1) $2 $4 }


Post  : Storage                                       { Post $1 Nothing }
      | Returns                                       { Post [] (Just $1) }
      | Storage Returns                               { Post $1 (Just $2) }

Returns : 'returns' Expr                              { $2 }

Storage : 'storage' nonempty(Store)                   { $2 }

Precondition : 'iff' nonempty(Expr)                   { Iff (posn $1) $2 }
             | 'iff in range' AbiType nonempty(Expr)  { IffIn (posn $1) $2 $3 }

Store : Entry '=>' Expr                               { Rewrite $1 $3 }

Entry : id                                            { EVar (posn $1) (name $1) }
      | Entry '[' Expr ']' list(Index)                { EMapping (posn $2) $1 ($3:$5) }
      | Entry '.' id                                  { EField (posn $2) $1 (name $3) }

Index : '[' Expr ']'                                  { $2 }


Creation : optblock('creates',Assign)                 { Creates $1 }

Assign : StorageVar ':=' Expr                         { AssignVal $1 $3 }
       | StorageVar ':=' '[' seplist(Defn, ',') ']'   { AssignMany $1 $4 }

Defn : Expr ':=' Expr                                 { Defn $1 $3 }
Decl : AbiType id                                     { Decl $1 (name $2) }

StorageVar : SlotType id                              { StorageVar (posn $2) $1 (name $2) }

AbiType : 'uint'
         { case validsize $1 of
	     True  -> AbiUIntType $1
	     False -> error $ "invalid uint size: uint" <> (show $1)
	 }
       | 'int'
         { case validsize $1 of
	     True  -> AbiIntType $1
	     False -> error $ "invalid int size: int" <> (show $1)
	 }
       | 'bytes'                                      { AbiBytesType $1 }
       | AbiType '[' ilit ']'                         { AbiArrayType (fromIntegral $ value $3) $1 }
       | 'address'                                    { AbiAddressType }
       | 'bool'                                       { AbiBoolType }
       | 'string'                                     { AbiStringType }

Type : AbiType                                        { PrimitiveType $1 }
     | id                                             { ContractType $ name $1 }

SlotType : 'mapping' '(' MappingArgs ')'              { (uncurry StorageMapping) $3 }
         | Type                                       { StorageValue $1 }


MappingArgs : Type '=>' Type                          { ($1 NonEmpty.:| [], $3) }
            | Type '=>' 'mapping' '(' MappingArgs ')' { (NonEmpty.cons $1 (fst $5), snd $5)  }


Expr : '(' Expr ')'                                   { $2 }

  -- terminals
  | ilit                                              { IntLit (posn $1) (value $1) }
  -- missing string literal
  -- missing wildcard

  -- boolean expressions
  | Expr 'and' Expr                                   { EAnd  (posn $2) $1 $3 }
  | Expr 'or'  Expr                                   { EOr   (posn $2) $1 $3 }
  | Expr '=>'  Expr                                   { EImpl (posn $2) $1 $3 }
  | 'not'      Expr                                   { ENot  (posn $1) $2 }
  | Expr '=='  Expr                                   { EEq   (posn $2) $1 $3 }
  | Expr '=/=' Expr                                   { ENeq  (posn $2) $1 $3 }
  | Expr '<='  Expr                                   { ELEQ  (posn $2) $1 $3 }
  | Expr '<'   Expr                                   { ELT   (posn $2) $1 $3 }
  | Expr '>='  Expr                                   { EGEQ  (posn $2) $1 $3 }
  | Expr '>'   Expr                                   { EGT   (posn $2) $1 $3 }
  | 'true'                                            { BoolLit (posn $1) True }
  | 'false'                                           { BoolLit (posn $1) False }
  | 'inRange' '(' AbiType ',' Expr ')'                { EInRange (posn $1) $3 $5 }
  -- integer expressions
  | Expr '+'   Expr                                   { EAdd (posn $2)  $1 $3 }
  | Expr '-'   Expr                                   { ESub (posn $2)  $1 $3 }
  | Expr '*'   Expr                                   { EMul (posn $2)  $1 $3 }
  | Expr '/'   Expr                                   { EDiv (posn $2)  $1 $3 }
  | Expr '%'   Expr                                   { EMod (posn $2)  $1 $3 }
  | Expr '^'   Expr                                   { EExp (posn $2)  $1 $3 }

  -- composites
  | 'if' Expr 'then' Expr 'else' Expr                 { EITE (posn $1) $2 $4 $6 }
  | Entry                                             { EUTEntry $1 }
  | 'pre'  '(' Entry ')'                              { EPreEntry $3 }
  | 'post' '(' Entry ')'                              { EPostEntry $3 }
  | 'create' id '(' seplist(Expr, ',') ')'            { ECreate (posn $2) (name $2) $4 }
  | Expr '++' Expr                                    { ECat   (posn $2) $1 $3 }
--  | id '[' Expr '..' Expr ']'                       { ESlice (posn $2) $1 $3 $5 }
  | 'CALLER'                                          { EnvExp (posn $1) Caller }
  | 'CALLDEPTH'                                       { EnvExp (posn $1) Calldepth }
  | 'ORIGIN'                                          { EnvExp (posn $1) Origin }
  | 'BLOCKHASH'                                       { EnvExp (posn $1) Blockhash }
  | 'BLOCKNUMBER'                                     { EnvExp (posn $1) Blocknumber }
  | 'DIFFICULTY'                                      { EnvExp (posn $1) Difficulty }
  | 'CHAINID'                                         { EnvExp (posn $1) Chainid }
  | 'GASLIMIT'                                        { EnvExp (posn $1) Gaslimit }
  | 'COINBASE'                                        { EnvExp (posn $1) Coinbase }
  | 'TIMESTAMP'                                       { EnvExp (posn $1) Timestamp }
  | 'CALLVALUE'                                       { EnvExp (posn $1) Callvalue }
  | 'THIS'                                            { EnvExp (posn $1) This }
  | 'NONCE'                                           { EnvExp (posn $1) Nonce }
  -- missing builtins
  | 'newAddr' '(' Expr ',' Expr ')'                   { ENewaddr (posn $1) $3 $5 }

{

nowhere = AlexPn 0 0 0

lastPos = AlexPn (-1) (-1) (-1)

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Error String a
parseError [] = throw (lastPos, "Expected more tokens")
parseError ((L token pn):_) =
  throw (pn, concat [
    "parsing error at token ",
    show token])

emptyConstructor :: Transition -> Definition
emptyConstructor (Transition _ _ c _ _ _ _ _) = Definition nowhere c (Interface "constructor" []) [] [] (Creates []) [] []

}
