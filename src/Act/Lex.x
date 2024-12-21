{
module Act.Lex
  ( LEX (..)
  , Lexeme (..)
  , AlexPosn (..)
  , lexer
  , posn
  , showposn
  , name
  , value
  ) where

import Prelude hiding (EQ, GT, LT)

}

%wrapper "posn"

$digit = 0-9                    -- digits
$alpha = [a-z A-Z]              -- alphabetic characters
$ident = [$alpha _]
$space = [\ \t\f\v\r]
$negative = \-

tokens :-

  $white+                               ;

  -- reserved words
  constructor                           { mk CONSTRUCTOR }
  behaviour                             { mk BEHAVIOUR }
  of                                    { mk OF }
  interface                             { mk INTERFACE }
  creates                               { mk CREATES }
  case                                  { mk CASE }
  returns                               { mk RETURNS }
  storage                               { mk STORAGE }
  noop                                  { mk NOOP }

  iff $white+ in $white+ range          { mk IFFINRANGE }
  inRange                               { mk INRANGE }
  iff                                   { mk IFF }
  pointers                              { mk POINTERS }
  and                                   { mk AND }
  not                                   { mk NOT }
  or                                    { mk OR }
  true                                  { mk TRUE }
  false                                 { mk FALSE }
  create                                { mk CREATE }
  as                                    { mk AS }
  mapping                               { mk MAPPING }
  ensures                               { mk ENSURES }
  invariants                            { mk INVARIANTS }
  if                                    { mk IF }
  then                                  { mk THEN }
  else                                  { mk ELSE }
  at                                    { mk AT }
  pre                                   { mk PRE }
  post                                  { mk POST }

  -- builtin types
  uint $digit+                          { \ p s -> L (UINT (read (drop 4 s))) p }
  int  $digit+                          { \ p s -> L (INT  (read (drop 3 s))) p }
  uint                                  { mk (UINT 256) }
  int                                   { mk (INT 256) }
  bytes $digit+                         { \ p s -> L (BYTES (read (drop 5 s))) p }
  bytes                                 { error "TODO" }
  address                               { mk ADDRESS }
  bool                                  { mk BOOL }
  string                                { mk STRING }

  -- builtin functions
  newAddr                               { mk NEWADDR }

  -- environment vars
  CALLER                                { mk CALLER }
  CALLVALUE                             { mk CALLVALUE }
  CALLDEPTH                             { mk CALLDEPTH }
  ORIGIN                                { mk ORIGIN }
  BLOCKHASH                             { mk BLOCKHASH }
  BLOCKNUMBER                           { mk BLOCKNUMBER }
  DIFFICULTY                            { mk DIFFICULTY }
  CHAINID                               { mk CHAINID }
  GASLIMIT                              { mk GASLIMIT }
  COINBASE                              { mk COINBASE }
  TIMESTAMP                             { mk TIMESTAMP }
  THIS                                  { mk THIS }  -- normally called address, but that's taken
  NONCE                                 { mk NONCE } -- technically not an opcode

  -- symbols
  ":="                                  { mk ASSIGN }
  "=>"                                  { mk ARROW }
  "|->"                                 { mk POINTSTO }
  "=="                                  { mk EQEQ }
  "=/="                                 { mk NEQ }
  ">="                                  { mk GE }
  "<="                                  { mk LE }
  "++"                                  { mk CAT }
  ".."                                  { mk SLICE }
  "("                                   { mk LPAREN }
  ")"                                   { mk RPAREN }
  "["                                   { mk LBRACK }
  "]"                                   { mk RBRACK }
  "="                                   { mk Act.Lex.EQ }
  ">"                                   { mk Act.Lex.GT }
  "<"                                   { mk Act.Lex.LT }
  ":"                                   { mk COLON }
  "+"                                   { mk PLUS }
  "-"                                   { mk MINUS }
  "*"                                   { mk STAR }
  "/"                                   { mk SLASH }
  "%"                                   { mk MOD }
  "^"                                   { mk CARET }
  "_"                                   { mk SCORE }
  "."                                   { mk DOT }
  ","                                   { mk COMMA }
  "//"                                  [.]* ; -- Toss single line comments
  -- identifiers
  $ident ($ident | $digit)*             { \ p s -> L (ID s) p }

  -- literals
  $negative? $digit+                    { \ p s -> L (ILIT (read s)) p }

{

data LEX =

  -- reserved words
    BEHAVIOUR
  | CONSTRUCTOR
  | OF
  | INTERFACE
  | CREATES
  | CASE
  | RETURNS
  | STORAGE
  | NOOP
  | IFFINRANGE
  | INRANGE
  | IFF
  | POINTERS
  | POINTSTO
  | AND
  | NOT
  | OR
  | TRUE
  | FALSE
  | CREATE
  | AS
  | MAPPING
  | ENSURES
  | INVARIANTS
  | IF
  | THEN
  | ELSE
  | AT
  | PRE
  | POST

  -- builtin types
  | UINT  Int
  | INT   Int
  | BYTES Int
  | ADDRESS
  | BOOL
  | STRING

  -- builtin functions
  | NEWADDR

  -- environment vars
  | CALLER
  | CALLVALUE
  | CALLDEPTH
  | ORIGIN
  | BLOCKHASH
  | BLOCKNUMBER
  | DIFFICULTY
  | CHAINID
  | GASLIMIT
  | COINBASE
  | TIMESTAMP
  | THIS
  | NONCE

  -- symbols
  | ASSIGN
  | ARROW
  | EQEQ
  | NEQ
  | GE
  | LE
  | CAT
  | SLICE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | EQ
  | GT
  | LT
  | COLON
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | MOD
  | CARET
  | SCORE
  | DOT
  | COMMA

  -- identifiers
  | ID String

  -- literals
  | ILIT Integer

  deriving (Eq, Show)

data Lexeme = L LEX AlexPosn
  deriving (Eq, Show)

-- annoying that we can't override the show instance for this here
showposn (AlexPn _ line column) =
  concat [show line, ":", show column]

posn :: Lexeme -> AlexPosn
posn (L _ p) = p

name :: Lexeme -> String
name (L (ID s) _) = s
name _ = error "unsupported arg to name"

value :: Lexeme -> Integer
value (L (ILIT i) _) = i
value _ = error "unsupported arg to value"

-- helper function to reduce boilerplate
mk :: LEX -> (AlexPosn -> String -> Lexeme)
mk lexeme p _ = L lexeme p

lexer :: String -> [Lexeme]
lexer = alexScanTokens
}
