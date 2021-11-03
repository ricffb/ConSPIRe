{
module Parser.CSP (parse) where

import qualified Data.Set as Set
import Data.Char
}

%name parse
%tokentype { Token }
%error { parseError }

%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF }

%token 
      STOP            { TokenStop }
      SKIP            { TokenSkip }
      var             { TokenVar $$ }
      name            { TokenName $$ }  
      if              { TokenIf }
      then            { TokenThen }
      else            { TokenElse }
      '='             { TokenEq }
      '=='            { TokenEquals }
      '!='            { TokenNotEquals }
      '+'             { TokenPlus }
      '-'             { TokenMinus }
      '*'             { TokenTimes }
      '/'             { TokenDiv }
      '('             { TokenOB }
      ')'             { TokenCB }
      '{'             { TokenOCB }
      '}'             { TokenCCB }
      '\\'            { TokenSlash }
      '|'             { TokenBar }
      '.'             { TokenDot }
      ';'             { TokenSemicolon }
      '[]'            { TokenBox }
      '|~|'           { TokenInt }
      '->'            { TokenPrefix }
      '<-'            { TokenAssign }
      '[|'            { TokenParOpen }
      '|]'            { TokenParClose }
      '@'             { TokenAmpersat }
      ':'             { TokenColon }
      '?'             { TokenQm }
      '!'             { TokenExcl }
      '$'             { TokenDollar }
      ','             { TokenComma }

%nonassoc '=='
%right '.'
%left '!' '?' '$'
%right '->'
%left ';'
%left '[]'
%left '|~|'
%left '\\'

%%
Proc :: {Proc}
Proc  : STOP                        { STOP }
      | SKIP                        { SKIP }
      | name                        { ProcName $1 }
      | Action '->' Proc            { Prefix $1 $3 }
      | Proc '[]' Proc              { ExtChoice $1 $3 }
      | Proc '|~|' Proc             { IntChoice $1 $3 }
      | if Exp then Proc else Proc  { Ite $2 $4 $6 }
      | Proc ';' Proc               { Seq $1 $3 }
      | Proc '[|' Set '|]' Proc     { Parallel $3 $1 $5 }
      | Proc '\\' Set               { Hide $3 $1 }
      | '|~|' var ':' Set '@' Proc  { ReplIntChoice $2 $4 $6 }
      | '(' Proc ')'                { $2 }

Set  ::  { Set.Set String }
Set   : '{' SetCont '}' { Set.fromList $2 }

SetCont ::  { [String] }
    : Seq {$1}
      {-  | Exp '|' VarDecls -}

{-
Type : name 

VarDecls : VarDecl
         | VarDecls ',' VarDecl

VarDecl : var '<-' Type -}

Seq :: { [String] }
Seq : Seq ',' var    { $3 : $1 }
      | {- empty -}  { [] }


Action :: { Action } 
        : var ActionS { ($1, reverse $2) }

ActionS :: { [ActionI] }
       : ActionS '?' var      { Input $3 : $1 }
       | ActionS '!' var       { Output $3 : $1 }
       | ActionS '$' var       { Selection $3 : $1 }
       | {- empty -}           { [] }

Exp   : Exp '==' Exp            { Eq $1 $3 }
      | Exp '.' Exp             { Dot $1 $3 }
      | var                     { Var $1 }
      | '(' Exp ')'             { Brack $2 }


{
type LineNumber = Int

data ParseResult a
	= ParseOk a
	| ParseFail String
      deriving Show

type P a = String -> LineNumber -> ParseResult a


thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \s l -> 
      case m s l of
      ParseFail s -> ParseFail s
      ParseOk a -> k a s l

returnP :: a -> P a
returnP a = \s l -> ParseOk a

data Proc 
    = STOP
    | SKIP
    | ProcName String
    | Prefix Action Proc
    | ExtChoice Proc Proc
    | IntChoice Proc Proc
    | Ite Exp Proc Proc
    | Seq Proc Proc
    | Parallel (Set.Set String) Proc Proc
    | Hide (Set.Set String) Proc
    | ReplIntChoice String (Set.Set String) Proc
    deriving (Show)
data Type
    = TypeName String

data Exp
  = Eq Exp Exp
  | Dot Exp Exp
  | Var String
  | Brack Exp
  deriving (Show)

data ActionI
  = Input String
  | Output String
  | Selection String
  deriving (Show)

type Action = (String, [ActionI])

data Token
  = TokenSkip
  | TokenStop
  | TokenVar String
  | TokenName String
  | TokenIf 
  | TokenThen 
  | TokenElse
  | TokenEq
  | TokenEquals
  | TokenNotEquals
  | TokenPlus
  | TokenMinus
  | TokenTimes
  | TokenDiv
  | TokenOB
  | TokenCB
  | TokenOCB
  | TokenCCB
  | TokenSlash
  | TokenBar
  | TokenDot
  | TokenSemicolon
  | TokenBox
  | TokenInt
  | TokenPrefix
  | TokenAssign
  | TokenParOpen
  | TokenParClose
  | TokenAmpersat
  | TokenColon
  | TokenQm
  | TokenDollar
  | TokenExcl
  | TokenComma
  | TokenEOF
  deriving (Show)

getLineNo :: P LineNumber
getLineNo = \s l -> ParseOk l

failP :: String -> P a
failP err = \s l -> ParseFail err

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s l ->
    case m s l of
      ParseOk a -> ParseOk a
      ParseFail e -> k e s l

happyError :: P a
happyError = \s i -> error (
	"Parse error in line " ++ show (i::Int) ++ "\n" ++ s)

parseError :: Token -> P a
parseError tok =
  getLineNo `thenP` \line ->
    failP (show line ++ ": parse error at token " ++ show tok)

lexer :: (Token -> P a) -> P a
lexer cont s =
  case s of
    [] -> cont TokenEOF []
    ('\n' : cs) -> \line -> lexer cont cs (line + 1)
    (c : cs)
        | isSpace c -> lexer cont cs
        | isAlpha c -> lexVar cont (c : cs)
    ('=':'=':cs) -> cont TokenEquals cs
    ('!':'=':cs) -> cont TokenNotEquals cs
    ('[':']':cs) -> cont TokenBox cs
    ('|':'~':'|':cs) -> cont TokenInt cs
    ('-':'>':cs) -> cont TokenPrefix cs
    ('<':'-':cs) -> cont TokenAssign cs
    ('[':'|':cs) -> cont TokenParOpen cs
    ('|':']':cs) -> cont TokenParClose cs
    ('=' : cs) -> cont TokenEq cs
    ('+' : cs) -> cont TokenPlus cs
    ('-' : cs) -> cont TokenMinus cs
    ('*' : cs) -> cont TokenTimes cs
    ('/' : cs) -> cont TokenDiv cs
    ('(' : cs) -> cont TokenOB cs
    (')' : cs) -> cont TokenCB cs
    ('{' : cs) -> cont TokenOCB cs
    ('}' : cs) -> cont TokenCCB cs
    ('\\' : cs) -> cont TokenSlash cs
    ('|' : cs) -> cont TokenBar cs
    ('.' : cs) -> cont TokenDot cs
    (';' : cs) -> cont TokenSemicolon cs
    ('@':cs) -> cont TokenAmpersat cs
    ('!':cs) -> cont TokenExcl cs
    ('?':cs) -> cont TokenQm cs
    ('$':cs) -> cont TokenDollar cs
    (',':cs) -> cont TokenComma cs
  where
      lexVar :: (Token -> P a) -> P a
      lexVar cont cs =
            case span isAlpha cs of
            ("if", rest) -> cont TokenIf rest
            ("then", rest) -> cont TokenThen rest
            ("else", rest) -> cont TokenElse rest
            ("STOP", rest) -> cont TokenStop rest
            ("SKIP", rest) -> cont TokenSkip rest
            (c:var, rest)
                | isUpper c -> cont (TokenName $ c:var) rest
                | otherwise -> cont (TokenVar $ c:var) rest



{--
lexNum cs = TokenInt (read num) : lexer rest
  where
    (num, rest) = span isDigit cs
--}
}