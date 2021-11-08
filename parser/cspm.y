{
module Parser.CSP (parse) where

import qualified Data.Set as Set
import Data.Char
import ParserUtil
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

{-
Type : name 

VarDecls : VarDecl
         | VarDecls ',' VarDecl

VarDecl : var '<-' Type -}

Seq :: { [String] }
Seq : Seq ',' var    { $3 : $1 }
      | {- empty -}  { [] }
      | var          { [$1] }


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
happyError :: P a
happyError = \s i -> error (
	"Parse error in line " ++ show (i::Int) ++ "\n" ++ s)
}