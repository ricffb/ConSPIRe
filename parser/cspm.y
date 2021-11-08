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
      '|-'            { TokenVDash }
      assert          { TokenAssert }
      typevar         { TokenTypeVar }
      datatype        { TokenDataType }
      Proc            { TokenProc }

%nonassoc '=='
%right '.'
%left '!' '?' '$'
%right '->'
%left ';'
%left '[]'
%left '|~|'
%left '\\'

%%

parse : parse Construct {$2 : $1}
      | Construct       {[$1]}
      | {- empty -}     {[]}


Construct   : Typedecl    {$1}
            | Assertion   {$1}
            | P_Assign    {$1}

Typedecl    : typevar var { TypeVar $1 }
            | datatype name '=' TypeBody { NamedType $2 $4 }

TypeBody    : T_Product {[$1]}
            | TypeBody '|' T_Product {$3 : $1}

T_Product   : T_Product_R {reverse $1}

T_Product_R   : var       {[$1]}
            | T_Product '.' var {$3 : $1}

Assertion   : assert Set '|-' name ':' P_Type {Assert $2 $4 $6}

P_Type      : Proc '(' name ')' { PType $3 }

P_Assign    : name '=' Proc               {NamedProc $1 [] $3}
            | name '(' Seq ')' '=' Proc   {NamedProc $1 (reverse $3) $6}

Proc :: {Proc}
Proc  : STOP                        { STOP }
      | SKIP                        { SKIP }
      | name                        { CallProc $1 [] }
      | name '(' Seq ')'            { CallProc $1 (reverse $3)}
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