{
{-# OPTIONS -w #-}
module Parser.CSP (parse, parseFile) where

import qualified Data.Set as Set
import Data.Char
import ParserUtil
import Lexer
}


%name parse
%tokentype { Token }
%error { happyError }

%monad { Alex }
%lexer { lexwrap } { Token _ TokenEOF }

%token 
      STOP            { Token _ TokenStop }
      SKIP            { Token _ TokenSkip }
      var             { Token _ (TokenVar $$) }
      name            { Token _ (TokenName $$) }
      number          { Token _ (TokenNum $$) }  
      if              { Token _ TokenIf }
      then            { Token _ TokenThen }
      else            { Token _ TokenElse }
      '='             { Token _ TokenEq }
      '=='            { Token _ TokenEquals }
      '!='            { Token _ TokenNotEquals }
      '+'             { Token _ TokenPlus }
      '-'             { Token _ TokenMinus }
      '*'             { Token _ TokenTimes }
      '/'             { Token _ TokenDiv }
      '('             { Token _ TokenOB }
      ')'             { Token _ TokenCB }
      '{'             { Token _ TokenOCB }
      '}'             { Token _ TokenCCB }
      '\\'            { Token _ TokenSlash }
      '|'             { Token _ TokenBar }
      '.'             { Token _ TokenDot }
      ';'             { Token _ TokenSemicolon }
      '[]'            { Token _ TokenBox }
      '|~|'           { Token _ TokenInt }
      '->'            { Token _ TokenPrefix }
      '<-'            { Token _ TokenAssign }
      '[|'            { Token _ TokenParOpen }
      '|]'            { Token _ TokenParClose }
      '@'             { Token _ TokenAmpersat }
      ':'             { Token _ TokenColon }
      '?'             { Token _ TokenQm }
      '!'             { Token _ TokenExcl }
      '$'             { Token _ TokenDollar }
      ','             { Token _ TokenComma }
      '|-'            { Token _ TokenVDash }
      assert          { Token _ TokenAssert }
      typevar         { Token _ TokenTypeVar }
      datatype        { Token _ TokenDataType }
      Proc            { Token _ TokenProc }

%nonassoc '=='
%right '.'
%left '!' '?' '$'
%right '->'
%left ';'
%left '[]'
%left '|~|'
%left '\\'

%%

Programm :: { Programm }
Programm : RProgramm { reverse $1 }

RProgramm :: { Programm }
RProgramm : RProgramm Construct {$2 : $1}
      | Construct       {[$1]}
      | {- empty -}     {[]}

Construct :: { Construct }
Construct   : Typedecl    {$1}
            | Assertion   {$1}
            | P_Assign    {$1}

Typedecl :: { Construct }
Typedecl    : typevar name { TypeVar $2 }
            | datatype name '=' TypeBody { NamedType $2 $4 }

TypeBody :: { TBody }
TypeBody    : T_Product {[$1]}
            | TypeBody '|' T_Product {$3 : $1}

T_Product   : T_Product_R {reverse $1}

T_Product_R   : var       {[$1]}
            | T_Product '.' name {$3 : $1}

Assertion :: { Construct }
Assertion   : assert Set '|-' name ':' P_Type {Assert $2 $4 $6}

P_Type :: { PType }
P_Type      : Proc '(' name ')' { PType $3 Nothing }

P_Assign :: { Construct }
P_Assign    : name '=' PProc               {NamedProc $1 [] $3}
            | name '(' Seq ')' '=' PProc   {NamedProc $1 (reverse $3) $6}

PProc :: {Proc}
PProc  : STOP                        { STOP }
      | SKIP                        { SKIP }
      | name                        { CallProc $1 [] }
      | name '(' Seq ')'            { CallProc $1 (reverse $3)}
      | Action '->' PProc            { Prefix $1 $3 }
      | PProc '[]' PProc              { ExtChoice $1 $3 }
      | PProc '|~|' PProc             { IntChoice $1 $3 }
      | if Exp then PProc else PProc  { Ite $2 $4 $6 }
      | PProc ';' PProc               { Seq $1 $3 }
      | PProc '[|' Set '|]' PProc     { Parallel $3 $1 $5 }
      | PProc '\\' Set               { Hide $3 $1 }
      | '|~|' var ':' Set '@' PProc  { ReplIntChoice $2 $4 $6 }
      | '(' PProc ')'                { $2 }

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
lexwrap :: (Token -> Alex a) -> Alex a
lexwrap = (alexMonadScan' >>=)

happyError :: Token -> Alex a
happyError (Token p t) =
  alexError' p ("parse error at token '" ++ unLex t ++ "'")

parseFile :: FilePath -> String -> Either String Programm
parseFile = runAlex' parse
}