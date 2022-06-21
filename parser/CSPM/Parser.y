{
{-# OPTIONS -w #-}
module CSPM.Parser (parse, parseFile) where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Char
import CSPM.Syntax
import CSPM.Lexer
import Data.Maybe
import Debug.Trace (traceShow)
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
      case            { Token _ TokenCase }
      of              { Token _ TokenOf }
      let             { Token _ TokenLet }
      rec             { Token _ TokenRec }
      fold            { Token _ TokenFold }
      within          { Token _ TokenIn }
      true            { Token _ TokenTrue }
      false           { Token _ TokenFalse }
      pr              { Token _ TokenProject}
      '='             { Token _ TokenEq }
      '=='            { Token _ TokenEquals }
      '!='            { Token _ TokenNotEquals }
      and             { Token _ TokenAnd }
      or              { Token _ TokenOr }
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
      '|||'           { Token _ TokenInterleave }
      '@'             { Token _ TokenAmpersat }
      '&'             { Token _ TokenAmpersand }
      ':'             { Token _ TokenColon }
      '::'            { Token _ TokenDoubleColon }
      '?'             { Token _ TokenQm }
      '!'             { Token _ TokenExcl }
      '$'             { Token _ TokenDollar }
      ','             { Token _ TokenComma }
      '_'             { Token _ TokenHole }
      '|-'            { Token _ TokenVDash }
      assert          { Token _ TokenAssert }
      typevar         { Token _ TokenTypeVar }
      datatype        { Token _ TokenDataType }
      Proc            { Token _ TokenProc }

%nonassoc let if '|' var '::' fold
%right ARROWTYPE
%right '->'
%left '\\'
%left '|~|'
%left '[]'
%left ';'
-- %right '->'
%right PREFIX
%left '!' '?' '$'
%right '.'
%nonassoc '==' '!='
%left and or 
%left '+' '-'
%left  '*' '/'
%left '(' ')'
%left APP
%left DOTEXPR
%%

Programm :: { Programm }
Programm : RProgramm { reverse $1 }

RProgramm :: { Programm }
RProgramm : RProgramm Construct {$2 : $1}
      | Construct    {[$1]}
      | {- empty -}     {[]}

Construct :: { Construct }
Construct   : Typedecl    {$1}
            | Assertion   {$1}
            | P_Assign    {$1}
            | ExprDecl ';'{$1}

Typedecl :: { Construct }
Typedecl    : typevar name { TypeVar $2 }
            | datatype name '=' TypeBody { NamedType $2 $4 }

TypeBody :: { Type }
TypeBody    : T_Product    { TProd $1 }
            | T_Sum        { TSum $ reverse $1}
            | '\\' name '->' TypeBody { TInd $2 $4 }
            | TypeBody '->' TypeBody %prec ARROWTYPE { TFun $1 $3}
            | name         { TVar $1 }
            | '(' TypeBody ')' {$2}


T_Sum :: { [SumT Type] } 
T_Sum : var '.' TypeBody            { [($1, $3)] }
      | T_Sum '|' var '.' TypeBody  { ($3, $5):$1 }
      | var                         { [($1, TProd [])]}               

T_Product   :: { [Type] }
T_Product   :  TypeBody '.' T_Product {$1:$3}
            | TypeBody '.' TypeBody  { [$1, $3]}
            | {- empty -}            { [] }
            | '(' ')'                { [] }

Assertion :: { Construct }
Assertion   : assert ConstSet '|-' name ':' P_Type {Assert $2 $4 $6}

ConstSet    :: { Map.Map String Type }
            : '{' ConstSeq '}' { Map.fromList $2 }

ConstSeq    :: {[(String, Type)]}
            : ConstSeq ',' var ':' TypeBody     {($3, $5):$1}
            |  var ':' TypeBody                 {[($1, $3)]}
            | {- empty -}                       {[]}

ExprDecl :: { Construct }
ExprDecl : var '=' Exp { NamedExpr $1 $3 }
ExprDecl : rec var '::' TypeBody '=' Exp { NamedRecExpr $2 $4 $6 }

P_Type :: { PType }
P_Type      : Proc '(' name ')' { PType $3 Nothing }

P_Assign :: { Construct }
P_Assign    : name '=' PProc               {NamedProc $1 [] $3}
            | name '(' ArgSeq ')' '=' PProc   {NamedProc $1 (reverse $3) $6}

PProc :: {Proc}
      : STOP                            { STOP  }
      | SKIP                            { SKIP }
      | name                            { CallProc $1 [] }
      | name '(' Seq ')'                { CallProc $1 (reverse $3)}
      | Action '->' PProc %prec PREFIX  { Prefix $1 $3 }
      | PProc '[]' PProc                { ExtChoice $1 $3 }
      | PProc '|~|' PProc               { IntChoice $1 $3 }
      | if Exp then PProc else PProc    { Ite $2 $4 $6 }
      | Exp '&' PProc                   { Ite $1 $3 STOP } 
      | PProc ';' PProc                 { Seq $1 $3 }
      | PProc '[|' Set '|]' PProc       { Parallel $3 $1 $5 }
      | PProc '|||' PProc               { Parallel Set.empty $1 $3}
      | PProc '\\' Set                  { Hide $3 $1 }
      | '|~|' var ':' TypeBody '@' PProc     { ReplIntChoice $2 $4 $6 }
      | '(' PProc ')'                   { $2 }
      | let var '=' Exp within PProc        { Let $2 $4 $6 }
      | case Exp PCases                 { PCaseExpr $2 $3 }
      | '\\' Vars ':' TypeBody '@' PProc { PLambda (reverse $2) $4 $6 }

PCases :: { [PCase] }
      : PCases of var '->' PProc       { (PCase $3 $5) : $1 }
      | of var '->' PProc              { [PCase $2 $4] }

Vars :: {[String]}
      : var {[$1]}
      | Vars var {$2:$1}
      | {-empty-} {[]}

Set  ::  { Set.Set SElem }
Set   : '{' SetCont '}' { Set.fromList $2 }

SetCont ::  { [SElem] }
    : SExp   {[$1]}
    | SetCont ',' SExp {$3 : $1}
    | {-empty-} {[]} 


{-
Type : name 

VarDecls : VarDecl
         | VarDecls ',' VarDecl

VarDecl : var '<-' Type -}

ArgSeq :: { [(String, Type)] }
ArgSeq : ArgSeq ',' var ':' TypeBody    { ($3, $5) : $1 }
       | var ':' TypeBody               { [($1, $3)] }

Seq :: { [String] }
Seq : Seq ',' var    { $3 : $1 }
      | {- empty -}  { [] }
      | var          { [$1] }


Action :: { Action } 
        : var ActionS { ($1, reverse $2) }

ActionS :: { [ActionI] }
       : ActionS '?' var       { Input $3 : $1 }
       | ActionS '!' Exp       { Output $3 : $1 }
       | ActionS '$' var       { Selection $3 : $1 }
       | {- empty -}           { [] }

{- id.a.b -> TSum "id" -}
Exp :: {TExp}
Exp   : -- '(' RawExp ')' {TExp $2 Nothing}
      -- | '(' RawExp ')' '::' TypeBody {TExp $2 (Just $5)}
       RawExp {TExp $1 Nothing}
      | RawExp '::' TypeBody {TExp $1 (Just $3)}

RawExp :: {Exp}
RawExp : Exp '==' Exp                { Eq $1 $3 }
      | let var '=' Exp within Exp  { LetExp $2 $4 $6 }
      | let rec var '::' TypeBody '=' Exp within Exp { LetRecExp $3 $5 $7 $9 }
      | if Exp then Exp else Exp    { IteExp $2 $4 $6 }
      | '(' ExpSeq ')'              { Tuple $ reverse $2 }
      | '(' RawExp ')'              { $2 }
      | '(' ')'                     { Tuple [] }
      | Exp Exp %prec APP           { App $1 $2 }
      | Lit                         { Lit $1 }
      | '\\' var ':' TypeBody '->' Exp  { ELambda $2 $4 $6 }
      | case Exp Cases              { ECaseExpr $2 $3 }
      | var '.' Exp %prec DOTEXPR   { Sum $1 $3 }
      | fold Exp Exp                { Fold $2 $3 }
      | Exp '+' Exp                 { MathOp [$1, $3] }
      | Exp '-' Exp                 { MathOp [$1, $3] }
      | Exp '*' Exp                 { MathOp [$1, $3] }
      | Exp '/' Exp                 { MathOp [$1, $3] }
      | Exp '!=' Exp                { Eq $1 $3 }
      | Exp and Exp               { IteExp $1 $3 (TExp (Lit (LBool False)) (Just TBool))}
      | Exp or Exp               { IteExp $1 (TExp (Lit (LBool True)) (Just TBool)) $3}
      | pr number Exp               { Project $2 $3 }

SExp :: {SElem}
SExp  : RawSExp {TExp $1 Nothing}
      | RawSExp '::' TypeBody {TExp $1 (Just $3)}

RawSExp :: { Exp'' SLiteral Type}
RawSExp   : SExp '==' SExp             { Eq $1 $3 }
      | SLit                        { Lit $1 }
      | '(' RawSExp ')'                 { $2 }
      | SExp SExp %prec APP           { App $1 $2 }
      | '\\' var ':' TypeBody '->' SExp  { ELambda $2 $4 $6 }
      | case SExp SCases              { ECaseExpr $2 $3 }
      | '(' SExpSeq ')'               { Tuple $ reverse $2 }
      | '(' ')'                       { Tuple [] }
      | var '.' SExp  %prec DOTEXPR   { Sum $1 $3 }
      | fold SExp SExp                { Fold $2 $3 }
      | SExp '+' SExp                 { MathOp [$1, $3] }
      | SExp '-' SExp                 { MathOp [$1, $3] }
      | SExp '*' SExp                 { MathOp [$1, $3] }
      | SExp '/' SExp                 { MathOp [$1, $3] }
      | SExp '!=' SExp                { Eq $1 $3 }

SExpSeq : SExpSeq ',' SExp  { $3 : $1 }
       | SExp ',' SExp     { [$3, $1]} 
       | {[]}

SCases :: { [SCase] }
      : SCases of cvar '->' SExp       { (ECase $3 $5) : $1 }
      | of cvar '->' SExp             { [ECase $2 $4] }


Lit   :: { Literal }
      : number          { LInt $1 }
      | var             { LVar $1 }
      | true            { LBool True }
      | false           { LBool False }

SLit :: { SLiteral }
      : '*' '{' TypeBody '}'  {LStar $3}
      | Lit {LLit $1}

ExpSeq : ExpSeq ',' Exp  { $3 : $1 }
       | Exp ',' Exp     { [$3, $1]} 


cvar :: {Maybe String} 
      : var {Just $1}
      | '_' {Nothing}

Cases :: { [ECase] }
      : Cases of cvar '->'   Exp      { (ECase $3 $5) : $1 }
      | of cvar '->'  Exp          { [ECase $2 $4] }

{
lexwrap :: (Token -> Alex a) -> Alex a
lexwrap = (alexMonadScan' >>=)

happyError :: Token -> Alex a
happyError (Token p t) =
  alexError' p ("parse error at token '" ++ unLex t ++ "'")

parseFile :: FilePath -> String -> Either String Programm
parseFile = runAlex' parse
}