{

{-# OPTIONS -w  #-}
module Lexer
  ( Token(..)
  , AlexPosn(..)
  , unLex
  , Alex(..)
  , runAlex'
  , runAlex
  , alexMonadScan'
  , alexError'
  ) where

import Prelude hiding (lex)
import Control.Monad ( liftM )
import ParserUtil

}

%wrapper "monadUserState"

$digit = 0-9
$alpha = [A-Za-z]
$validident = [$alpha $digit \_ \']
@var = [a-z] $validident*
@name = [A-Z] $validident*

tokens :-
  $white+                               ;
  "--".*                                ;
  STOP                               { lex' TokenStop         }
  SKIP                                { lex' TokenSkip          }
  if                                  { lex' TokenIf }
  then                                { lex' TokenThen }
  else                                { lex' TokenElse }
  assert                              { lex' TokenAssert }
  typevar                             { lex' TokenTypeVar }
  datatype                            { lex' TokenDataType }
  Proc                                { lex' TokenProc }´
  $digit+                               { lex (TokenNum . read) }  
  @var                                  { lex  TokenVar }
  @name                                 { lex  TokenName }
  \{                                    { lex' TokenOCB }
  \}                                    { lex' TokenCCB }
  \\                                    { lex' TokenSlash }
  \|                                    { lex' TokenBar }
  \.                                    { lex' TokenDot }
  \=                                    { lex' TokenEq          }
  \+                                    { lex' TokenPlus        }
  \-                                    { lex' TokenMinus       }
  \*                                    { lex' TokenTimes       }
  \/                                    { lex' TokenDiv         }
  \(                                    { lex' TokenOB      }
  \)                                    { lex' TokenCB      }
  \;                                    { lex' TokenSemicolon }
  \@                                    { lex' TokenAmpersat }
  \:                                    { lex' TokenColon }
  \?                                    { lex' TokenQm }
  \!                                    { lex' TokenExcl }
  \$                                    { lex' TokenDollar }
  \,                                    { lex' TokenComma }
  "=="                                  { lex' TokenEquals }
  "!="                                  { lex' TokenNotEquals }
  "[]"                                  { lex' TokenBox }
  "|~|"                                 { lex' TokenInt }
  "->"                                  { lex' TokenPrefix }
  "<-"                                  { lex' TokenAssign }
  "[|"                                  { lex' TokenParOpen }
  "|]"                                  { lex' TokenParClose }
  "|-"                                  { lex' TokenVDash }

  
{
-- To improve error messages, We keep the path of the file we are
-- lexing in our own state.
data AlexUserState = AlexUserState { filePath :: FilePath }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "<unknown>"

getFilePath :: Alex FilePath
getFilePath = liftM filePath alexGetUserState

setFilePath :: FilePath -> Alex ()
setFilePath = alexSetUserState . AlexUserState

-- The token type, consisting of the source code position and a token class.
data Token = Token AlexPosn TokenClass
  deriving ( Show )

-- For nice parser error messages.
unLex :: TokenClass -> String
unlex TokenStop = "STOP"      
unlex TokenSkip = "SKIP"       
unlex TokenIf = "if"
unlex TokenThen = "then"
unlex TokenElse = "else"
unlex TokenAssert = "assert"
unlex TokenTypeVar = "typevar"
unlex TokenDataType = "datatype"
unlex TokenProc = "Proc"
unlex TokenOCB = "{"
unlex TokenCCB = "}"
unlex TokenSlash = "\\"
unlex TokenBar = "|"   
unlex TokenOB = "("     
unlex TokenCB = ")"     
unlex TokenSemicolon = ";"
unlex TokenAmpersat = "@"
unlex TokenColon = ":"
unlex TokenQm = "?"
unlex TokenExcl = "!"
unlex TokenDollar = "$"
unlex TokenComma = ","
unlex TokenEquals = "=="
unlex TokenNotEquals = "!="
unlex TokenBox = "[]"
unlex TokenInt = "|~|"
unlex TokenPrefix = "->"
unlex TokenAssign = "<-"
unlex TokenParOpen = "[|"
unlex TokenParClose = "|]"
unlex TokenVDash = "|-"
unLex (TokenNum i) = show i
unLex (TokenVar s) = show s
unLex (TokenName s) = show s
unLex TokenEq = "="
unLex TokenPlus = "+"
unLex TokenMinus = "-"
unLex TokenTimes = "*"
unLex TokenDiv = "/"
unLex TokenEOF = "<EOF>"

alexEOF :: Alex Token
alexEOF = do
  (p,_,_,_) <- alexGetInput
  return $ Token p TokenEOF

-- Unfortunately, we have to extract the matching bit of string
-- ourselves...
lex :: (String -> TokenClass) -> AlexAction Token
lex f = \(p,_,_,s) i -> return $ Token p (f (take i s))

-- For constructing tokens that do not depend on
-- the input
lex' :: TokenClass -> AlexAction Token
lex' = lex . const

-- We rewrite alexMonadScan' to delegate to alexError' when lexing fails
-- (the default implementation just returns an error message).
alexMonadScan' :: Alex Token
alexMonadScan' = do
  inp <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError (p, _, _, s) ->
        alexError' p ("lexical error at character '" ++ take 1 s ++ "'")
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan'
    AlexToken inp' len action -> do
        alexSetInput inp'
        action (ignorePendingBytes inp) len

-- Signal an error, including a commonly accepted source code position.
alexError' :: AlexPosn -> String -> Alex a
alexError' (AlexPn _ l c) msg = do
  fp <- getFilePath
  alexError (fp ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ msg)

-- A variant of runAlex, keeping track of the path of the file we are lexing.
runAlex' :: Alex a -> FilePath -> String -> Either String a
runAlex' a fp input = runAlex input (setFilePath fp >> a)
}