module CSPM.Syntax where

import Data.Char
import qualified Data.Set as Set

type Programm = [Construct]

data Construct
  = TypeVar String
  | NamedType String TBody
  | Assert (Set.Set String) String PType
  | NamedProc String [String] Proc
  deriving (Show)

data Proc
  = STOP
  | SKIP
  | CallProc String [String]
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
  deriving (Show)

-- The Type Construction Body
type TBody = [[String]]

-- If the Phi type is Nothing, it should be inferred.
type PhiT = Maybe String

data PType
  = PType String PhiT
  deriving (Show)

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

data TokenClass
  = TokenSkip
  | TokenStop
  | TokenVar String
  | TokenName String
  | TokenNum Int
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
  | TokenVDash
  | TokenAssert
  | TokenTypeVar
  | TokenDataType
  | TokenProc
  | TokenEOF
  deriving (Show)