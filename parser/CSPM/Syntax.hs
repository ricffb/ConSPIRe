{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module CSPM.Syntax where

import Data.Bifunctor (second)
import Data.Char
import Data.Foldable.Extra (Foldable)
import Data.Functor (Functor)
import qualified Data.Set as Set

type Programm = [Construct]

type ArgName = String

type TypeName = String

data Construct
  = TypeVar String
  | NamedType String Type
  | NamedExpr String Exp
  | TypeAnnotation String Type
  | Assert (Set.Set String) String PType
  | NamedProc String [(ArgName, TypeName)] Proc
  deriving (Show)

type Proc = Proc' Type

type Exp = Exp' Type

data Proc' a
  = STOP
  | SKIP
  | CallProc String [String]
  | Prefix (Action' a) (Proc' a)
  | ExtChoice (Proc' a) (Proc' a)
  | IntChoice (Proc' a) (Proc' a)
  | Ite (Exp' a) (Proc' a) (Proc' a)
  | Seq (Proc' a) (Proc' a)
  | Parallel (Set.Set String) (Proc' a) (Proc' a)
  | Hide (Set.Set String) (Proc' a)
  | Let String (Exp' a) (Proc' a)
  | PCaseExpr (Exp' a) [PCase' a]
  | PLambda ArgName a (Proc' a)
  | ReplIntChoice String (Set.Set String) (Proc' a)
  deriving (Show, Functor, Foldable)

-- If the Phi type is Nothing, it should be inferred.
type PhiT = Maybe String

data PType
  = PType String PhiT
  deriving (Show)

data Exp' a
  = Eq (Exp' a) (Exp' a)
  | App (Exp' a) (Exp' a)
  | ELambda ArgName a (Exp' a)
  | ECaseExpr (Exp' a) [ECase' a]
  | Lit Literal
  | Tuple [Exp' a]
  | Sum String (Exp' a)
  | Fold (Exp' a) (Exp' a)
  | MathOp [Exp' a]
  deriving (Show, Functor, Foldable)

data Literal
  = LInt Int
  | LVar String
  | LBool Bool
  deriving (Show)

type ECase = ECase' Type

data ECase' a = ECase String (Exp' a)
  deriving (Show, Functor, Foldable)

type PCase = PCase' Type

data PCase' a = PCase String (Proc' a)
  deriving (Show, Functor, Foldable)

data Pattern
  = PVar String
  | PDot Pattern Pattern

type ActionI = ActionI' Type

data ActionI' a
  = Input String
  | Output (Exp' a)
  | Selection String
  deriving (Show, Functor, Foldable)

type Action = Action' Type

type Action' a = (String, [ActionI' a])

type SumT a = (String, a)

data Type
  = TProc Type
  | TFun Type Type
  | TInd String Type
  | TNum
  | TBool
  | TSum [SumT Type]
  | TProd [Type]
  | TVar String
  deriving (Show, Eq)

data TokenClass
  = TokenSkip
  | TokenStop
  | TokenVar String
  | TokenName String
  | TokenNum Int
  | TokenIf
  | TokenThen
  | TokenElse
  | TokenCase
  | TokenOf
  | TokenLet
  | TokenIn
  | TokenTrue
  | TokenFalse
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
  | TokenFold
  deriving (Show)
