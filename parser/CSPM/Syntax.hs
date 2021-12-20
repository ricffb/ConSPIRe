{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module CSPM.Syntax where

import Data.Bifunctor (second)
import Data.Char
import Data.Foldable.Extra (Foldable)
import Data.Functor (Functor)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Programm = [Construct]

type ArgName = String

data Construct
  = TypeVar String
  | NamedType String Type
  | NamedExpr String Exp
  | -- | TypeAnnotation String Type
    Assert (Map.Map String Type) String PType
  | NamedProc String [(ArgName, Type)] Proc
  deriving (Show)

type Proc = Proc' Type

type Exp = Exp'' Literal Type

type Exp' = Exp'' Literal

type SElem = Exp'' SLiteral Type

data Proc' a
  = STOP
  | SKIP
  | CallProc String [String]
  | Prefix (Action' a) (Proc' a)
  | ExtChoice (Proc' a) (Proc' a)
  | IntChoice (Proc' a) (Proc' a)
  | Ite (Exp' a) (Proc' a) (Proc' a)
  | Seq (Proc' a) (Proc' a)
  | Parallel (Set.Set SElem) (Proc' a) (Proc' a)
  | Hide (Set.Set SElem) (Proc' a)
  | Let String (Exp' a) (Proc' a)
  | PCaseExpr (Exp' a) [PCase' a]
  | PLambda [ArgName] a (Proc' a)
  | ReplIntChoice String Type (Proc' a)
  deriving (Show, Functor, Foldable)

-- If the Phi type is Nothing, it should be inferred.
type PhiT = Maybe String

data PType
  = PType String PhiT
  deriving (Show)

data Exp'' l a
  = Eq (Exp'' l a) (Exp'' l a)
  | App (Exp'' l a) (Exp'' l a)
  | ELambda ArgName a (Exp'' l a)
  | ECaseExpr (Exp'' l a) [ECase' l a]
  | Lit l
  | Tuple [Exp'' l a]
  | Sum String (Exp'' l a)
  | Fold (Exp'' l a) (Exp'' l a)
  | MathOp [Exp'' l a]
  | Project Int (Exp'' l a)
  deriving (Show, Functor, Foldable, Eq, Ord)

data Literal
  = LInt Int
  | LVar String
  | LBool Bool
  deriving (Show, Eq, Ord)

data SLiteral
  = LLit Literal
  | LStar Type
  deriving (Show, Eq, Ord)

type ECase = ECase' Literal Type

type SCase = ECase' SLiteral Type

data ECase' l a = ECase String (Exp'' l a)
  deriving (Show, Functor, Foldable, Eq, Ord)

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
  deriving (Show, Eq, Ord)

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
  | TokenProject
  deriving (Show)
