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
  | Let String Exp Proc
  | PCaseExpr Exp [PCase]
  | PLambda ArgName Type Proc
  | ReplIntChoice String (Set.Set String) Proc
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
  | App Exp Exp
  | ELambda ArgName Type Exp
  | ECaseExpr Exp [ECase]
  | Lit Literal
  | Tuple [Exp]
  | Sum String Exp
  | Fold Exp Exp
  | MathOp [Exp]
  deriving (Show)

data Literal
  = LInt Int
  | LVar String
  | LBool Bool
  deriving (Show)

data ECase = ECase String Exp
  deriving (Show)

data PCase = PCase String Proc
  deriving (Show)

data Pattern
  = PVar String
  | PDot Pattern Pattern

data ActionI
  = Input String
  | Output Exp
  | Selection String
  deriving (Show)

type Action = (String, [ActionI])

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

mapVar :: (String -> Type) -> Type -> Type
mapVar f ty = case ty of
  TProc ty' -> TProc $ mapVar f ty'
  TFun ty' ty_a -> TFun (mapVar f ty') (mapVar f ty_a)
  TInd a ty' -> TInd a (mapVar f ty')
  TNum -> TNum
  TBool -> TBool
  TSum x0 -> TSum $ second (mapVar f) <$> x0
  TProd tys -> TProd $ mapVar f <$> tys
  TVar a -> f a

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

-- Insert a type on Place of every Type variable
(</) :: Type -> String -> Type -> Type
t </ var = \t' -> mapVar (\s -> if s == var then t' else TVar s) t