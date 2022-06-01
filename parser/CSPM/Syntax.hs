{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module CSPM.Syntax where

import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (second)
import Data.Char
import Data.Foldable (foldl')
import Data.Foldable.Extra (Foldable)
import Data.Functor (Functor)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

type Programm = [Construct]

type ArgName = String

data Construct
  = TypeVar String
  | NamedType String Type
  | NamedExpr String TExp
  | NamedRecExpr String Type TExp
   -- | TypeAnnotation String Type
  |  Assert (Map.Map String Type) String PType
  | NamedProc String [(ArgName, Type)] Proc
  deriving (Show)

type Proc = Proc' Type

type TExp = TExp'' Literal Type

type TExp' = TExp'' Literal

type Exp = Exp'' Literal Type

type Exp' = Exp'' Literal

type SElem = TExp'' SLiteral Type

data Proc' a
  = STOP
  | SKIP
  | CallProc String [String]
  | Prefix (Action' a) (Proc' a)
  | ExtChoice (Proc' a) (Proc' a)
  | IntChoice (Proc' a) (Proc' a)
  | Ite (TExp' a) (Proc' a) (Proc' a)
  | Seq (Proc' a) (Proc' a)
  | Parallel (Set.Set SElem) (Proc' a) (Proc' a)
  | Hide (Set.Set SElem) (Proc' a)
  | Let String (TExp' a) (Proc' a)
  | PCaseExpr (TExp' a) [PCase' a]
  | PLambda [ArgName] a (Proc' a)
  | ReplIntChoice String Type (Proc' a)
  deriving (Show, Functor, Foldable)

-- If the Phi type is Nothing, it should be inferred.
type PhiT = Maybe String

data PType
  = PType String PhiT
  deriving (Show)

data TExp'' l a
 = TExp (Exp'' l a) (Maybe a)
 deriving(Show, Functor, Foldable, Eq, Ord)

data Exp'' l a
  = Eq (TExp'' l a) (TExp'' l a)
  | App (TExp'' l a) (TExp'' l a)
  | ELambda ArgName a (TExp'' l a)
  | ECaseExpr (TExp'' l a) [ECase' l a]
  | Lit l
  | Tuple [TExp'' l a]
  | Sum String (TExp'' l a)
  | Fold (TExp'' l a) (TExp'' l a)
  | MathOp [TExp'' l a]
  | Project Int (TExp'' l a)
  | LetExp ArgName (TExp'' l a) (TExp'' l a)
  | LetRecExp ArgName a (TExp'' l a) (TExp'' l a)
  | IteExp (TExp'' l a) (TExp'' l a) (TExp'' l a)
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

data ECase' l a = ECase String (TExp'' l a)
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
  | Output (TExp' a)
  | Selection String
  deriving (Show, Functor, Foldable)

type Action = Action' Type

type Action' a = (String, [ActionI' a])

type SumT a = (String, a)

type Type = Type' String

data Type' a
  = TProc (Type' a)
  | TFun (Type' a) (Type' a)
  | TInd a (Type' a)
  | TNum
  | TBool
  | TSum [SumT (Type' a)]
  | TProd [Type' a]
  | TVar a
  deriving (Ord, Functor)

instance Eq a => Eq (Type' a) where
  (TProc lhs) == (TProc rhs) = lhs == rhs
  (TFun lhsa lhsi) == (TFun rhsa rhsi) = lhsa == rhsa && lhsi == rhsi
  (TInd ls lhs) == (TInd rs rhs) = ls == rs && lhs == rhs
  TNum == TNum = True
  TBool == TBool = True
  (TVar s) == (TVar r) = s == r
  (TProd lts) == (TProd rts) = and $ zipWith (==) lts rts
  (TSum lts) == (TSum rts) = and $ zipWith (\(c1, t1) (c2, t2) -> c1 == c2 && t1 == t2) lts rts
  _ == _ = False

instance Show a => Show (Type' a) where
  show ty = case ty of
    TProc ty' -> "Proc(" ++ show ty' ++ ")"
    TFun ty' ty2 -> show ty' ++ " -> " ++ show ty2
    TInd s ty' -> "\\" ++ show s ++ " -> " ++ show ty'
    TNum -> "Int"
    TBool -> "Bool"
    TSum [] -> "{}"
    TSum ((ch0, ty0) : xs) -> "{" ++ foldl' (\acc (ch, ty) -> acc ++ " | " ++ ch ++ "." ++ show ty) (ch0 ++ "." ++ show ty0) xs ++ "}"
    TProd [] -> "()"
    TProd (x : xs) -> "(" ++ foldl' (\acc ty -> acc ++ "." ++ show ty) (show x) xs ++ ")"
    TVar s -> show s

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
  | TokenRec
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
  | TokenAmpersand
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
  | TokenDoubleColon
  deriving (Show)
