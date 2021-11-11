module Lib where

import CSPM.Parser
import CSPM.Syntax (Construct (..), Exp (Brack, Dot, Eq, Var), Proc (..), Programm)
import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.Reader
  ( MonadReader (ask, local),
    Reader,
    runReader,
  )
import Control.Monad.State (State)
import qualified Data.HashMap.Lazy as Map
import Text.Show (Show)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

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

data TypeError
  = TypeMismatch Type Type
  | NotFunction Type
  | NotInScope String
  | NotExpression String
  deriving (Show)

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

tBool :: Type
tBool = TSum [("true", pEmpty), ("false", sEmpty)]

type CanBeEvaluated = Either Type Proc

type Env = [(String, CanBeEvaluated)]

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> (n, Left t) : env)

check :: Proc -> Type -> Check Type
check p t = case p of
  STOP -> return $ TProc t
  --
  SKIP -> return $ TProc t
  --
  CallProc process args -> do
    env <- ask
    case lookup process env of
      Just (Left t) -> return t
      Just (Right p) -> addToEnv (process, TProc t) $ check p t
      Nothing -> throwError $ NotInScope process
  --
  Prefix action pr -> undefined
  --
  ExtChoice pleft pright -> do
    lhs <- check pleft t
    rhs <- check pright t
    case lhs of
      TProc ty
        | ty == t -> case rhs of
          TProc ty'
            | ty' == t -> return $ TProc t
          _ -> throwError $ TypeMismatch rhs (TProc t)
      _ -> throwError $ TypeMismatch lhs (TProc t)
  --
  IntChoice pleft pright -> do
    lhs <- check pleft t
    rhs <- check pright t
    case lhs of
      TProc ty
        | ty == t -> case rhs of
          TProc ty'
            | ty' == t -> return $ TProc t
          _ -> throwError $ TypeMismatch rhs (TProc t)
      _ -> throwError $ TypeMismatch lhs (TProc t)
  --
  Ite exp pleft pright -> do
    et <- checkExp exp
    lhs <- check pleft t
    rhs <- check pright t
    if et /= TBool
      then throwError $ TypeMismatch et TBool
      else case lhs of
        TProc ty
          | ty == t -> case rhs of
            TProc ty'
              | ty' == t -> return $ TProc t
            _ -> throwError $ TypeMismatch rhs (TProc t)
        _ -> throwError $ TypeMismatch lhs (TProc t)
  --
  Seq pr pr' -> undefined
  Parallel set pr pr' -> undefined
  Hide set pr -> undefined
  ReplIntChoice s set pr -> undefined

checkExp :: Exp -> Check Type
checkExp exp = case exp of
  Eq exp' exp2 -> do
    rhs <- checkExp exp'
    lhs <- checkExp exp2
    if rhs == lhs then return TBool else throwError $ TypeMismatch rhs lhs
  Dot exp' exp2 -> do
    rhs <- checkExp exp'
    lhs <- checkExp exp2
    return $ TProd [rhs, lhs]
  Var s -> do
    env <- ask
    case lookup s env of
      Nothing -> throwError $ NotInScope s
      Just (Right e) -> throwError $ NotExpression s
      Just (Left t) -> return t
  Brack exp' -> checkExp exp'

trivial :: Proc
trivial = ExtChoice (Ite (Eq (Var "s") (Var "s'")) (CallProc "P" []) STOP) (CallProc "Q" [])

trivEnv :: Env
trivEnv = [("s", Left $ TVar "X"), ("s'", Left $ TVar "X"), ("P", Left (TProc tBool)), ("Q", Right (ExtChoice (CallProc "P" []) STOP))]

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Proc -> Type -> Either TypeError Type
checkTop env x t = runCheck env (check x t)