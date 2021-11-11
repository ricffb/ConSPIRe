module Lib where

import CSPM.Parser
import CSPM.Syntax (Construct (..), Proc (..), Programm)
import Control.Monad.Except
import Control.Monad.Reader
import Text.Show (Show)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

type SumT a = (String, a)

data Type
  = TProc Type
  | TFun Type Type
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
  deriving (Show)

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

tBool :: Type
tBool = TSum [("true", pEmpty), ("false", sEmpty)]

type Env = [(String, Type)]

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> (n, t) : env)

check :: Proc -> Type -> Check Type
check p t = case p of
  STOP -> return $ TProc t
  SKIP -> return $ TProc t
  CallProc process args -> do
    env <- ask
    case lookup process env of
      Just t -> return t
      Nothing -> throwError $ NotInScope process
  Prefix action pr -> undefined
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
  IntChoice pr pr' -> undefined
  Ite exp pr pr' -> undefined
  Seq pr pr' -> undefined
  Parallel set pr pr' -> undefined
  Hide set pr -> undefined
  ReplIntChoice s set pr -> undefined

trivial :: Proc
trivial = ExtChoice SKIP STOP

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Proc -> Type -> Either TypeError Type
checkTop env x t = runCheck env (check x t)