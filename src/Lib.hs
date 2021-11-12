{-# LANGUAGE TupleSections #-}

module Lib where

import CSPM.Parser
import CSPM.Syntax (Action (..), ActionI (..), Construct (..), Exp (Brack, Dot, Eq, Var), Proc (..), Programm)
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
import Data.Bifoldable
import qualified Data.HashMap.Lazy as Map
import Data.Tuple.Extra (both)
import Debug.Trace (trace)
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
  | NotChannel String Type
  deriving (Show)

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

tBool :: Type
tBool = TSum [("true", pEmpty), ("false", pEmpty)]

type CanBeEvaluated = Either Type Proc

type Env = [(String, CanBeEvaluated)]

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> (n, Left t) : env)

-- Return a tuple of (var, type) pairs, fst -> Outputs, snd -> new Variables
findTypesOfChannel :: Action -> Type -> Check ([(String, Type)], [(String, Type)])
findTypesOfChannel (chan, items) t@(TSum sum) =
  case lookup chan sum of
    Nothing -> throwError $ NotChannel chan t
    Just t -> matchItems t items
  where
    matchItems :: Type -> [ActionI] -> Check ([(String, Type)], [(String, Type)])
    matchItems t@(TProd typs) actions =
      if length typs /= length actions
        then throwError $ NotChannel ("The number of Arguments is different" ++ show actions) t
        else return (foldl (flip (flip addT . bifoldMap (,[]) ([],))) ([], []) (zipWith extractNames actions typs))
    matchItems t [a] = case a of
      Output s -> return ([(s, t)], [])
      Input s -> return ([], [(s, t)])
      Selection s -> return ([], [(s, t)])
    matchItems _ _ = undefined
    extractNames (Input x) t = Right [(x, t)]
    extractNames (Output x) t = Left [(x, t)]
    extractNames (Selection x) t = Right [(x, t)]
findTypesOfChannel (chan, _) t = throwError $ NotChannel chan t

addT :: (Monoid m, Monoid n) => (m, n) -> (m, n) -> (m, n)
addT (a, x) (b, y) = (a <> b, x <> y)

-- Test if a type satisfies the communication property
satTcomm :: Type -> Bool
satTcomm typ = case typ of
  TProc ty -> False
  TFun ty ty' -> False
  TInd s ty -> satTcomm ty
  TNum -> True
  TBool -> True
  TSum sums -> all (satTcomm . snd) sums
  TProd tys -> all satTcomm tys
  TVar s -> True

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
  Prefix action pr -> do
    (outputs, vars) <- findTypesOfChannel action t

    return $ trace ("Vars: " ++ show vars) $ TProc t
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

withPrefix :: Proc
withPrefix = Prefix ("in", [Input "x", Input "y"]) SKIP

prefixT :: Type
prefixT = TSum [("in", TProd [tBool, tBool]), ("out", tBool)]

trivEnv :: Env
trivEnv = [("s", Left $ TVar "X"), ("s'", Left $ TVar "X"), ("P", Left (TProc tBool)), ("Q", Right (ExtChoice (CallProc "P" []) STOP))]

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Proc -> Type -> Either TypeError Type
checkTop env x t = runCheck env (check x t)