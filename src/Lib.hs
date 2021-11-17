{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

-- {-# LANGUAGE LambdaCase #-}

module Lib where

import CSPM.Parser
import CSPM.Syntax (Action (..), ActionI (..), Construct (..), Exp (..), Literal (LBool, LInt, LVar), Proc (..), Programm, Type (..))
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
import Data.Bifunctor (second)
-- import qualified Data.HashMap.Lazy as Map

import Data.Map ((!?))
import qualified Data.Map as Map
import Data.Tuple.Extra (both)
import Debug.Trace (trace)
import Text.Show (Show)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data TypeError
  = TypeMismatch Type Type
  | NotFunction Type
  | NotInScope String
  | NotExpression String
  | NotChannel String Type
  deriving (Show, Eq)

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

data Env = Env
  { typeEnv :: Map.Map String Type,
    procEnv :: Map.Map String Proc
  }

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> Env {typeEnv = Map.insert n t (typeEnv env)})

addToEnv' :: [(String, Type)] -> Check a -> Check a
addToEnv' xs = local (\env -> Env {typeEnv = Map.fromList xs `Map.union` typeEnv env})

-- Return a tuple of (var, type) pairs, fst -> Outputs, snd -> new Variables
findTypesOfChannel :: Action -> Type -> Check ([(Exp, Type)], [(String, Type)])
findTypesOfChannel (chan, items) t@(TSum sum) =
  case lookup chan sum of
    Nothing -> throwError $ NotChannel chan t
    Just t -> matchItems t items
  where
    matchItems :: Type -> [ActionI] -> Check ([(Exp, Type)], [(String, Type)])
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
    let pEnv = procEnv env
    let tEnv = typeEnv env
    case tEnv !? process of
      Just t -> return t
      Nothing -> case pEnv !? process of
        Nothing -> throwError $ NotInScope process
        Just pr -> addToEnv (process, TProc t) $ check pr t
  --
  Prefix action pr -> do
    (outputs, vars) <- findTypesOfChannel action t
    outputTypes <- mapM (uncurry checkExpHasType) outputs
    addToEnv' vars $ check pr t
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
    et <- checkExpHasType exp TBool
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
  Seq pr pr' -> do
    p1Type <- check pr t
    check pr' t
  Parallel set pr pr' -> undefined
  Hide set pr -> undefined
  ReplIntChoice s set pr -> undefined
  PCaseExpr exp cases -> undefined
  PLambda arg typ pr -> undefined
  Let var exp pr -> undefined

checkExpHasType :: Exp -> Type -> Check Type
checkExpHasType exp t = do
  inferredType <- checkExp exp
  if inferredType == t
    then return t
    else throwError $ TypeMismatch inferredType t

-- Check Expression for type
checkExp :: Exp -> Check Type
checkExp exp = case exp of
  Eq exp' exp2 -> do
    rhs <- checkExp exp'
    lhs <- checkExp exp2
    if rhs == lhs then return TBool else throwError $ TypeMismatch rhs lhs
  Lit s -> checkLit s
  App fun arg -> do
    tfun <- checkExp fun
    targ <- checkExp arg
    case tfun of
      TFun argT retT -> if argT == targ then return retT else throwError $ TypeMismatch argT targ
      _ -> throwError $ NotFunction tfun
  ELambda argname typename expr -> undefined --do
  --retT <- addToEnv (argname, typename) $ checkExp expr
  -- return TFun T Type
  ECaseExpr exp cases -> undefined
  Tuple exprs -> do
    typs <- mapM checkExp exprs
    return $ TProd typs

checkLit :: Literal -> Check Type
checkLit l = case l of
  LInt n -> return TNum
  LVar s -> do
    env <- ask
    case typeEnv env !? s of
      Nothing -> throwError $ NotInScope s
      Just nt -> return nt
  LBool b -> return TBool

tBool :: Type
tBool = TSum [("true", pEmpty), ("false", pEmpty)]

trivial :: Proc
trivial = ExtChoice (Ite (Eq (Lit $ LVar "s") (Lit $ LVar "s'")) (CallProc "P" []) STOP) (CallProc "Q" [])

withVarIte :: Proc
withVarIte = Ite (Lit $ LVar "y") SKIP STOP

withPrefix :: Proc
withPrefix = Prefix ("in", [Input "x", Input "y"]) $ Prefix ("out", [Output $ Eq (Lit $ LVar "x") (Lit $ LVar "x")]) withVarIte

prefixT :: Type
prefixT = TSum [("in", TProd [tBool, TBool]), ("out", TBool)]

--trivEnv :: Env
--trivEnv = [("s", Left $ TVar "X"), ("s'", Left $ TVar "X"), ("P", Left (TProc tBool)), ("Q", Right (ExtChoice (CallProc "P" []) STOP))]

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Proc -> Type -> Either TypeError Type
checkTop env x t = runCheck env (check x t)