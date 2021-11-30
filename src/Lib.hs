{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Lib where

import CSPM.Parser
import CSPM.Syntax (Action, Action' (..), ActionI, ActionI' (..), Construct (..), ECase, ECase' (..), Exp, Exp' (..), Literal (LBool, LInt, LVar), Proc, Proc' (..), Programm, SumT, Type (..))
-- import qualified Data.HashMap.Lazy as Map

-- import qualified Data.HashMap.Lazy as Map
import Control.Monad (foldM, foldM_)
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
import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (Bifunctor, bimap, first, second)
import Data.Map ((!?))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple.Extra (both)
import Debug.Trace (trace, traceShow)
import Subsume (Subsume ((|<|)))
import Text.Show (Show)
import TypeLib (mapVar, resolve, (</))
import Utility (safeHead)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data TypeError
  = TypeMismatch Type Type
  | NotFunction Type
  | NotInScope String
  | NotExpression String
  | NotChannel String Type
  | NotSumType Type
  | NotInductive Type
  | EmptyCase
  deriving (Show, Eq)

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

data Env = Env
  { typeEnv :: Map.Map String Type,
    procEnv :: Map.Map String Proc,
    exprEnv :: Map.Map String Exp,
    alphabet :: Type
  }

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> env {typeEnv = Map.insert n t (typeEnv env)})

addToEnv' :: [(String, Type)] -> Check a -> Check a
addToEnv' xs = local (\env -> env {typeEnv = Map.fromList xs `Map.union` typeEnv env})

-- Return a tuple of (var, type) pairs, fst -> Outputs, snd -> new Variables
findTypesOfChannel :: Action -> Check ([(Exp, Type)], [(String, Type)])
findTypesOfChannel (chan, items) = do
  Env {alphabet} <- ask
  case alphabet of
    t@(TSum sum) -> case lookup chan sum of
      Nothing -> throwError $ NotChannel chan t
      Just t -> matchItems t items
    _ -> throwError $ NotChannel chan alphabet
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

check :: Proc -> Check Type
check p = case p of
  STOP -> do
    Env {alphabet} <- ask
    return $ TProc alphabet
  --
  SKIP -> do
    Env {alphabet} <- ask
    return $ TProc alphabet
  --
  CallProc process args -> do
    Env {alphabet, procEnv, typeEnv} <- ask
    case typeEnv !? process of
      Just t -> return t
      Nothing -> case procEnv !? process of
        Nothing -> throwError $ NotInScope process
        Just pr -> addToEnv (process, TProc alphabet) $ check pr
  --
  Prefix action pr -> do
    (outputs, vars) <- findTypesOfChannel action
    outputTypes <- mapM (uncurry checkExpHasType) outputs
    addToEnv' vars $ check pr
  --
  ExtChoice pleft pright -> do
    lhs <- check pleft
    rhs <- check pright
    Env {alphabet} <- ask
    case lhs of
      TProc ty
        | ty |<| alphabet -> case rhs of
          TProc ty'
            | ty' |<| alphabet -> return $ TProc alphabet
          _ -> throwError $ TypeMismatch rhs (TProc alphabet)
      _ -> throwError $ TypeMismatch lhs (TProc alphabet)
  --
  IntChoice pleft pright -> do
    lhs <- check pleft
    rhs <- check pright
    Env {alphabet} <- ask
    case lhs of
      TProc ty
        | ty |<| alphabet -> case rhs of
          TProc ty'
            | ty' |<| alphabet -> return $ TProc alphabet
          _ -> throwError $ TypeMismatch rhs (TProc alphabet)
      _ -> throwError $ TypeMismatch lhs (TProc alphabet)
  --
  Ite exp pleft pright -> do
    et <- checkExpHasType exp TBool
    lhs <- check pleft
    rhs <- check pright
    Env {alphabet} <- ask
    case lhs of
      TProc ty
        | ty |<| alphabet -> case rhs of
          TProc ty'
            | ty' |<| alphabet -> return $ TProc alphabet
          _ -> throwError $ TypeMismatch rhs (TProc alphabet)
      _ -> throwError $ TypeMismatch lhs (TProc alphabet)
  --
  Seq pr pr' -> do
    p1Type <- check pr
    check pr'
  Parallel set pr pr' -> undefined
  Hide set pr -> undefined
  ReplIntChoice s set pr -> undefined
  PCaseExpr exp cases -> undefined
  PLambda arg typ pr -> undefined
  Let var exp pr -> do
    expT <- checkExp exp
    addToEnv (var, expT) $ check pr

checkExpHasType :: Exp -> Type -> Check Type
checkExpHasType exp t = do
  inferredType <- checkExp exp
  if inferredType == t
    then return t
    else throwError $ TypeMismatch inferredType t

-- Check Expression for type
checkExp :: Exp -> Check Type
-- checkExp exp | traceShow exp False = undefined
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
      TFun argT retT -> if targ |<| argT then return retT else throwError $ TypeMismatch argT targ
      _ -> throwError $ NotFunction tfun
  ELambda argname t@(TVar typename) expr -> do
    env <- ask
    let tEnv = typeEnv env
    case Map.lookup typename tEnv of
      Nothing -> do
        retT <- addToEnv (argname, t) $ checkExp expr
        return $ TFun t retT
      Just ty -> do
        retT <- addToEnv (argname, ty) $ checkExp expr
        return $ TFun ty retT
  ELambda argname ty expr -> do
    retT <- addToEnv (argname, ty) $ checkExp expr
    return $ TFun ty retT
  ECaseExpr exp cases -> do
    expT <- checkExp exp
    checkECase expT cases
  Tuple exprs -> do
    typs <- mapM checkExp exprs
    return $ TProd typs
  Sum chan expr -> do
    exprT <- checkExp expr
    return $ TSum [(chan, exprT)]
  Fold ind fun -> do
    inferredT <- checkExp ind
    indT <- case inferredT of
      TVar s -> do
        Env {typeEnv} <- ask
        case typeEnv !? s of
          Just ty@(TInd _ _) -> return $ Just ty
          Just ty -> fitInductiveType ty
          Nothing -> throwError $ NotInScope s
      _ -> fitInductiveType inferredT
    case indT of
      Nothing -> throwError $ NotInductive inferredT
      Just (TInd var t) -> do
        funT <- checkExp fun
        case funT of
          TFun dom img ->
            let tu = (t </ var $ img)
             in if dom |<| tu
                  then return img
                  else throwError $ TypeMismatch tu dom
          _ -> throwError $ NotFunction funT
      _ -> undefined
  MathOp exprs -> do
    mapM_ (`checkExpHasType` TNum) exprs
    return TNum

checkLit :: Literal -> Check Type
checkLit l = case l of
  LInt n -> return TNum
  LVar s -> do
    Env {typeEnv, exprEnv} <- ask
    case typeEnv !? s of
      Nothing -> case exprEnv !? s of
        Nothing -> throwError $ NotInScope s
        Just expr -> checkExp expr -- TODO: Watch out for infinite  recursion; Is there Memoization?
      Just nt -> return nt
  LBool b -> return TBool

checkECase :: Type -> [ECase] -> Check Type
checkECase _ [] = throwError EmptyCase
checkECase t@(TSum ts) (c : cs) = do
  init <- checkCase c
  foldM foldCase init cs
  where
    foldCase :: Type -> ECase -> Check Type
    foldCase ty cs = do
      ct <- checkCase cs
      if ct == ty then return ty else throwError $ TypeMismatch ty ct
    checkCase :: ECase -> Check Type
    checkCase (ECase ident exp)
      | Just ty <- lookup ident ts =
        checkExp exp
          >>= ( \case
                  (TFun argT resT)
                    | argT == ty -> return resT
                    | otherwise -> throwError $ TypeMismatch ty argT
                  t -> throwError $ NotFunction t
              )
      | otherwise = throwError $ NotChannel ident t
checkECase t _ = throwError $ NotSumType t

-- Return a user defined type if there exist one
fitInductiveType :: Type -> Check (Maybe Type)
fitInductiveType ty@(TInd _ _) = return $ Just ty
fitInductiveType ty = do
  Env {typeEnv} <- ask
  return $ safeHead [ty' | ty'@(TInd _ _) <- Map.elems typeEnv, ty |<| ty']

expand :: Env -> Proc -> Proc
expand Env {typeEnv} = fmap (resolve typeEnv)

expandEnv :: Env -> Env
expandEnv Env {procEnv, exprEnv, typeEnv, alphabet} = Env {typeEnv = rTypeEnv, exprEnv = rExprEnv, procEnv = rProcEnv, alphabet = rAlpha}
  where
    rTypeEnv = resolve typeEnv <$> typeEnv
    rExprEnv = fmap (resolve rTypeEnv) <$> exprEnv
    rProcEnv = fmap (resolve rTypeEnv) <$> procEnv
    rAlpha = resolve rTypeEnv alphabet

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
checkTop env x t = runCheck expandE (check $ expand expandE x)
  where
    alphaEnv = (env {alphabet = t})
    expandE = expandEnv alphaEnv