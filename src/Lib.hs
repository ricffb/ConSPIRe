{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Lib where

import CSPM.Parser
import CSPM.Syntax (Action, Action' (..), ActionI, ActionI' (..), Construct (..), ECase, ECase' (..), Exp, Exp'' (..), Literal (LBool, LInt, LVar), PCase, PCase' (PCase), Proc, Proc' (..), Programm, SElem, SLiteral (LLit, LStar), SumT, Type' (..), Type, TExp'' (TExp), TExp)
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
    asks,
    lift,
    runReader,
  )
import Control.Monad.State (State)
import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (Bifunctor, bimap, first, second)
import Data.Foldable (Foldable (foldl'))
import Data.Map ((!?))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Tuple.Extra (both)
import Debug.Trace (trace, traceShow, traceShowId, traceShowM)
import Subsume (Subsume ((<|)))
import Text.Show (Show)
import TypeLib (mapVar, resolve, (</))
import Utility (safeHead)
import Control.Monad.Extra (maybeM)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data TypeError
  = TypeMismatch String Type Type
  | NotFunction Type
  | NotInScope String
  | NotExpression String
  | NotChannel String Type
  | NotSumType String Type
  | NotProduct Type
  | NotInductive Type
  | NotProcess Type
  | EmptyCase
  | Generic String
  | TooManyValues [String] Type
  deriving (Eq)

instance Show TypeError where
  show err = case err of
    TypeMismatch loc t1 t2 -> "Error TypeMismatch in " ++ loc ++ ": expected type\n" ++ show t1 ++ "\n could not be matched with actual type\n" ++ show t2
    NotFunction ty -> "Error Not a Function: Expected a function type but got: " ++ show ty
    NotInScope s -> "Error Not in Scope: Symbol " ++ s ++ " was not in scope."
    NotExpression s -> "Error Not an Expression: Expected " ++ s ++ " to be an expression."
    NotChannel s ty -> "Error Not a Channel: Expected \"" ++ s ++ "\" to be a channel of " ++ show ty
    NotSumType s ty -> "Error Not a Sum Type: Expected " ++ show ty ++ " to be a sum type in " ++ s ++ "."
    NotProduct ty -> "Error Not a Product Type: Expected " ++ show ty ++ " to be a product type."
    NotInductive ty -> "Error Not an inductive Type: Expected " ++ show ty ++ " to be inductive."
    NotProcess ty -> "Error Not a process Type: Expected " ++ show ty ++ " to be a process."
    EmptyCase -> "Error: "
    Generic s -> "Error: " ++ s
    TooManyValues ss ty -> "Error Too many values to unpack for type " ++ show ty ++ ": " ++ show ss

pEmpty :: Type
pEmpty = TProd []

sEmpty :: Type
sEmpty = TSum []

data Env = Env
  { typeEnv :: Map.Map String Type,
    procEnv :: Map.Map String Proc,
    exprEnv :: Map.Map String TExp,
    alphabet :: Type
  }
  deriving (Show)

emptyEnv :: Env
emptyEnv = Env {alphabet = TSum [], typeEnv = Map.empty, procEnv = Map.empty, exprEnv = Map.empty}

type Check = ExceptT TypeError (Reader Env)

addToEnv :: (String, Type) -> Check a -> Check a
addToEnv (n, t) = local (\env -> env {typeEnv = Map.insert n t (typeEnv env)})

addToEnv' :: [(String, Type)] -> Check a -> Check a
addToEnv' xs = local (\env -> env {typeEnv = Map.fromList xs `Map.union` typeEnv env})

-- Return a tuple of (var, type) pairs, fst -> Outputs, snd -> new Variables(TExp'' l a) (TExp'' l a)
findTypesOfChannel :: Action -> Check ([(TExp, Type)], [(String, Type)])
findTypesOfChannel (chan, items) = do
  Env {alphabet} <- ask
  case alphabet of
    t@(TSum sum) -> case lookup chan sum of
      Nothing -> throwError $ NotChannel chan t
      Just t -> matchItems t items
    _ -> throwError $ NotChannel chan alphabet
  where
    matchItems :: Type -> [ActionI] -> Check ([(TExp, Type)], [(String, Type)])
    matchItems t@(TProd typs) actions =
      if length typs /= length actions
        then throwError $ Generic $ "The number of Arguments for type " ++ show t ++ " is different: " ++ show actions
        else return $ foldl' addT ([], []) (zipWith extractNames actions typs)
    matchItems t [a] = case a of
      Output s -> return ([(s, t)], [])
      Input s -> return ([], [(s, t)])
      Selection s -> return ([], [(s, t)])
    matchItems _ _ = undefined
    extractNames (Input x) t = ([], [(x, t)])
    extractNames (Output x) t = ([(x, t)], [])
    extractNames (Selection x) t = ([], [(x, t)])

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

compareProcs :: String -> Type -> Type -> Type -> Check Type
compareProcs msg lhs rhs alphabet = case lhs of
  TProc ty
    | ty <| alphabet -> case rhs of
      TProc ty'
        | ty' <| alphabet -> return $ TProc alphabet
        | otherwise -> throwError $ TypeMismatch ("alphabet of " ++ msg ++ " rhs") alphabet ty'
      _ -> throwError $ NotProcess rhs
    | otherwise -> throwError $ TypeMismatch ("alphabet of " ++ msg ++ " lhs") alphabet ty
  _ -> throwError $ NotProcess lhs

(!!?) :: Map.Map String v -> String -> Check v
map !!? k = case map !? k of
  Nothing -> throwError $ NotInScope k
  Just v -> return v

(<!|) :: Type -> Type -> Check ()
s <!| t = if s <| t then return () else throwError $ TypeMismatch "PCase" s t

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
  CallProc process [] -> do
    Env {alphabet, procEnv, typeEnv} <- ask
    case typeEnv !? process of
      Just t -> return t
      Nothing -> case procEnv !? process of
        Nothing -> throwError $ NotInScope process
        Just pr -> addToEnv (process, TProc alphabet) $ check pr
  --
  CallProc process [arg] -> do
    Env {alphabet, procEnv, typeEnv} <- ask
    argT <- typeEnv !!? arg
    case typeEnv !? process of
      Just (TFun fargT prT) -> if argT <| fargT then return prT else throwError $ TypeMismatch "CallProc" fargT argT
      Just pr -> throwError $ NotFunction pr
      Nothing -> case procEnv !? process of
        Nothing -> throwError $ NotInScope process
        Just pr -> do
          prT <- addToEnv (process, TFun argT (TProc alphabet)) $ check pr
          case prT of
            (TFun fargT' prT') -> if argT <| fargT' then return prT' else throwError $ TypeMismatch "CallProc" fargT' argT
            pr' -> throwError $ NotFunction pr'
  --
  CallProc process args -> do
    Env {alphabet, procEnv, typeEnv} <- ask
    argTypes <- TProd <$> mapM (typeEnv !!?) args
    case typeEnv !? process of
      Just (TFun fargT prT) -> if argTypes <| fargT then return prT else throwError $ TypeMismatch "CallProc" fargT argTypes
      Just pr -> throwError $ NotFunction pr
      Nothing -> case procEnv !? process of
        Nothing -> throwError $ NotInScope process
        Just pr -> do
          prT <- addToEnv (process, TFun argTypes (TProc alphabet)) $ check pr
          case prT of
            (TFun fargT' prT') -> if argTypes <| fargT' then return prT' else throwError $ TypeMismatch "CallProc" fargT' argTypes
            pr' -> throwError $ NotFunction pr'
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
    compareProcs
      "external choice"
      lhs
      rhs
      alphabet
  --
  IntChoice pleft pright -> do
    lhs <- check pleft
    rhs <- check pright
    Env {alphabet} <- ask
    compareProcs "internal choice" lhs rhs alphabet
  --
  Ite exp pleft pright -> do
    et <- checkExpHasType exp TBool
    lhs <- check pleft
    rhs <- check pright
    Env {alphabet} <- ask
    compareProcs "if-then-else" lhs rhs alphabet
  --
  Seq pr pr' -> do
    p1Type <- check pr
    check pr'
  Parallel set pr pr' -> do
    lhs <- check pr
    rhs <- check pr'
    setTy <- checkSet set
    Env {alphabet} <- ask
    compareProcs "parallel" lhs rhs alphabet
  Hide set pr -> do
    ptype <- check pr
    setTy <- checkSet set
    Env {alphabet} <- ask
    case ptype of
      (TProc ty)
        | ty <| alphabet -> return ptype
        | otherwise -> throwError $ TypeMismatch "hide alphabet" alphabet ty
      _ -> throwError $ NotProcess ptype
  ReplIntChoice s typ pr -> do
    Env {alphabet, typeEnv} <- ask
    ptype <- addToEnv (s, resolve typeEnv typ) $ check pr
    case ptype of
      (TProc ty)
        | ty <| alphabet -> return (TProc alphabet)
        | otherwise -> throwError $ TypeMismatch "replicated internal alphabet" alphabet ty
      _ -> throwError $ NotProcess ptype
  PCaseExpr exp cases -> do
    expT <- checkTExp exp
    checkPCase expT cases
  PLambda [arg] typ pr -> do
    prT <- addToEnv (arg, typ) $ check pr
    return $ TFun typ prT
  PLambda args typ pr -> do
    argTs <- matchProd args typ
    prT <- addToEnv' argTs $ check pr
    return $ TFun typ prT
  Let var exp pr -> do
    expT <- checkTExp exp
    addToEnv (var, expT) $ check pr

matchProd :: [String] -> Type -> Check [(String, Type)]
matchProd as@(a : aas) tp@(TProd ts) =
  let las = length as
      lts = length ts
   in if las == lts
        then return $ zip as ts
        else
          if las < lts
            then
              let front = take (las - 1) ts
                  back = [TProd $ drop (las -1) ts]
               in return $ zip as (front ++ back)
            else throwError $ TooManyValues as tp
matchProd [] _ = throwError EmptyCase
matchProd _ ty = throwError $ NotProduct ty

checkPCase :: Type -> [PCase] -> Check Type
checkPCase _ [] = throwError EmptyCase
checkPCase t@(TSum sums) cases = do
  mapM_ checkCase cases
  Env {alphabet} <- ask
  return $ TProc alphabet
  where
    checkCase :: PCase -> Check ()
    checkCase (PCase str pr) = do
      let sumT = lookup str sums
      case sumT of
        Nothing -> throwError $ NotChannel str t
        Just ty -> do
          prT <- check pr
          case prT of
            TFun argT (TProc alph) -> do
              Env {alphabet} <- ask
              ty <!| argT
              alph <!| alphabet
            _ -> throwError $ NotFunction prT
checkPCase ty _ = throwError $ NotSumType "case splitting of processes" ty

checkExpHasType' :: Show l => (l -> Check Type) -> TExp'' l Type -> Type -> Check Type
checkExpHasType' chLit exp t = do
  inferredType <- checkExp' chLit exp
  if inferredType <| t
    then return t
    else throwError $ TypeMismatch "check exp has type" inferredType t

checkExpHasType = checkExpHasType' checkLit

checkTExp' :: Show l => (l -> Check Type) -> TExp'' l Type -> Check Type
checkTExp' chLit texp@(TExp exp mType) = case mType of
  Just ty -> checkExpHasType' chLit texp ty
  Nothing -> checkExp' chLit texp

-- Check Expression for type
checkExp' :: Show l => (l -> Check Type) -> TExp'' l Type -> Check Type
checkExp' _ exp | traceShow exp False = undefined
checkExp' chLit texp@(TExp exp assertTy) = case exp of
  ---
  Eq exp' exp2 ->
    if maybe False ( <| TBool) assertTy then throwError $ Generic $ "Asserted Equality type must be subsumed by bool was: " ++ maybe "" show assertTy
    else do
    rhs <- checkExp exp'
    lhs <- checkExp exp2
    if rhs == lhs then return TBool else throwError $ TypeMismatch "==" rhs lhs
  ---
  Lit s -> chLit s
  ---
  App fun arg -> do
    tfun <- checkExp fun
    targ <- checkExp arg
    case tfun of
      TFun argT retT -> if targ <| argT then return retT else throwError $ TypeMismatch "fun application" argT targ
      _ -> throwError $ NotFunction tfun
  ---
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
  ---
  ELambda argname ty expr -> do
    retT <- addToEnv (argname, ty) $ checkExp expr
    let funT = TFun ty retT
    if maybe True (funT <|) assertTy 
      then return $ fromMaybe funT assertTy
      else throwError $ TypeMismatch "lambda expr" (fromMaybe funT assertTy) funT
  ---
  ECaseExpr exp cases -> do
    expT <- checkExp exp
    checkECase chLit expT cases
  ---
  Tuple exprs -> do
    typs <- mapM checkExp exprs
    return $ TProd typs
  ---
  Sum chan expr -> do
    exprT <- checkExp expr
    return $ TSum [(chan, exprT)]
  ---
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
            case assertTy of
              Nothing -> let tu = (t </ var $ img) 
                in if dom <| tu
                  then return img
                  else throwError $ TypeMismatch "fold" tu dom
              Just aty -> 
                if img <| aty 
                then let tu = (t </ var $ aty)
                  in if dom <| tu
                     then return aty
                     else throwError $ TypeMismatch "fold" tu dom
                else throwError $ TypeMismatch "fold asserted type" aty img
          _ -> throwError $ NotFunction funT
      _ -> undefined
  ---
  MathOp exprs -> do
    mapM_ (`checkExpHasType` TNum) exprs
    return TNum
  ---
  Project i exp
    | i > 0 -> do
      ty <- checkExp exp
      case ty of
        TProd ts -> if i <= length ts then return $ ts !! (i -1) else throwError $ NotInScope $ "pr " ++ show i ++ " " ++ show ty
        _ -> throwError $ NotProduct ty
    | otherwise -> throwError $ NotInScope $ "pr " ++ show i ++ ": " ++ show i ++ "<= 0"
  ---
  LetExp var assign exp -> do
    expT <- checkExp assign
    addToEnv (var, expT) $ checkExp exp
  ---
  LetRecExp var ty assign exp -> do
    expT <- addToEnv (var, ty) $ checkExp assign
    if expT <| ty 
    then addToEnv (var, ty) $ checkExp exp
    else throwError $ TypeMismatch "let rec" ty expT
  ---
  IteExp test ifBranch elseBranch -> do
    et <- checkExpHasType test TBool
    lhs <- checkExp ifBranch
    rhs <- checkExp elseBranch
    typeMerge "exp if-then-else" lhs rhs
  

  where
    checkExp = checkExp' chLit
    checkExpHasType = checkExpHasType' chLit

typeMerge :: String -> Type -> Type -> Check Type
typeMerge _ (TSum xs) (TSum ys) = return $ TSum $ xs ++ ys
typeMerge msg x y
  | x <| y = return y
  | y <| x = return x
  | otherwise = throwError $ TypeMismatch msg x y

checkExp :: TExp -> Check Type
checkExp = checkExp' checkLit

checkTExp = checkTExp' checkLit

checkSet :: Set.Set SElem -> Check ()
checkSet = mapM_ checkElem

checkElem :: SElem -> Check Type
checkElem = checkExp' checkSLit
  where
    checkSLit :: SLiteral -> Check Type
    checkSLit lit = case lit of
      LLit lit' -> checkLit lit'
      LStar ty -> do
        Env {typeEnv} <- ask
        return $ resolve typeEnv ty

checkLit :: Literal -> Check Type
checkLit l = case l of
  LInt n -> return TNum
  LVar s -> do
    Env {typeEnv, exprEnv} <- ask
    case typeEnv !? s of
      Nothing -> case exprEnv !? s of
        Nothing -> throwError $ NotInScope s
        Just texp@(TExp exp (Just ty)) -> addToEnv (s,ty) $ checkExp texp -- TODO: Watch out for infinite  recursion; Is there Memoization?
        Just texp@(TExp exp _) -> checkExp texp --throwError $ Generic $ show texp--checkExp texp
      Just nt -> return nt
  LBool b -> return TBool

checkECase :: forall l. (Show l) => (l -> Check Type) -> Type -> [ECase' l Type] -> Check Type
checkECase _ _ [] = throwError EmptyCase
checkECase chLit t@(TSum ts) (c : cs) = do
  init <- checkCase c
  foldM foldCase init cs
  where
    foldCase :: Type -> ECase' l Type -> Check Type
    foldCase ty cs = do
      ct <- checkCase cs
      typeMerge "exp case" ct ty
    checkCase :: ECase' l Type -> Check Type
    checkCase (ECase Nothing exp) = do
      checkExp' chLit exp
    checkCase (ECase (Just ident) exp)
      | Just ty <- lookup ident ts =
        checkExp' chLit exp
          >>= ( \case
                  (TFun argT resT)
                    | argT <| ty -> return resT
                    | otherwise -> throwError $ TypeMismatch ("exp case (" ++ ident ++ ")") ty argT
                  t -> throwError $ NotFunction t
              )
      | otherwise = throwError $ NotChannel ident t
checkECase _ t _ = throwError $ NotSumType "case expression" t

-- Return a user defined type if there exist one
fitInductiveType :: Type -> Check (Maybe Type)
fitInductiveType ty@(TInd _ _) = return $ Just ty
fitInductiveType ty = do
  Env {typeEnv} <- ask
  return $ safeHead [ty' | ty'@(TInd _ _) <- Map.elems typeEnv, ty <| ty']

expand :: Env -> Proc -> Proc
expand Env {typeEnv} = fmap (resolve typeEnv)

expandEnv :: Env -> Env
expandEnv Env {procEnv, exprEnv, typeEnv, alphabet} = Env {typeEnv = rTypeEnv, exprEnv = rExprEnv, procEnv = rProcEnv, alphabet = rAlpha}
  where
    rTypeEnv = resolve typeEnv <$> typeEnv
    rExprEnv = fmap (resolve rTypeEnv) <$> exprEnv
    rProcEnv = fmap (resolve rTypeEnv) <$> procEnv
    rAlpha = resolve rTypeEnv alphabet

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Proc -> Type -> Either TypeError Type
checkTop env x t = runCheck expandE (check $ expand expandE x)
  where
    alphaEnv = env {alphabet = t}
    expandE = expandEnv alphaEnv