{-# LANGUAGE NamedFieldPuns #-}

module PrepParsed (prepEnv) where

import CSPM.Syntax (Construct (Assert, NamedExpr, NamedProc, NamedType, TypeVar), Proc' (PLambda), Type (TProd, TVar))
import Data.Foldable (foldl')
import qualified Data.Map as Map
import Lib (Env (Env, exprEnv, procEnv, typeEnv), emptyEnv)
import StdLib (stdTypeEnv)

-- Transform a named proc with args into a Lambda Proc without args
tfNamedProc :: Construct -> Construct
tfNamedProc np@(NamedProc name [] pr) = np
tfNamedProc np@(NamedProc name [(argName, typ)] pr) = NamedProc name [] $ PLambda [argName] typ pr
tfNamedProc (NamedProc name args pr) = NamedProc name [] newPr
  where
    argNames = fst <$> args
    argTy = TProd $ snd <$> args
    newPr = PLambda argNames argTy pr
tfNamedProc ct = ct

prepEnv :: [Construct] -> Env
prepEnv = foldl' (flip $ collectEnv . tfNamedProc) stdEnv
  where
    stdEnv = emptyEnv {typeEnv = stdTypeEnv}
    collectEnv :: Construct -> Env -> Env
    collectEnv constr env@Env {typeEnv, procEnv, exprEnv} = case constr of
      TypeVar s -> let newtEnv = Map.insert s (TVar s) typeEnv in env --{typeEnv = newtEnv}
      NamedType s ty -> let newtEnv = Map.insert s ty typeEnv in env {typeEnv = newtEnv}
      NamedExpr s ex -> let neweEnv = Map.insert s ex exprEnv in env {exprEnv = neweEnv}
      Assert {} -> env
      NamedProc s [] pr -> let newpEnv = Map.insert s pr procEnv in env {procEnv = newpEnv}
      NamedProc {} -> undefined -- must not occur due to tfNamedProc
