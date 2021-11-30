module TypeLib where

import CSPM.Syntax (Type (..))
import Data.Bifunctor (Bifunctor (second))
import Data.Map ((!?))
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe, maybe)

type TypeMap = Map.Map String Type

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

-- Insert a type on Place of every Type variable
(</) :: Type -> String -> Type -> Type
t </ var = \t' -> mapVar (\s -> if s == var then t' else TVar s) t

resolve :: TypeMap -> Type -> Type
resolve env = mapVar (mapResolve env)
  where
    mapResolve :: TypeMap -> String -> Type
    mapResolve env s = maybe (TVar s) (resolve env) (env !? s)