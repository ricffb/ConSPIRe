module TypeLib where

import CSPM.Syntax (Type' (..), Type)
import Data.Bifunctor (Bifunctor (second))
import Data.Map ((!?))
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe, maybe)
import Debug.Trace

type TypeMap = Map.Map String Type

mapVar :: (a -> Type' a) -> Type' a  -> Type' a
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
(</) :: Eq a => Type' a -> a -> Type' a -> Type' a
t </ var = \t' -> mapVar (\s -> if s == var then t' else TVar s) t

rename :: Eq a => a -> a -> Type' a  -> Type' a
rename old new = fmap (\s -> if s==old then new else s)

resolve :: TypeMap -> Type -> Type
resolve env = mapVar (mapResolve env)
  where
    mapResolve :: TypeMap -> String -> Type
    mapResolve env s = maybe (TVar s) (resolve env) (env !? s) -- TODO: fix infinite recursion

  {-
    example:
    fromList [
    ("Alpha",\A -> {a.() | sq.L_Alpha}),
    ("L_Alpha",\L -> {nil.() | cons.(Alpha.L)}),
    ]

    leads to infinite recursion as neither can be resolved with this method.
  -}