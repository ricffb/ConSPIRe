{-# LANGUAGE RankNTypes #-}
module Subsume (Subsume, (<|)) where

import CSPM.Syntax
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (second))
import Data.Maybe (fromMaybe)
import TypeLib ((</), rename)
import Debug.Trace (trace, traceShowId)

class Subsume a where
  (<|) :: a -> a -> Bool

instance forall a .(Eq a, Show a) => Subsume (Type' a)  where
  -- (<|) t1 t2 | trace (show t1 ++ "\n<|\n" ++ show t2 ++ "\n") False = undefined
  ty <| ty' | ty == ty' = True
  ind1@(TInd var1 ty1) <| ind2@(TInd var2 ty2)
    | var1 == var2 = ty1 <| ty2
    | otherwise = ty1 <| rename var2 var1 ty2 -- Check if two inductive types only differ in their names 
  ty <| i@(TInd var ty') = ty <| (ty' </ var $ i)
  (TSum sts) <| (TSum sts') = foldr foldSubsume True sts
    where
      --foldSubsume :: SumT (Type' a) -> Bool -> Bool
      foldSubsume _ False = False
      foldSubsume (s, t) b =
        False `fromMaybe` do
          t' <- lookup s sts'
          let b' = t <| t'
          return $ b && b'
  (TProd []) <| (TProd []) = True
  (TProd tys) <| (TProd tys')
    | length tys == length tys' = and $ zipWith (<|) tys tys'
  (TFun dom img) <| (TFun dom' img') = (dom' <| dom) && (img <| img')
  ty <| ty' = ty == ty'
