module Subsume (Subsume, (|<|)) where

import CSPM.Syntax
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (second))
import Data.Maybe (fromMaybe)
import TypeLib ((</))

class Subsume a where
  (|<|) :: a -> a -> Bool

instance Subsume Type where
  ty |<| i@(TInd var ty') = ty |<| (ty' </ var $ i)
  (TSum sts) |<| (TSum sts') = foldr foldSubsume True sts
    where
      foldSubsume :: SumT Type -> Bool -> Bool
      foldSubsume _ False = False
      foldSubsume (s, t) b =
        False `fromMaybe` do
          t' <- lookup s sts'
          let b' = t |<| t'
          return $ b && b'
  (TProd []) |<| (TProd []) = True
  (TProd tys) |<| (TProd tys') = and $ zipWith (|<|) tys tys'
  (TFun dom img) |<| (TFun dom' img') = (dom |<| dom') && (img |<| img')
  ty |<| ty' = ty == ty'
