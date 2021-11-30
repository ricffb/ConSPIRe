module Utility (safeHead) where

safeHead :: [a] -> Maybe a
safeHead (x : _) = Just x
safeHead _ = Nothing

unEither :: Either a a -> a
unEither (Right a) = a
unEither (Left a) = a
