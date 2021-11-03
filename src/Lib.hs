module Lib
  ( someFunc,
  )
where

import Language.CSPM.AST
import Language.CSPM.Frontend

someFunc :: IO ()
someFunc = putStrLn "someFunc"

myTraverse :: ModuleFromParser