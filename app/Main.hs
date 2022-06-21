module Main where

import CSPM.Parser (parseFile)
import CSPM.Syntax (Construct (Assert), PType (PType), Programm, Type' (TProc), Type)
import Data.Map ((!?))
import qualified Data.Map as Map
import Debug.Trace (traceShowId)
import Lib (Env (Env, procEnv, typeEnv), TypeError, checkTop)
import PrepParsed (prepEnv)
import System.Environment (getArgs)
import TypeLib (resolve)
import Control.Monad.Cont (MonadIO(liftIO))

main :: IO ()
main = do
  args <- getArgs
  mapM_ checkFile args

checkFile :: String -> IO ()
checkFile s = do
  file <- readFile s
  case parseFile s file of
    Left str -> putStrLn str
    Right prog ->
      let baseEnv = prepEnv prog
          asserts = [x | x@Assert {} <- prog]
       in runAssertions baseEnv asserts

runAssertions :: Env -> [Construct] -> IO ()
runAssertions baseEnv constr = do 
                            res <- mapM checkAssert constr
                            mapM_ (\(n, x) -> putStrLn $ "Result of assertion " ++ show n ++ ": " ++ if x then "success" else "fail") $ zip [1..] res 
  where
    checkAssert :: Construct -> IO Bool
    checkAssert ass@(Assert gamma procName (PType typeName _)) =
      let env = baseEnv {typeEnv = typeEnv baseEnv `Map.union` gamma}
          mPr = procEnv env !? procName
          mAlph = typeEnv env !? typeName
       in do
            putStrLn $ "\n\nRunning Assertion: " ++ prettyAssert ass
            case mPr of
              Just pr -> case mAlph of
                Just alph -> checkResult (TProc $ resolve (typeEnv env) alph) $ checkTop env pr alph
                Nothing -> putStrLn ("Alphabet type \"" ++ typeName ++ "\" was not in Scope") >> return False
              Nothing -> putStrLn ("Process with name \"" ++ typeName ++ "\" was not in Scope") >> return False
    checkAssert _ = undefined

checkResult :: Type -> Either TypeError Type -> IO Bool
checkResult _ (Left err) = print err >> return False
checkResult expect (Right ty) = if expect == ty then putStrLn ("Type check successful: " ++ show ty) >> return True 
                                else putStrLn ("Type check failed: asserted " ++ show expect ++ " but got " ++ show ty) >> return False

prettyAssert :: Construct -> String
prettyAssert (Assert gamma procName (PType typeName _)) = "assert " ++ prettyGamma gamma ++ " |- " ++ procName ++ ": Proc(" ++ typeName ++ ")"
  where
    prettyGamma :: Map.Map String Type -> String
    prettyGamma m = "{ " ++ Map.foldlWithKey (\str k t -> str ++ ", " ++ k ++ ": " ++ show t) "" m ++ " }"
prettyAssert c = show c