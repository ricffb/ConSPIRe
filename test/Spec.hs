import CSPM.Syntax
import qualified Data.Map as Map
import Lib (Env (..), TypeError, checkTop, pEmpty, runCheck)
import Test.Hspec

main :: IO ()
main =
  hspec $
    describe "Lib.check" $ do
      it "uses Processes from the Environment" $
        checkTop trivEnv trivial tBool `shouldBe` (Right (TProc tBool) :: Either TypeError Type)
      it "deduces Prefix Types" $
        checkTop emptyEnv withPrefix prefixT `shouldBe` (Right (TProc prefixT) :: Either TypeError Type)
      it "can handle case in expression" $
        let alph = alphabet withECaseEnv in checkTop withECaseEnv withECaseExpr alph `shouldBe` (Right (TProc alph) :: Either TypeError Type)

tBool :: Type
tBool = TSum [("myTrue", pEmpty), ("myFalse", pEmpty)]

emptyEnv :: Env
emptyEnv = Env {alphabet = TSum [], typeEnv = Map.empty, procEnv = Map.empty}

trivial :: Proc
trivial = ExtChoice (Ite (Eq (Lit $ LVar "s") (Lit $ LVar "s'")) (CallProc "P" []) STOP) (CallProc "Q" [])

withVarIte :: Proc
withVarIte = Ite (Lit $ LVar "y") SKIP STOP

withPrefix :: Proc
withPrefix = Prefix ("in", [Input "x", Input "y"]) $ Prefix ("out", [Output $ Eq (Lit $ LVar "x") (Lit $ LVar "x")]) withVarIte

-- let f = \ u : U -> case u of myTrue -> \t : E -> true of myFalse -> \t : E -> false within in?u -> if f u then SKIP else STOP
withECaseExpr :: Proc
withECaseExpr = Let "f" (ELambda "u" "U" (ECaseExpr (Lit (LVar "u")) [ECase "myFalse" (ELambda "t" "E" (Lit (LBool False))), ECase "myTrue" (ELambda "t" "E" (Lit (LBool True)))])) (Prefix ("in", [Input "u"]) (Ite (App (Lit (LVar "f")) (Lit (LVar "u"))) SKIP STOP))

withECaseEnv :: Env
withECaseEnv =
  Env
    { alphabet = TSum [("in", tBool)],
      typeEnv = Map.fromList [("U", tBool), ("E", pEmpty)],
      procEnv = Map.empty
    }

prefixT :: Type
prefixT = TSum [("in", TProd [tBool, TBool]), ("out", TBool)]

trivEnv :: Env
trivEnv =
  Env
    { alphabet = tBool,
      typeEnv = Map.fromList [("s", TVar "X"), ("s'", TVar "X"), ("P", TProc tBool)],
      procEnv = Map.singleton "Q" $ ExtChoice (CallProc "P" []) STOP
    }