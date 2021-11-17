import CSPM.Syntax
import Lib (Env, TypeError, checkTop, pEmpty, runCheck)
import Test.Hspec

main :: IO ()
main =
  hspec $
    describe "Lib.check" $ do
      it "uses Processes from the Environment" $
        checkTop trivEnv trivial tBool `shouldBe` (Right (TProc tBool) :: Either TypeError Type)
      it "deduces Prefix Types" $
        checkTop [] withPrefix prefixT `shouldBe` (Right (TProc prefixT) :: Either TypeError Type)

tBool :: Type
tBool = TSum [("true", pEmpty), ("false", pEmpty)]

trivial :: Proc
trivial = ExtChoice (Ite (Eq (Lit $ LVar "s") (Lit $ LVar "s'")) (CallProc "P" []) STOP) (CallProc "Q" [])

withVarIte :: Proc
withVarIte = Ite (Lit $ LVar "y") SKIP STOP

withPrefix :: Proc
withPrefix = Prefix ("in", [Input "x", Input "y"]) $ Prefix ("out", [Output $ Eq (Lit $ LVar "x") (Lit $ LVar "x")]) withVarIte

prefixT :: Type
prefixT = TSum [("in", TProd [tBool, TBool]), ("out", TBool)]

trivEnv :: Env
trivEnv = undefined

-- trivEnv = [("s", Left $ TVar "X"), ("s'", Left $ TVar "X"), ("P", Left (TProc tBool)), ("Q", Right (ExtChoice (CallProc "P" []) STOP))]