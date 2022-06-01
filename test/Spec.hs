import CSPM.Syntax
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lib (Env (..), TypeError, checkTop, pEmpty, runCheck)
import Test.Hspec


{--
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
      it "can deal with inductive types" $
        let alph = alphabet foldEnv in checkTop foldEnv foldProc alph `shouldBe` (Right (TProc alph) :: Either TypeError Type)
      it "can handle sets in parallel op" $
        let alph = alphabet parallelEnv in checkTop parallelEnv parallelProc alph `shouldBe` (Right (TProc alph) :: Either TypeError Type)

tBool :: Type
tBool = TSum [("myTrue", pEmpty), ("myFalse", pEmpty)]

emptyEnv :: Env
emptyEnv = Env {alphabet = TSum [], typeEnv = Map.empty, procEnv = Map.empty, exprEnv = Map.empty}

trivial :: Proc
trivial = ExtChoice (Ite (Eq (Lit $ LVar "s") (Lit $ LVar "s'")) (CallProc "P" []) STOP) (CallProc "Q" [])

withVarIte :: Proc
withVarIte = Ite (Lit $ LVar "y") SKIP STOP

withPrefix :: Proc
withPrefix = Prefix ("in", [Input "x", Input "y"]) $ Prefix ("out", [Output $ Eq (Lit $ LVar "x") (Lit $ LVar "x")]) withVarIte

-- let f = \ u : U ->
-- case u of myTrue -> \t : E -> true
--        of myFalse -> \t : E -> false within in?u -> if f u then SKIP else STOP
withECaseExpr :: Proc
withECaseExpr = Let "f" (ELambda "u" (TVar "U") (ECaseExpr (Lit (LVar "u")) [ECase "myFalse" (ELambda "t" (TVar "E") (Lit (LBool False))), ECase "myTrue" (ELambda "t" (TVar "E") (Lit (LBool True)))])) (Prefix ("in", [Input "u"]) (Ite (App (Lit (LVar "f")) (Lit (LVar "u"))) SKIP STOP))

withECaseEnv :: Env
withECaseEnv =
  Env
    { alphabet = TSum [("in", tBool)],
      typeEnv = Map.fromList [("U", tBool), ("E", pEmpty)],
      procEnv = Map.empty,
      exprEnv = Map.empty
    }

prefixT :: Type
prefixT = TSum [("in", TProd [tBool, TBool]), ("out", TBool)]

trivEnv :: Env
trivEnv =
  Env
    { alphabet = tBool,
      typeEnv = Map.fromList [("s", TVar "X"), ("s'", TVar "X"), ("P", TProc tBool)],
      procEnv = Map.singleton "Q" $ ExtChoice (CallProc "P" []) STOP,
      exprEnv = Map.empty
    }

foldEnv :: Env
foldEnv =
  Env
    { alphabet = TSum [("asklen", TInd "L" (TSum [("nil", TProd []), ("cons", TProd [TBool, TVar "L"])])), ("retlen", TNum)],
      typeEnv = Map.fromList [("MyList", TInd "L" (TSum [("nil", TProd []), ("cons", TProd [TVar "Bool", TVar "L"])])), ("Bool", TBool), ("Int", TNum), ("snd", TFun (TProd [TVar "Bool", TVar "Int"]) (TVar "Int"))],
      procEnv = Map.empty,
      exprEnv =
        Map.fromList
          [ ("ll", Sum "cons" (Tuple [Lit (LBool True), Sum "cons" (Tuple [Lit (LBool False), Sum "nil" (Tuple [])])])),
            ("calcLen", ELambda "xs" (TSum [("nil", TProd []), ("cons", TProd [TVar "Bool", TVar "Int"])]) (ECaseExpr (Lit (LVar "xs")) [ECase "cons" (ELambda "tpl" (TProd [TVar "Bool", TVar "Int"]) (MathOp [Lit (LInt 1), App (Lit (LVar "snd")) (Lit (LVar "tpl"))])), ECase "nil" (ELambda "y" (TProd []) (Lit (LInt 0)))]))
          ]
    }

foldProc :: Proc
foldProc = Prefix ("asklen", [Input "list"]) (Let "len" (Fold (Lit (LVar "list")) (Lit (LVar "calcLen"))) (Prefix ("retlen", [Output (Lit (LVar "len"))]) SKIP))

parallelEnv :: Env
parallelEnv =
  Env
    { alphabet = TSum [("send", TProd [u, u, TVar "X"]), ("recv", TProd [u, u, TVar "X"])],
      typeEnv = Map.fromList [("U", u)],
      procEnv = Map.fromList [("A", Prefix ("send", [Output (Sum "a" (Tuple [])), Output (Sum "b" (Tuple [])), Input "x"]) STOP), ("B", Prefix ("recv", [Output (Sum "b" (Tuple [])), Input "from", Input "m"]) STOP), ("Net", Prefix ("send", [Input "from", Input "to", Input "m"]) (Prefix ("recv", [Output (Lit (LVar "to")), Output (Lit (LVar "from")), Output (Lit (LVar "m"))]) (CallProc "Net" [])))],
      exprEnv = Map.empty
    }
  where
    u = TSum [("a", TProd []), ("b", TProd []), ("c", TProd [])]

parallelProc :: Proc
parallelProc = Parallel (Set.fromList [Sum "recv" (Lit (LStar (TProd [TVar "U", TVar "U", TVar "X"]))), Sum "send" (Lit (LStar (TProd [TVar "U", TVar "U", TVar "X"])))]) (Parallel (Set.fromList []) (CallProc "A" []) (CallProc "B" [])) (CallProc "Net" [])
--}