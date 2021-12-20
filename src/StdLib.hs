module StdLib where

import CSPM.Syntax (Exp, Exp'' (ELambda, Project), Type (TBool, TNum))
import qualified Data.Map as Map

stdTypeEnv :: Map.Map String Type
stdTypeEnv = Map.fromList [("Bool", TBool), ("Int", TNum)]