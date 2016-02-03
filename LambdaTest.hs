module LambdaTest where

import qualified Data.Map as Map
import Control.Monad
import Test.HUnit

import Lambda

substTests :: Test
substTests = TestList
  [ subst "x" (App (Var "u") (Var "y")) t1 ~?= t1'
  , subst "s" (Var "ss") (mkChurchNat 2)   ~?= t2'
  ]
  where
    t1  = Lam "x". Lam "y". Lam "z" $ App (Var "x") (Var "y")
    t1' = Lam "x_1". Lam "y_1". Lam "z" $ App (Var "x_1") (Var "y_1")
    t2' = Lam "s_1". Lam "z" $ App (Var "s_1") (App (Var "s_1") (Var "z"))

renameVars :: [(String, String)] -> Term String -> Term String
renameVars vars t = foldr renameVar t vars

renameVar :: (String, String) -> Term String -> Term String
renameVar (x,y) (Var z)
  | z == x    = (Var y)
  | otherwise = (Var z)
renameVar (x,y) (App t1 t2) = App (renameVar (x,y) t1) (renameVar (x,y) t2)
renameVar (x,y) (Lam z t1)
  | z == x    = Lam y (subst x (Var y) t1)
  | otherwise = (Lam z (renameVar (x,y) t1))

removeRestoreNamesTest :: Test
removeRestoreNamesTest = TestList
  [ removeNames Map.empty c0     ~?= nc0
  , removeNames Map.empty c2     ~?= nc2
  , removeNames Map.empty plus   ~?= nplus
  , restoreNames Map.empty nc0   ~?= renameVars [("s","v_1"), ("z","v_2")] c0
  , restoreNames Map.empty nc2   ~?= renameVars [("s", "v_1"), ("z", "v_2")] c2
  , restoreNames Map.empty nplus ~?=
      renameVars [("m", "v_1"), ("n", "v_2"), ("s", "v_3"), ("z", "v_4")] plus
  ]
  where
    c0    = mkChurchNat 0
    nc0   = LamN. LamN $ VarN 0
    c2    = mkChurchNat 2
    nc2   = LamN. LamN $ AppN (VarN 1) (AppN (VarN 1) (VarN 0))
    nplus = LamN. LamN. LamN. LamN $
      AppN (VarN 3) (VarN 1) `AppN` (AppN (VarN 2) (VarN 1) `AppN` (VarN 0))
    ctxt  = Map.empty

main :: IO ()
main = void . runTestTT $ TestList
  [ substTests
  , removeRestoreNamesTest
  ]
