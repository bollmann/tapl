{-# LANGUAGE TemplateHaskell #-}
module TypedLambdaTest where

import Control.Applicative
import Control.Monad
import Data.Either
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude
import Test.HUnit hiding (Testable)
import Test.QuickCheck

import TypedLambda

{- Test Programs in PCF, based on exercise 11.11.1 -}

false, true :: Term
false = Zero
true  = Succ Zero

equal :: Term
equal = Fix eqf where
  eqf = Lam "eq" (NatT :->: NatT :->: NatT) . Lam "m" NatT . Lam "n" NatT $
          Ifz (Var "m")
            (Ifz (Var "n")
              true
              false)
            (Ifz (Var "n")
              false
              ((Var "eq") `App` (Pred (Var "m")) `App` (Pred (Var "n"))))

plus :: Term
plus =
 Let "plf"
   (Lam "pl" (NatT :->: NatT :->: NatT) . Lam "m" NatT . Lam "n" NatT $
     Ifz (Var "m")
       (Var "n")
       (Succ (Var "pl" `App` Pred (Var "m") `App` Var "n")))
   (Fix (Var "plf"))

times :: Term
times =
  Let "tif" (Lam "ti" (NatT :->: NatT :->: NatT) . Lam "m" NatT . Lam "n" NatT $
              Ifz (Var "m")
                Zero
                (plus `App` Var "n" `App`
                  (Var "ti" `App` Pred (Var "m") `App` Var "n")))
  (Fix (Var "tif"))

factorial :: Term
factorial =
  Let "fa" (Lam "fact" (NatT :->: NatT) . Lam "n" NatT $
             Ifz (Var "n")
               (Succ Zero)
               (times `App` (Var "n") `App`
                 ((Var "fact") `App` Pred (Var "n"))))
  (Fix (Var "fa"))

toNatTerm :: Int -> Term
toNatTerm n
  | n < 0     = error "toNatTerm: cannot convert negative numbers!"
  | n == 0    = Zero
  | otherwise = Succ (toNatTerm (pred n))

toBool :: Term -> Bool
toBool Zero     = False
toBool (Succ _) = True
toBool _ = error "toBool: function is only defined on Num terms"

{- Quickcheck properties to assert that the test programs deliver the
expected results -}

prop_equal :: NonNegative Int -> NonNegative Int -> Bool
prop_equal (NonNegative m) (NonNegative n) =
  toBool (eval $ equal `App` toNatTerm m `App` toNatTerm n) == (m == n)

prop_plus :: NonNegative Int -> NonNegative Int -> Bool
prop_plus (NonNegative m) (NonNegative n) =
  (eval $ plus `App` toNatTerm m `App` toNatTerm n) == toNatTerm (m + n)

prop_times :: NonNegative Int -> NonNegative Int -> Bool
prop_times (NonNegative m) (NonNegative n) =
  (eval $ times `App` toNatTerm m `App` toNatTerm n) == toNatTerm (m * n)

-- FIXME: checking this property is *awfully* slow. How can we make it
-- faster? Also, this property doesn't work with TH's quickcheckAll. Why?
prop_factorial :: Small (NonNegative Int) -> Bool
prop_factorial (Small (NonNegative n)) =
   (eval $ factorial `App` toNatTerm n) == toNatTerm (product [1..n])

{- Typechecking unit tests -}

typeTests :: Test
typeTests = TestList
  [ typeOf equal     ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf plus      ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf times     ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf factorial ~?= Right (NatT :->: NatT) ]

testProp :: Testable prop => (String, prop) -> IO ()
testProp (lbl, p) = do
  putStrLn $ "testing " ++ lbl ++ ": "
  quickCheck p

return []
main :: IO ()
main = do
  void $ runTestTT $ TestList [typeTests]
  mapM_ testProp [ ("prop_equal", prop_equal)
                 , ("prop_plus", prop_plus)
                 , ("prop_times", prop_times) ]
--void $ $quickCheckAll -- doesn't work due to prop_factorial. I don't know why.
