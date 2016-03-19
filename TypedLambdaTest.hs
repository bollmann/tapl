{-# LANGUAGE TemplateHaskell #-}
module TypedLambdaTest where

import Control.Applicative
import Control.Monad
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

toNat :: Int -> Term
toNat n
  | n < 0     = error "toNat: cannot convert negative numbers!"
  | n == 0    = Zero
  | otherwise = Succ (toNat (pred n))

toBool :: Term -> Bool
toBool Zero     = False
toBool (Succ _) = True
toBool _ = error "toBool: function is only defined on Num terms"

{- Quickcheck properties to assert that the test programs deliver the
expected results -}

prop_equal :: NonNegative Int -> NonNegative Int -> Bool
prop_equal (NonNegative m) (NonNegative n) =
  toBool (eval $ equal `App` toNat m `App` toNat n) == (m == n)

prop_plus :: NonNegative Int -> NonNegative Int -> Bool
prop_plus (NonNegative m) (NonNegative n) =
  (eval $ plus `App` toNat m `App` toNat n) == toNat (m + n)

prop_times :: NonNegative Int -> NonNegative Int -> Bool
prop_times (NonNegative m) (NonNegative n) =
  (eval $ times `App` toNat m `App` toNat n) == toNat (m * n)

-- FIXME: checking this property is *awfully* slow. How can we make it
-- faster? Also, this property doesn't work with TH's quickcheckAll. Why?
prop_factorial :: Small (NonNegative Int) -> Bool
prop_factorial (Small (NonNegative n)) =
   (eval $ factorial `App` toNat n) == toNat (product [1..n])

{- Typechecking unit tests -}

typeTests :: Test
typeTests = TestList
  [ typeOf equal     ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf plus      ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf times     ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf factorial ~?= Right (NatT :->: NatT) ]

{- Type Inference -}

-- | Another, more convoluted, implementation of unify
unify' :: [Constraint] -> Maybe (Map Type Type)
unify' = foldM go Map.empty
  where
    go sub (ty1 :~: ty2) = solve sub (substTy sub ty1 :~: substTy sub ty2)
    solve sub (ty1 :~: ty2)
      | ty1 == ty2                        = return sub
    solve sub (ty1@(VarT _) :~: ty2)
      | ty1 `occursIn` ty2                = empty
      | otherwise                         = return $ extend ty1 ty2 sub
    solve sub (ty1 :~: ty2@(VarT _))      = solve sub (ty2 :~: ty1)
    solve sub (t1 :->: t2 :~: u1 :->: u2) = do
      sub' <- solve sub (t1 :~: u1)
      go sub' (t2 :~: u2)
    solve _ _                             = empty

{- Quickcheck formalization that unify' behaves like unify -}

-- TODO: make the arbitrary instance sized so that it always terminates
instance Arbitrary Type where
  -- arbitrary :: Gen Type
  arbitrary = frequency
    [ (1, return NatT)
    , (2, (VarT . (:[])) <$> elements ['A'..'Z'])
    , (3, (:->:) <$> arbitrary <*> arbitrary) ]

instance Arbitrary Constraint where
  arbitrary = (:~:) <$> arbitrary <*> arbitrary

-- | Asserts that unify and unify' agree.
prop_unify_equals_unify' :: [Constraint] -> Bool
prop_unify_equals_unify' cs = unify cs == unify' cs

{- Type inference unit tests -}

inferTests :: Test
inferTests = TestList
  [ infer (Lam "x" (VarT "X") (Var "x")) ~?= Just (VarT "X" :->: VarT "X")
  , infer (Lam "z" (VarT "ZZ") . Lam "y" (VarT "YY") $
            Var "y" `App` (Var "z" `App` Zero))
      ~?= Just ((NatT :->: VarT "X_1") :->:
                (VarT "X_1" :->: VarT "X_2") :->: VarT "X_2")
  , infer (Lam "x" (VarT "X") . Lam "w" (VarT "W") $
            Ifz (Var "x") Zero (Var "w" `App` Var "x"))
      ~?= Just (NatT :->: (NatT :->: NatT) :->: NatT)
  , infer (Fix (Lam "f" (NatT :->: NatT) Zero)) ~?= Nothing
  , infer (Let "double" (Lam "f" (VarT "X" :->: VarT "X") . Lam "x" (VarT "X") $
                          Var "f" `App` (Var "f" `App` Var "x"))
          (Let "a" (Var "double" `App` (Lam "f" (NatT :->: NatT) (Var "f"))
                                 `App` (Lam "n" NatT Zero))
          (Let "b" (Var "double" `App` (Lam "n" NatT (Succ (Var "n")))
                                 `App` Zero)
               Zero ) ) )
      ~?= Nothing -- requires let polymorphism, which we don't (yet) support.
  ]

{- A quickcheck property asserting that 'infer' is sound wrt to 'typeof'. -}

-- TODO: make the arbitrary instance sized so that it always terminates.
instance Arbitrary Term where
  arbitrary = frequency [ (1, Var <$> varName)
                        , (1, Lam <$> varName <*> arbitrary <*> arbitrary)
                        , (1, App <$> arbitrary <*> arbitrary) ]
    where varName = fmap (:[]) (elements ['a'..'f'])

makeContext :: Term -> Context
makeContext t = Map.fromList $ zip (free t) varTys
  where varTys = [ VarT ("X_" ++ show k) | k <- ([1..] :: [Integer]) ]

prop_infer_soundness :: Term -> Bool
prop_infer_soundness t =
  case unify constraints of
    Nothing  -> True
    Just sub -> typeof (substCxt sub cxt) (substTm sub t) == Right (substTy sub ty)
  where
    (ty, constraints) = derive cxt t
    cxt               = makeContext t

-- TODO: finish this property: add arbitrary instance for type substitutions!
prop_infer_completeness :: Map Type Type -> Term -> Bool
prop_infer_completeness sub t =
  case (typeof (substCxt sub cxt) (substTm sub t), unify constraints) of
    (Left _, _)           -> True
    (Right ty, Just sub') -> sub `Map.isSubmapOf` sub' && ty == substTy sub' ty'
    _                     -> False
  where
    cxt = makeContext t
    (ty', constraints) = derive cxt t

return []
main :: IO ()
main = do
  void $ runTestTT $ TestList [ typeTests, inferTests ]
--  void $ $quickCheckAll -- doesn't work due to prop_factorial. I don't know why.
