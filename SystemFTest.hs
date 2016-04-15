{-# LANGUAGE TemplateHaskell #-}
module SystemFTest where

import Control.Applicative
import Control.Monad
import Data.Either
import Data.Map (Map)
import qualified Data.Map as Map
import Test.HUnit hiding (Testable)
import Test.QuickCheck

import Prelude hiding (succ)

import SystemF

{- Test Programs in PCF -}

false, true :: Term
false = Zero
true  = Succ Zero

equals :: Term
equals = Fix eqf where
  eqf = Lam eq (NatT :->: NatT :->: NatT) . Lam m NatT . Lam n NatT $
          Ifz (Var m)
            (Ifz (Var n)
              true
              false)
            (Ifz (Var n)
              false
              ((Var eq) `App` (Pred (Var m)) `App` (Pred (Var n))))
  [eq, m, n] = map TermVar ["eq", "m", "n"]

succ :: Term
succ = Lam n NatT $ Succ (Var n)

plus :: Term
plus =
 Let plf
   (Lam pl (NatT :->: NatT :->: NatT) . Lam m NatT . Lam n NatT $
     Ifz (Var m)
       (Var n)
       (Succ (Var pl `App` Pred (Var m) `App` Var n)))
   (Fix (Var plf))
  where [plf, pl, m, n] = map TermVar ["plf", "pl", "m", "n"]

times :: Term
times =
  Let tif (Lam ti (NatT :->: NatT :->: NatT) . Lam m NatT . Lam n NatT $
              Ifz (Var m)
                Zero
                (plus `App` Var n `App`
                  (Var ti `App` Pred (Var m) `App` Var n)))
  (Fix (Var tif))
  where [tif, ti, m, n] = map TermVar ["tif", "ti", "m", "n"]

factorial :: Term
factorial =
  Let fa (Lam fact (NatT :->: NatT) . Lam n NatT $
             Ifz (Var n)
               (Succ Zero)
               (times `App` (Var n) `App`
                 ((Var fact) `App` Pred (Var n))))
  (Fix (Var fa))
  where [fa, fact, n] = map TermVar ["fa", "fact", "n"]

toNatTerm :: Int -> Term
toNatTerm n
  | n < 0     = error "toNatTerm: cannot convert negative numbers!"
  | n == 0    = Zero
  | otherwise = Succ (toNatTerm (pred n))

toBool :: Term -> Bool
toBool Zero     = False
toBool (Succ _) = True
toBool _ = error "toBool: function is only defined on Num terms"

{- Quickcheck properties asserting that the test programs above compute
the expected results -}

prop_equals :: NonNegative Int -> NonNegative Int -> Bool
prop_equals (NonNegative m) (NonNegative n) =
  toBool (eval $ equals `App` toNatTerm m `App` toNatTerm n) == (m == n)

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

{- Polymorphic test programs -}

-- some types and terms for later uses:
xTy, yTy, zTy :: TypeVar
xTy = TypeVar "X"
yTy = TypeVar "Y"
zTy = TypeVar "Z"

f, n, m, s, x, y, z :: TermVar
f = TermVar "f"
n = TermVar "n"
m = TermVar "m"
s = TermVar "s"
x = TermVar "x"
y = TermVar "y"
z = TermVar "z"

idF :: Term
idF = LamT xTy . Lam x (VarT xTy) $ (Var x)

selfApp :: Term
selfApp = Lam x (ForallT xTy (VarT xTy :->: VarT xTy)) $
  (Var x) `AppT` (ForallT xTy (VarT xTy :->: VarT xTy)) `App` (Var x)

{- Church Booleans -}

cbool :: Type
cbool = ForallT xTy (VarT xTy :->: VarT xTy :->: VarT xTy)

cfls, ctru, ctest, cand :: Term
cfls  = LamT xTy . Lam x (VarT xTy) . Lam y (VarT xTy) $ (Var y)
ctru  = LamT xTy . Lam x (VarT xTy) . Lam y (VarT xTy) $ (Var x)
ctest = LamT xTy . Lam x cbool . Lam y (VarT xTy) . Lam z (VarT xTy) $
  Var x `AppT` VarT xTy `App` Var y `App` Var z

cand' = Lam x cbool. Lam y cbool. LamT yTy. Lam s (VarT yTy). Lam z (VarT yTy) $
  (ctest `AppT` cbool `App` Var x `App` Var y `App` cfls)
    `AppT` VarT yTy `App` Var s `App` Var z

cand = Lam x cbool. Lam y cbool $
  ctest `AppT` cbool `App` Var x `App` Var y `App` cfls


-- TODO: write more combinators (e.g., `or`, etc.) and state some
-- properties about them!

{- Church Naturals -}

cnat :: Type
cnat = ForallT xTy ((VarT xTy :->: VarT xTy) :->: VarT xTy :->: VarT xTy)

churchNat :: Int -> Term
churchNat n
  | n < 0     = error "makeChurchNat: can only convert non-negative numbers!"
  | otherwise = LamT xTy . Lam s (VarT xTy :->: VarT xTy) . Lam z (VarT xTy) $
                  foldr (\_ acc -> (Var s) `App` acc) (Var z) [1..n]

csucc, cplus, ctimes, cpred, ciszero, cequals :: Term
csucc = Lam n cnat. LamT yTy. Lam s (VarT yTy :->: VarT yTy). Lam z (VarT yTy) $
  Var s `App` (Var n `AppT` VarT yTy `App` Var s `App` Var z)

cplus = Lam m cnat. Lam n cnat. LamT xTy. Lam s (VarT xTy :->: VarT xTy).
  Lam z (VarT xTy) $ Var m `AppT` VarT xTy `App` Var s `App`
    (Var n `AppT` VarT xTy `App` Var s `App` Var z)

ctimes = Lam m cnat. Lam n cnat $
  Var n `AppT` cnat `App` (cplus `App` Var m) `App` churchNat 0

{- Church Pairs for Naturals -}

-- a generic definition of pairs:
-- but uh, ah! we cannot instantiate it correctly without type operators!
-- that is, these pairs are essentially useless.
cpair :: Type
cpair = ForallT zTy
  ((ForallT xTy (ForallT yTy (VarT xTy :->: VarT yTy :->: VarT zTy)))
   :->: VarT zTy)

cpr, cfst, csnd :: Term
cpr = LamT xTy. LamT yTy . Lam x (VarT xTy). Lam y (VarT yTy). LamT zTy.
  Lam f (ForallT xTy (ForallT yTy (VarT xTy :->: VarT yTy :->: VarT zTy))) $
    Var f `AppT` VarT xTy `AppT` VarT yTy `App` Var x `App` Var y

cfst = LamT xTy. Lam z cpair $ Var z `AppT` VarT xTy `App` first
  where first = LamT xTy. LamT yTy. Lam x (VarT xTy). Lam y (VarT yTy) $ Var x

csnd = LamT yTy. Lam z cpair $ Var z `AppT` VarT yTy `App` second
  where second = LamT xTy. LamT yTy. Lam x (VarT xTy). Lam y (VarT yTy) $ Var y

cnatpair :: Type
cnatpair = ForallT zTy ((cnat :->: cnat :->: VarT zTy) :->: VarT zTy)

cnatpr, cnatfst, cnatsnd :: Term
cnatpr = Lam x cnat. Lam y cnat. LamT zTy. Lam f (cnat :->: cnat :->: VarT zTy)
  $ Var f `App` Var x `App` Var y

cnatfst = Lam z cnatpair $ Var z `AppT` cnat `App` (ctru `AppT` cnat)
cnatsnd = Lam z cnatpair $ Var z `AppT` cnat `App` (cfls `AppT` cnat)

cpred = Lam n cnat $ cnatsnd `App` (Var n `AppT` cnatpair `App` ss `App` zz)
  where
    ss = Lam z cnatpair $
      cnatpr `App` (csucc `App` (cnatfst `App` Var z))
             `App` (cnatfst `App` Var z)
    zz = cnatpr `App` churchNat 0 `App` churchNat 0

ciszero = Lam n cnat $ Var n `AppT` cbool `App` (Lam x cbool cfls) `App` ctru

cequals = Lam m cnat. Lam n cnat $
  cand `App` (ciszero `App` (Var m `AppT` cnat `App` cpred `App` Var n))
       `App` (ciszero `App` (Var n `AppT` cnat `App` cpred `App` Var m))

-- FIXME: testing this property is quite slow. WHY??
prop_equals_cequals
  :: (NonNegative (Small Int)) -> (NonNegative (Small Int)) -> Property
prop_equals_cequals (NonNegative (Small m)) (NonNegative (Small n))
  = eval primEquals === eval churchEquals
  where
    primEquals = equals `App` toNatTerm m `App` toNatTerm n
    churchEquals = cequals `App` churchNat m `App` churchNat n
      `AppT` NatT `App` (Succ Zero) `App` Zero

prop_plus_cplus :: NonNegative Int -> NonNegative Int -> Bool
prop_plus_cplus (NonNegative m) (NonNegative n) =
  eval primitivePlus == eval churchPlus
  where
    primitivePlus = plus `App` toNatTerm m `App` toNatTerm n
    churchPlus = cplus `App` churchNat m `App` churchNat n
      `AppT` NatT `App` succ `App` Zero


prop_times_ctimes :: NonNegative Int -> NonNegative Int -> Property
prop_times_ctimes (NonNegative m) (NonNegative n) =
  eval primTimes === eval churchTimes
  where
    primTimes = times `App` toNatTerm m `App` toNatTerm n
    churchTimes = ctimes `App` churchNat m `App` churchNat n
      `AppT` NatT `App` succ `App` Zero

{- Typechecking unit tests -}

typeTests :: Test
typeTests = TestList
  [ isLeft (typeOf (equals `App` plus)) ~? "wrong type!"
  , typeOf equals            ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf plus              ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf times             ~?= Right (NatT :->: NatT :->: NatT)
  , typeOf factorial         ~?= Right (NatT :->: NatT)
  , typeOf idF               ~?= Right (ForallT xTy (VarT xTy :->: VarT xTy))
  , typeOf (idF `AppT` NatT) ~?= Right (NatT :->: NatT)
  , typeOf selfApp           ~?= Right ((ForallT xTy (VarT xTy :->: VarT xTy))
                                   :->: (ForallT xTy (VarT xTy :->: VarT xTy)))
  , typeOf cfls              ~?= Right cbool
  , typeOf ctest             ~?= Right (ForallT xTy (cbool :->:
                                   VarT xTy :->: VarT xTy :->: VarT xTy))
  , typeOf cand              ~?= Right (cbool :->: cbool :->: cbool)
  , typeOf (churchNat 3)     ~?= Right cnat
  , typeOf (churchNat 9)     ~?= Right cnat
  , typeOf cplus             ~?= Right (cnat :->: cnat :->: cnat)
  , typeOf ctimes            ~?= Right (cnat :->: cnat :->: cnat)
  , typeOf ciszero           ~?= Right (cnat :->: cbool)
  , typeOf cnatpr            ~?= Right (cnat :->: cnat :->: cnatpair)
  , typeOf cnatfst           ~?= Right (cnatpair :->: cnat)
  , typeOf cnatsnd           ~?= Right (cnatpair :->: cnat)
  , typeOf cpred             ~?= Right (cnat :->: cnat)
  , typeOf cequals           ~?= Right (cnat :->: cnat :->: cnat) ]

evalTests :: Test
evalTests = TestList
  [ eval (isZeroWith 9) ~?= false -- i.e., 9 is /not/ equal to zero.
  , eval (isZeroWith 0) ~?= true  -- i.e., 0 is equal to zero
  ]
  where
    isZeroWith n
      = ciszero `App` churchNat n `AppT` NatT `App` (Succ Zero) `App` Zero

testProp :: Testable prop => (String, prop) -> IO ()
testProp (lbl, p) = do
  putStrLn $ "testing " ++ lbl ++ ": "
  quickCheck p

return []
main :: IO ()
main = do
  void $ runTestTT $ TestList [ typeTests, evalTests]
  mapM_ testProp [ ("prop_equal", prop_equals)
                 , ("prop_plus", prop_plus)
                 , ("prop_times", prop_times) ]
--void $ $quickCheckAll -- doesn't work due to prop_factorial. I don't know why.
