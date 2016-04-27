-- some church encodings in pure System F.
{-# LANGUAGE RankNTypes #-}
module Church where

import Prelude hiding (succ)

{- Booleans -}

type CBool = forall a. a -> a -> a

tru, fls :: CBool
tru = \t -> \f -> t
fls = \t -> \f -> f

test :: forall r. CBool -> r -> r -> r
test b t e = b t e

{- Naturals -}

type CNat = forall s. (s -> s) -> s -> s

zero :: CNat
zero s z = z

succ :: CNat -> CNat
succ n s z = s (n s z)

mkChurchNat :: Int -> CNat
mkChurchNat n
  | n < 0     = error "mkChurchNat: can only be used on non-negative numbers."
  | n == 0    = zero
  | otherwise = succ (mkChurchNat (n-1))

{- Lists -}

type CList a = forall r. (a -> r -> r) -> r -> r

nil :: forall a. CList a
nil c n = n

cons :: forall a. a -> CList a -> CList a
cons x l = \c -> \n -> c x (l c n)

isnil :: forall a. CList a -> CBool
isnil l = l (\x xs -> fls) tru
