{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module ExistentialObjects where

import Prelude hiding (read)

data CounterMethods a
  = Methods {
    get :: a -> Int
  , inc :: a -> a
  }

data Counter where
  Counter :: forall b. { state :: b, methods :: CounterMethods b } -> Counter

c = Counter { state = 0
            , methods = Methods { get = (\x -> x)
                                , inc = (\x -> succ x) } }

sendGet :: Counter -> Int
sendGet (Counter state methods) = (get methods) state

sendInc :: Counter -> Counter
sendInc (Counter state methods) = Counter (inc methods state) methods

data FlipFlop where
  FlipFlop :: forall a.
              { ctr    :: a
              , read   :: a -> Bool
              , toggle :: a -> a
              , reset  :: a -> a }
           -> FlipFlop

flipFlop = FlipFlop { ctr    = c
                    , read   = \c -> even (sendGet c)
                    , toggle = \c -> sendInc c
                    , reset  = \_ -> c }

sendNew :: FlipFlop -> FlipFlop
sendNew (FlipFlop state read toggle reset)
  = FlipFlop (reset state) read toggle reset

sendRead :: FlipFlop -> Bool
sendRead (FlipFlop state read toggle reset)
  = read state

sendToggle :: FlipFlop -> FlipFlop
sendToggle (FlipFlop state read toggle reset)
  = FlipFlop (toggle state) read toggle reset

sendReset :: FlipFlop -> FlipFlop
sendReset _ = flipFlop
