module ADTs
  ( -- a stack abstract data type
    Stack
  , new
  , push
  , pop
  , top
  , isempty
    -- a counter abstract data type
  , Counter
  , newC
  , incC
  ) where

import Data.IORef

-- exercise 24.2.1:
newtype Stack a = Stack { getStack :: [a] }

new :: Stack a
new = Stack []

push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> Stack a
pop (Stack [])     = Stack []
pop (Stack (x:xs)) = Stack xs

top :: Stack a -> Maybe a
top (Stack [])    = Nothing
top (Stack (x:_)) = Just x

isempty :: Stack a -> Bool
isempty (Stack [])    = True
isempty (Stack (_:_)) = False

-- exercise 24.2.2
newtype Counter a = Counter { getCounter :: IORef a }

newC :: Num a => a -> IO (Counter a)
newC = fmap Counter . newIORef

incC :: Num a => Counter a -> IO ()
incC (Counter ref) = do
  c <- readIORef ref
  writeIORef ref (c+1)

getC :: Num a => Counter a -> IO a
getC (Counter ref) = readIORef ref
