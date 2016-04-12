module ADTsTest where

import ADTs
import Test.HUnit

testStack :: Test
testStack = TestList
  [ top (push 3 (push 2 (push 1 new)))    ~?= Just 3
  , top new                               ~?= (Nothing :: Maybe Int)
  , top (push 2 (pop (pop (push 1 new)))) ~?= Just 2 ]

main = runTestTT $ TestList [ testStack ]
