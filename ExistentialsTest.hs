module ExistentialsTest where

import Test.HUnit

import ADTs
import ExistentialObjects

testStack :: Test
testStack = TestList
  [ top (push 3 (push 2 (push 1 new)))    ~?= Just 3
  , top new                               ~?= (Nothing :: Maybe Int)
  , top (push 2 (pop (pop (push 1 new)))) ~?= Just 2 ]

testCounter :: Test
testCounter = TestList
  [ sendGet c                                   ~?= 0
  , (sendGet . sendInc . sendInc . sendInc $ c) ~?= 3 ]

testFlipFlop :: Test
testFlipFlop = TestList
  [ sendRead flipFlop                               ~?= True
  , sendRead (sendToggle flipFlop)                  ~?= False
  , (sendRead . sendToggle . sendToggle $ flipFlop) ~?= True
  ]

main = runTestTT $ TestList [ testStack, testCounter, testFlipFlop ]
