module Main where  

import Test.HUnit
import Debug.Trace

import Syntax
import TypeCheck (runTC, runTCD, Label, Decl)
import qualified System.Exit as Exit
import Free.Scope (Graph)

runTCTest :: Expr -> IO (Type, Graph Label Decl) 
runTCTest = either assertFailure return . runTC

runTCDTest :: DeclT -> IO (Type, Graph Label Decl)
runTCDTest = either assertFailure return . runTCD

-- Define your test cases like the following
testApplicationPlus :: IO ()
testApplicationPlus = do
  t <- runTCTest $ App (Abs "x" NumT (Plus (Ident "x") (Ident "x"))) (Num 21)
  trace "why" $ return ()
  assertEqual "Incorrect type" NumT $ fst t

testClass :: IO ()
testClass = do 
  t <- runTCDTest $ ClassT "Eq" ["a"] [Var "==" (Forall ["a", "a"] "Bool")]
  assertEqual "Typecheck not ok" BoolT $ fst t

tests :: Test
tests = TestList
    -- Add your test cases to this list
    [ "testApplicationPlus" ~: testApplicationPlus,
      "testClass" ~: testClass ]

main :: IO ()
main = do
    result <- runTestTT tests
    print result
    if failures result > 0 then Exit.exitFailure else Exit.exitSuccess
