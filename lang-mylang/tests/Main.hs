module Main where 

import Test.HUnit
import Debug.Trace

import Syntax
import TypeCheck (runTC, runTCD, Label, Decl)
import qualified System.Exit as Exit
import Free.Scope (Graph)

runTCTest :: Expr -> IO (Graph Label Decl, Ty) 
runTCTest = either assertFailure return . runTC

runTCDTest :: DeclT -> IO (Graph Label Decl, Ty)
runTCDTest = either assertFailure return . runTCD

-- Define your test cases like the following
testApplicationPlus :: IO ()
testApplicationPlus = do
  t <- runTCTest $ App (Abs "x" (Plus (Ident "x") (Ident "x"))) (Num 21)
  assertEqual "Incorrect type" numT $ snd t

classEq :: DeclT
classEq = ClassT "Eq" ["a"]
  [ VarT "==" (TypeScheme [] (toTy (FunT (TyVar "a") (FunT (TyVar "a") BoolT)))) ]

-- prog :: DeclT
-- prog = ClassT "Eq" ["a"] 
--           [ VarT "==" (TypeScheme [] (toTy(funT (TyVar "a") (funT (TyVar "a") boolT))))]
          -- TypeScheme [0] (funT (TyVar "a") (funT (TyVar "a") boolT))

testClass :: IO ()
testClass = do 
  t <- runTCDTest $ classEq 
  -- ClassT "Eq" ["a"] [Var "==" (Forall ["a", "a"] "Bool")]
  assertEqual "Typecheck not ok" (typeclsT "Eq") $ snd t

tests :: Test
tests = TestList
    -- Add your test cases to this list
    [ "testApplicationPlus" ~: testApplicationPlus,
       "testClass" ~: testClass ]

main :: IO ()
main = do
    result <- runTestTT tests
    print result
    if errors result > 0 || failures result > 0 then Exit.exitFailure else Exit.exitSuccess
