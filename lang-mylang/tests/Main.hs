module Main where

import Test.HUnit
import Debug.Trace

import Syntax
import TypeCheck (runTC, runTCD, Label, Decl, runTCP)
import qualified System.Exit as Exit
import Free.Scope (Graph)
import Free.Logic.Equals (inspectVar)
import Data.Either
import Data.Term

runTCTest :: Expr -> IO (Graph Label Decl) --, Ty) 
runTCTest = either assertFailure return . runTC

runTCDTest :: DeclT -> IO (Graph Label Decl)
runTCDTest = either assertFailure return . runTCD

runTCPTest :: ProgT -> IO (Graph Label Decl)
runTCPTest = either assertFailure return . runTCP

runTCPFail :: ProgT -> IO String
runTCPFail p = either return (const $ assertFailure "Expected exception, got none") $ runTCP p

testApplicationPlus :: IO ()
testApplicationPlus = do
  assertEqual "Typecheck ok" True $! isRight (runTC $ App (Abs "x" (Plus (Ident "x") (Ident "x"))) (Num 21))

-- changed because for now method has only one parameter
classEq :: DeclT
classEq = ClassDecl "Eq" [typeVar "a"] [Method "==" (typeVar "a") boolT]

-- type class definition
testClass :: IO ()
testClass = do 
  t <- runTCPTest [classEq]
  assertEqual "Typecheck ok" True $! isRight (runTCP [classEq])

-- type class + correct instance
clsInst :: [DeclT]
-- classEq ++ [InstDecl]
clsInst = [ClassDecl "Eq" [typeVar"a"] [Method "==" (typeVar "a") boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" numT boolT) (Bool True)]]

-- method inside instance is wrong
clsWrongInstance :: [DeclT]
clsWrongInstance = [ClassDecl "Eq" [typeVar"a"] [Method "==" (typeVar "a") boolT, InstDecl numT "Eq" [Method "==" numT numT]]]

-- method signatures in type classes can't have types as parameters / need to have at least one type variable (use all of the defined ones)
clsInstSameSigIncorrect :: [DeclT]
clsInstSameSigIncorrect = [ClassDecl "Eq" [numT] [Method "==" numT boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" numT boolT) (Bool True)]] -- do I really need the type variables? they are in the method signature as well

-- type class + correct instance, where method defined for instance has type variable 
clsInstSameSigCorrect :: [DeclT]
clsInstSameSigCorrect = [ClassDecl "Eq" [typeVar "a"] [Method "==" (typeVar "a") boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" numT boolT) (Bool True)]]

-- this one should fail, can't instantiate type variables
clsInstSigIncorrect :: [DeclT]
clsInstSigIncorrect = [ClassDecl "Eq" [typeVar "a"] [Method "==" (typeVar "a") boolT], InstDecl (typeVar "a") "Eq" [FunDecl "==" "x" (Method "==" (typeVar "a") boolT) (Bool True)]]
-- (typeVar "a") "Eq" [Method "==" (typeVar "a") boolT]]]

-- type class + correct instance
testClassInstance :: IO () 
testClassInstance =
  do
  t <- runTCPTest clsInst
  assertEqual "Typecheck ok" True $! isRight (runTCP clsInst) 

-- method signatures in type classes can't have types as parameters / need to have at least one type variable (use all of the defined ones)
testClassInstanceSigFail :: IO () 
testClassInstanceSigFail = do 
  t <- runTCPFail clsInstSameSigIncorrect
  assertEqual "Type classes need to be defined for type variables" False $! isRight (runTCP clsInstSameSigIncorrect)
  -- assertFailure "Typeclasses should have type variables"

-- method inside instance is wrong
testClassWrongInstance :: IO () 
testClassWrongInstance = do 
  t <- runTCPFail clsWrongInstance
  assertEqual "Method defined in instance needs to have signature compatible to the type class" False $! isRight (runTCP clsWrongInstance)

-- type class + correct instance, where method defined for instance has type variable 
testClassInstanceSig :: IO () 
testClassInstanceSig = do 
  t <- runTCPTest clsInstSameSigCorrect
  assertEqual "Method signature defined for an instance can have type variables" True $! isRight (runTCP clsInstSameSigCorrect)

-- this one should fail, can't instantiate type variables
testInstSigIncorrect :: IO ()
testInstSigIncorrect = do 
  t <- runTCPFail clsInstSigIncorrect
  assertEqual "Can't instantiate type variables" False $! isRight (runTCP clsInstSigIncorrect)

clsInstFd :: [DeclT] 
-- clsInstFd = clsInst ++ [FunDecl "f" (Method "f" numT boolT) (Abs "x" NumT (App (IdentFun "==") (Ident "x")))]
clsInstFd = clsInst ++ [FunDecl "f" "x" (Method "f" numT boolT) (App (Ident "==") (Ident "x"))]
-- ident fun != ident because i wanna look inside type classes for those (possibly)

clsInstFdIncorrect :: [DeclT]
clsInstFdIncorrect = clsInst ++ [FunDecl "f" "x" (Method "f" boolT boolT) (App (Ident "==") (Ident "x"))]

-- Method defined for instance uses type variables, but function declaration uses the instance; should typecheck
clsInstFdTyVar :: [DeclT]
clsInstFdTyVar = clsInstSameSigCorrect ++ [FunDecl "f" "x" (Method "f" numT boolT) (App (Ident "==") (Ident "x"))]

-- this looks wrong
funDecl :: [DeclT] 
funDecl = [FunDecl "f" "x" (Method "f" numT boolT) (App (Ident "==") (Ident "x"))]
--(Abs "x" (App (App (Ident "==") (Ident "x")) (Num 42)))]

-- foo :: Int -> Int
-- foo x = + x 2
--
-- bar :: Int -> Int 
-- bar x = foo x
multipleFunDecl :: [DeclT]
multipleFunDecl = [FunDecl "foo" "x" (Method "foo" numT numT) (Plus (Ident "x") (Num 2)),--(Abs "x" (Plus (Ident "x") (Num 2))),
                    FunDecl "bar" "x" (Method "bar" numT numT) (App (Ident "foo") (Ident "x"))] 
                    --(Abs "x" (Plus (Num 5) (IdentFun "foo" (Ident "x"))))]
-- unification error Num -> Num != Num if I don't have Abs "x" in bar

multipleInst :: ProgT 
multipleInst = [ClassDecl "F" [typeVar "a"] [Method "foo" (typeVar "a") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" numT boolT) (Bool True)],
            InstDecl boolT "F" [FunDecl "foo" "x" (Method "foo" boolT boolT) (Bool False)]]

multipleInstFd :: ProgT 
multipleInstFd = [ClassDecl "F" [typeVar "a"] [Method "foo" (typeVar "a") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" numT boolT) (Bool True)],
            InstDecl boolT "F" [FunDecl "foo" "x" (Method "foo" boolT boolT) (Bool False)],
            FunDecl "foo" "x" (Method "foo" numT numT) (App (Ident "foo") (Ident "x"))]

testFdNoInstance :: IO () 
testFdNoInstance = 
  do 
    t <- runTCPFail clsInstFdIncorrect
    assertEqual "Typecheck ok" False $! isRight (runTCP clsInstFdIncorrect)

-- Method defined for instance uses type variables, but function declaration uses the instance; should typecheck
testInstTyVarFd :: IO ()
testInstTyVarFd = 
  do 
    t <- runTCPTest clsInstFdTyVar 
    assertEqual "Methods inside instances can use type variables" True $! isRight (runTCP clsInstFdTyVar)

testMultipleInst :: IO () 
testMultipleInst = 
  do 
    t <- runTCPTest multipleInst
    assertEqual "Type classes can have multiple instances" True $! isRight (runTCP multipleInst)

testMultipleInstFd :: IO () 
testMultipleInstFd = 
  do 
    t <- runTCPTest multipleInstFd
    assertEqual "Instance resolution basic" True $! isRight (runTCP multipleInstFd)

-- no matching declaration found
testFd :: IO ()
testFd = 
  do 
    t <- runTCPFail funDecl 
    assertEqual "Typecheck ok" False $! isRight (runTCP funDecl)

testClsInstFd :: IO ()
testClsInstFd =  
  -- assertEqual "Typecheck ok" True $! isRight (runTCP $ clsInstFd)  
  do
  t <- runTCPTest clsInstFd
  assertEqual "Typecheck ok" True $! isRight (runTCP clsInstFd) 

testMultipleFd :: IO ()
testMultipleFd = 
  do 
    t <- runTCPTest multipleFunDecl
    assertEqual "Multiple function declarations" True $! isRight (runTCP multipleFunDecl)


-- try representing all functons as FunDecl with no implementation and just method signature?
noClsConstr :: ProgT 
noClsConstr = [ClassDecl "Eq" [typeVar "a"] [Method "==" (typeVar "a") boolT], 
              FunDecl "f" "x" (Method "f" numT boolT) (App (Ident "==") (Ident "x"))]

testNoConstr :: IO ()
testNoConstr = 
  do 
    t <- runTCPFail noClsConstr 
    assertEqual "No instance Num of Eq" False $! isRight (runTCP noClsConstr)

-- class F a where 
--   foo :: a -> Bool 

-- instance F Int where 
--   foo :: Int -> Bool 
--   foo x = True -- implementation has to be given for instances

-- bar :: Int -> Bool 
-- bar x = foo x
instImpl :: ProgT 
instImpl = [ClassDecl "F" [typeVar "a"] [Method "foo" (typeVar "a") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" numT boolT) (Bool True)], 
            FunDecl "bar" "x" (Method "bar" numT boolT) (App (Ident "foo") (Ident "x"))] -- (Bool True)

classF :: DeclT 
classF = ClassDecl "F" [typeVar "a"] [Method "foo" (typeVar "a") boolT] --[FunDecl "fun" (Method "fun" (typeVar "a") boolT) (Bool True)]

-- can't represent default implementation nicer?
clsDefaultImpl :: ProgT 
clsDefaultImpl = [ClassDecl "F" [typeVar "a"] [FunDecl "fun" "x" (Method "fun" (typeVar "a") boolT) (Bool True)], 
                  InstDecl numT "F" [FunDecl "fun" "x" (Method "fun" numT boolT) (Bool False)], 
                  FunDecl "foobar" "x" (Method "foobar" numT boolT) (App (Ident "fun") (Ident "x"))]

testDefaultImpl :: IO ()
testDefaultImpl = 
  do 
    t <- runTCPTest clsDefaultImpl
    assertEqual "Type class can have default implementation" True $! isRight (runTCP clsDefaultImpl)

testInstImpl :: IO () 
testInstImpl = 
  do 
    t <- runTCPTest instImpl -- should catch the errors and report them
    assertEqual "Type check instance implementation" True $! isRight (runTCP instImpl)

tests :: Test
tests = TestList
    -- -- Add your test cases to this list
    [ "testApplicationPlus" ~: testApplicationPlus,
       "testClass" ~: testClass,
       "testClassInstSameSignature" ~: testClassInstanceSig,
       "testClassInstanceSameSignatureFail" ~: testClassInstanceSigFail,
       "testInstanceSignatureIncorrect" ~: testInstSigIncorrect,
       "testClassWithInstance" ~: testClassInstance,
       "testClassWithInstanceFunctionDecl" ~: testClsInstFd,
       "testFunctionDeclaration" ~: testFd,
       "testFunctionDeclarationNoInstance" ~: testFdNoInstance,
       "testInstanceTyVarFunctionDecl" ~: testInstTyVarFd,
       "testMultipleFunctionDecl" ~: testMultipleFd, -- THIS ONE DOES NOT PASS YET!
       "testMultipleInstabces" ~: testMultipleInst, 
       "testInstRes" ~: testMultipleInstFd,
       "testNoTypeConstraint" ~: testNoConstr,
       "testInstanceImplementation" ~: testInstImpl,
       "testTypeClsDefaultImpl" ~: testDefaultImpl]

main :: IO ()
main = do
    result <- runTestTT tests
    print result
    if errors result > 0 || failures result > 0 then Exit.exitFailure else Exit.exitSuccess

-- classEq = ClassDecl "Eq" [typeVar "a"] [Method "==" [typeVar "a", typeVar "a"] boolT]

-- classEq = ClassT "Eq" ["a"]
--   [ VarT "==" (TypeScheme [] (toTy (FunT (TyVar "a") (FunT (TyVar "a") BoolT)))) ]

-- prog :: DeclT
-- prog = ClassT "Eq" ["a"] 
--           [ VarT "==" (TypeScheme [] (toTy(funT (TyVar "a") (funT (TyVar "a") boolT))))]
          -- TypeScheme [0] (funT (TyVar "a") (funT (TyVar "a") boolT))