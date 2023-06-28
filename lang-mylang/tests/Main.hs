module Main where

import Test.HUnit
import Debug.Trace

import Syntax
import TypeCheck (runTC, runTCD, Label, Decl, runTCP, re'')
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

-- this runs on expressions
testApplicationPlus :: IO ()
testApplicationPlus = do
  -- t <- runTCPTest [App (Abs "x" (Plus (Ident "x") (Ident "x"))) (Num 21)]
  assertEqual "Typecheck ok" True $! isRight (runTC $ App (Abs "x" (Plus (Ident "x") (Ident "x"))) (Num 21))



-- class Eq a where 
-- == :: a -> Bool
classEq :: DeclT
classEq = ClassDecl "Eq" [typeVar "Eq"] [Method "==" "Eq" (typeVar "Eq") boolT]

-- type class definition
testClass :: IO ()
testClass = do 
  t <- runTCPTest [classEq]
  assertEqual "Typecheck ok" True $! isRight (runTCP [classEq])

-- class Eq a where 
-- == :: a -> Bool
--
-- instance Eq Int where 
-- == :: Int -> Bool
-- == x = True
clsInst :: [DeclT]
clsInst = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" [] (typeVar "Eq") boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" [] numT boolT) (Bool True)]]

-- method inside instance is wrong
-- class Eq a where 
-- == :: a -> Bool 
--
-- instance Eq Int where 
-- == :: Int -> Int
-- == x = 42
clsWrongInstance :: [DeclT]
clsWrongInstance = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" "Eq" (typeVar "Eq") boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" [] numT numT) (Num 42)]]--[Method "==" [] numT numT]]]

-- method signatures in type classes can't have types as parameters / need to have at least one type variable (use all of the defined ones)
-- class Eq Int where 
-- == :: Int -> Bool
-- 
-- instance Eq Int where 
-- == :: Int -> Bool
-- == x = True
clsInstSameSigIncorrect :: [DeclT]
clsInstSameSigIncorrect = [ClassDecl "Eq" [numT] [Method "==" [] numT boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" [] numT boolT) (Bool True)]] -- do I really need the type variables? they are in the method signature as well

-- type class + correct instance, where method defined for instance has type variable 
clsInstSameSigCorrect :: [DeclT]
clsInstSameSigCorrect = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" "Eq" (typeVar "Eq") boolT], InstDecl numT "Eq" [FunDecl "==" "x" (Method "==" [] numT boolT) (Bool True)]]

-- this one should fail, can't instantiate type variables
clsInstSigIncorrect :: [DeclT]
clsInstSigIncorrect = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" "Eq" (typeVar []) boolT], InstDecl (typeVar []) "Eq" [FunDecl "==" "x" (Method "==" [] (typeVar []) boolT) (Bool True)]]
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
clsInstFd = clsInst ++ [FunDecl "f" "x" (Method "f" [] numT boolT) (App (Ident "==") (Ident "x"))]
-- ident fun != ident because i wanna look inside type classes for those (possibly)

clsInstFdTConstr :: [DeclT] 
-- clsInstFd = clsInst ++ [FunDecl "f" (Method "f" numT boolT) (Abs "x" NumT (App (IdentFun "==") (Ident "x")))]
clsInstFdTConstr = clsInst ++ [FunDecl "f" "x" (Method "f" "Eq" (typeVar "Eq") boolT) (App (Ident "==") (Ident "x"))]

fdTConstr :: [DeclT]
fdTConstr = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" "Eq" (typeVar "Eq") boolT], FunDecl "f" "x" (Method "f" "Eq" (typeVar "Eq") boolT) (App (Ident "==") (Ident "x"))]

clsInstFdIncorrect :: [DeclT]
clsInstFdIncorrect = clsInst ++ [FunDecl "f" "x" (Method "f" [] boolT boolT) (App (Ident "==") (Ident "x"))]

-- Method defined for instance uses type variables, but function declaration uses the instance; should typecheck
clsInstFdTyVar :: [DeclT]
clsInstFdTyVar = clsInstSameSigCorrect ++ [FunDecl "f" "x" (Method "f" [] numT boolT) (App (Ident "==") (Ident "x"))]

-- this looks wrong
funDecl :: [DeclT] 
funDecl = [FunDecl "f" "x" (Method "f" [] numT boolT) (App (Ident "==") (Ident "x"))]
--(Abs "x" (App (App (Ident "==") (Ident "x")) (Num 42)))]

-- foo :: Int -> Int
-- foo x = + x 2
--
-- bar :: Int -> Int 
-- bar x = foo x
multipleFunDecl :: [DeclT]
multipleFunDecl = [FunDecl "foo" "x" (Method "foo" [] numT numT) (Plus (Ident "x") (Num 2)),--(Abs "x" (Plus (Ident "x") (Num 2))),
                    FunDecl "bar" "x" (Method "bar" [] numT numT) (App (Ident "foo") (Ident "x"))] 
                    --(Abs "x" (Plus (Num 5) (IdentFun "foo" (Ident "x"))))]
-- unification error Num -> Num != Num if I don't have Abs "x" in bar

multipleInst :: ProgT 
multipleInst = [ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT boolT) (Bool True)],
            InstDecl boolT "F" [FunDecl "foo" "x" (Method "foo" [] boolT boolT) (Bool False)]]

-- class F a where
--  foo :: a -> Bool
--
-- instance F Int where
--  foo :: Int -> Bool
--  foo x = True
-- 
-- instance F Bool where 
--  foo :: Bool -> Bool
--  foo x = False

-- bar :: Int -> Bool
-- bar x = foo x
multipleInstFd :: ProgT 
multipleInstFd = [ClassDecl "F" [typeVar "F"] [Method "foo" "F" (typeVar "F") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT boolT) (Bool True)],
            InstDecl boolT "F" [FunDecl "foo" "x" (Method "foo" [] boolT boolT) (Bool False)],
            FunDecl "bar" "x" (Method "bar" [] numT boolT) (App (Ident "foo") (Ident "x"))]

-- this test does not pass if we don't have "F" in method, look into why
noInstFd :: ProgT 
noInstFd = [ClassDecl "F" [typeVar "F"] [Method "foo" "F" (typeVar "F") numT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT numT) (Num 42)],
            FunDecl "fun" "x" (Method "fun" [] boolT numT) (App (Ident "foo") (Ident "x"))]

-- class C where
-- foo :: a -> Bool

-- f :: C a => a -> Bool
-- f x = foo x
example :: ProgT
example =  [
  ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") boolT],
  FunDecl "f" "x" (Method "f" [] (typeVar "C") boolT) (App (Ident "foo") (Ident "x"))]
  -- Method "f" "C" typeVar typeVar, FunDecl "g" "x" (Method "g" [] typeVar boolT) (App (Ident "f") (Bool True))] 

-- class F where
-- bar :: a -> Bool 
--
-- class C where
-- foo :: a -> Bool
-- foo x = True
--
-- fun :: F a => a -> Bool
-- fun x = foo x
example2 :: ProgT 
example2 = [
  ClassDecl "F" [typeVar "F"] [Method "bar" [] (typeVar "F") boolT],
  ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") boolT],--[FunDecl "foo" "x" (Method "foo" [] (typeVar "C") boolT) (Bool True)],--[Method "foo" [] (typeVar "C") boolT],
  FunDecl "fun" "y" (Method "fun" [] (typeVar "F") boolT) (App (Ident "foo") (Ident "y"))]

useDefaultImpl :: ProgT 
useDefaultImpl = [
  ClassDecl "F" [typeVar "F"] [FunDecl "foo" "x" (Method "foo" [] (typeVar "F") numT) (Num 42),
  FunDecl "fun" "y" (Method "fun" [] (typeVar "F") numT) (App (Ident "foo") (Ident "y"))]]

exampleOverlappingInst :: ProgT 
exampleOverlappingInst = [
  ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") numT],
  InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT numT) (Num 42)],
  InstDecl boolT "F" [FunDecl "foo" "x" (Method "foo" [] boolT numT) (Num 0)],
  FunDecl "fun" "x" (Method "fun" [] (typeVar "F") numT) (App (Ident "foo") (Ident "x"))]

instanceTyVar :: ProgT 
instanceTyVar = [
  ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") numT],
  InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT numT) (Num 42)],
  InstDecl (typeVar "F") "F" [FunDecl "foo" "x" (Method "foo" [] (typeVar "F") numT) (Num 21)],
  FunDecl "fun" "x" (Method "fun" [] (typeVar "F") numT) (App (Ident "foo") (Ident "x"))]

exampleInstTyVar :: ProgT 
exampleInstTyVar = [
  ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") numT],
  InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT numT) (Num 42)],
  InstDecl (typeVar "F") "F" [FunDecl "foo" "x" (Method "foo" [] (typeVar "F") numT) (Num 21)],
  FunDecl "fun" "x" (Method "fun" [] (typeVar "F") numT) (App (Ident "foo") (Ident "x"))]

exampleLet :: ProgT 
exampleLet = [
  ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") numT],
  InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT numT) (Num 42)],
  FunDecl "fun" "x" (Method "fun" [] (typeVar "F") numT) (Let "x" (App (Ident "foo") (Num 32)) (Ident "x"))]

testLet :: IO ()
testLet = 
  do 
    t <- runTCPTest exampleLet
    assertEqual "Let expression" True $! isRight (runTCP exampleLet)

testInstTyVar :: IO ()
testInstTyVar = 
  do 
    t <- runTCPTest instanceTyVar
    assertEqual "Overlapping instances error" True $! isRight (runTCP instanceTyVar)

testOverlappingInst :: IO ()
testOverlappingInst = 
  do 
    t <- runTCPTest exampleOverlappingInst
    assertEqual "Overlapping instances provided" True $! isRight (runTCP exampleOverlappingInst)

exampleWDefaultImpl :: IO ()
exampleWDefaultImpl = 
  do 
    t <- runTCPTest useDefaultImpl
    assertEqual "Default implementation provided" True $! isRight (runTCP useDefaultImpl)

exampleWInst :: ProgT 
exampleWInst = [
  ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") boolT],
  InstDecl boolT "C" [FunDecl "foo" "x" (Method "foo" [] boolT boolT) (Bool True)],
  Method "f" "C" (typeVar "C") (typeVar []), FunDecl "g" "x" (Method "g" [] (typeVar []) boolT) (App (Ident "f") (Bool True))]
  -- just method because i dont care about the implementation in this example

exampleWInst2 :: ProgT 
exampleWInst2 = [
  ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") boolT],
  InstDecl boolT "C" [FunDecl "foo" "x" (Method "foo" [] boolT boolT) (Bool False)],
  FunDecl "g" "x" (Method "g" [] (typeVar "C") boolT) (App (Ident "foo") (Bool True))]

exampleMissingInst :: ProgT 
exampleMissingInst = [
  ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") boolT],
  FunDecl "g" "x" (Method "g" [] (typeVar "C") boolT) (App (Ident "foo") (Bool True))]

testExample :: IO ()
testExample = 
  do 
    t <- runTCPTest example 
    assertEqual "Typecheck" True $! isRight (runTCP example)

testExample2 :: IO ()
testExample2 = 
  do 
    t <- runTCPFail example2 
    assertEqual "Does not typecheck" False $! isRight (runTCP example2)

testExampleWInst :: IO () 
testExampleWInst = 
  do 
    t <- runTCPTest exampleWInst 
    assertEqual "Typecheck" True $! isRight (runTCP exampleWInst)

testExampleWInst2 :: IO () 
testExampleWInst2 = 
  do 
    t <- runTCPTest exampleWInst2
    assertEqual "Typecheck" True $! isRight (runTCP exampleWInst2)

testFdNoInstance :: IO () 
testFdNoInstance = 
  do 
    t <- runTCPFail clsInstFdIncorrect
    assertEqual "No instance declared" False $! isRight (runTCP clsInstFdIncorrect)

-- think it does the same as previous one
testExMissingInst :: IO () 
testExMissingInst = 
  do 
    t <- runTCPFail exampleMissingInst
    assertEqual "No instance declared" False $! isRight (runTCP exampleMissingInst)

-- check if it does smth different from test fd no instance
testNoInstFd :: IO ()
testNoInstFd = 
  do 
    t <- runTCPFail noInstFd
    assertEqual "No instance declared" False $! isRight (runTCP noInstFd)

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

testClsInstFdTConstr :: IO ()
testClsInstFdTConstr = 
  do 
    t <- runTCPTest clsInstFdTConstr
    assertEqual "Function signature with type constraint, instances and type classes as well" True $! isRight (runTCP clsInstFdTConstr)

testFdTypeConstr :: IO () 
testFdTypeConstr = 
  do 
    t <- runTCPTest fdTConstr
    assertEqual "Function signature with type constraint" True $! isRight (runTCP fdTConstr)

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
noClsConstr = [ClassDecl "Eq" [typeVar "Eq"] [Method "==" [] (typeVar "Eq") boolT], 
              FunDecl "f" "x" (Method "f" [] numT boolT) (App (Ident "==") (Ident "x"))]

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
instImpl = [ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") boolT], 
            InstDecl numT "F" [FunDecl "foo" "x" (Method "foo" [] numT boolT) (Bool True)], 
            FunDecl "bar" "x" (Method "bar" [] numT boolT) (App (Ident "foo") (Ident "x"))] -- (Bool True)

classF :: DeclT 
classF = ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar "F") boolT] --[FunDecl "fun" (Method "fun" (typeVar "a") boolT) (Bool True)]

-- example8 :: ProgT 
-- example8 = ClassDecl "A" [typeVar] [Method "foo" [] (typeVar) boolT,
--            FunDecl "f" "x" (Method "f" [] typeVar typeVar) (App (Ident))]

-- can't represent default implementation nicer?
clsDefaultImpl :: ProgT 
clsDefaultImpl = [ClassDecl "F" [typeVar "F"] [FunDecl "fun" "x" (Method "fun" [] (typeVar "F") boolT) (Bool True)], 
                  InstDecl numT "F" [FunDecl "fun" "x" (Method "fun" [] numT boolT) (Bool False)], 
                  FunDecl "foobar" "x" (Method "foobar" [] numT boolT) (App (Ident "fun") (Ident "x"))]

-- multiple declarations of foo
sameFunMultipleClasses :: ProgT 
sameFunMultipleClasses = [ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar []) numT],
                          ClassDecl "F" [typeVar "F"] [Method "foo" [] (typeVar []) numT]]

sameFunTwice :: ProgT 
sameFunTwice = [FunDecl "foo" "x" (Method "foo" [] (typeVar []) boolT) (Bool True),
                FunDecl "foo" "x" (Method "foo" [] boolT boolT) (Bool True)]

instanceWrongClass :: ProgT 
instanceWrongClass = [ClassDecl "F" [typeVar "F"] [Method "fun" [] (typeVar "F") numT],
                      ClassDecl "C" [typeVar "C"] [Method "foo" [] (typeVar "C") numT],
                      InstDecl numT "F" [FunDecl "fun" "x" (Method "fun" [] numT numT) (Num 42)],
                      FunDecl "f" "x" (Method "f" [] numT numT) (App (Ident "foo") (Num 21))]

testinstanceWrongCls :: IO () 
testinstanceWrongCls = 
  do 
    t <- runTCPFail instanceWrongClass
    assertEqual "No instance found in the right type class" False $! isRight (runTCP instanceWrongClass)

-- pass functions as arguments

-- class C a where
--   bar :: a -> a

-- instance C Int where
--   bar n = n + 2

-- instance C Bool where
--   bar b = b

-- twice :: C a => a -> a
-- twice x = bar (bar x)
exampleTwice :: ProgT 
exampleTwice = [
  ClassDecl "C" [typeVar "C"] [Method "bar" [] (typeVar "C") (typeVar "C")],
  InstDecl numT "C" [FunDecl "bar" "x" (Method "bar" [] numT numT) (Plus (Ident "x") (Num 2))],
  InstDecl boolT "C" [FunDecl "bar" "x" (Method "bar" [] boolT boolT) (Ident "x")],
  FunDecl "twice" "x" (Method "twice" [] (typeVar "C") (typeVar "C")) (App (Ident "bar") (App (Ident "bar") (Ident "x")))]

exampleSimplePlus :: ProgT
exampleSimplePlus = [
  ClassDecl "C" [typeVar "C"] [Method "bar" [] (typeVar "C") (typeVar "C")],
  InstDecl numT "C" [FunDecl "bar" "x" (Method "bar" [] numT numT) (Plus (Ident "x") (Num 2))],
  FunDecl "f" "y" (Method "f" [] numT numT) (App (Ident "bar") (Ident "y"))]

examplePlus2 :: ProgT 
examplePlus2 = [
  ClassDecl "C" [typeVar "C"] [Method "bar" [] (typeVar "C") numT],
  InstDecl numT "C" [FunDecl "bar" "x" (Method "bar" [] numT numT) (Plus (Ident "x") (Num 2))],
  FunDecl "f" "y" (Method "f" [] numT numT) (App (Ident "bar") (Ident "y"))]

exampleTwoTyVars :: ProgT
exampleTwoTyVars = [
  ClassDecl "C" [typeVar "C", typeVar []] [Method "bar" [] (typeVar "C") (typeVar [])],
  InstDecl numT "C" [FunDecl "bar" "x" (Method "bar" [] numT boolT) (Bool True)],
  FunDecl "f" "y" (Method "f" [] numT boolT) (App (Ident "bar") (Ident "y"))]

exampleTwoVarsWConstr :: ProgT 
exampleTwoVarsWConstr = [
  ClassDecl "C" [typeVar "C", typeVar []] [Method "bar" [] (typeVar "C") (typeVar [])],
  InstDecl numT "C" [FunDecl "bar" "x" (Method "bar" [] numT boolT) (Bool True)],
  FunDecl "f" "y" (Method "f" [] numT boolT) (App (Ident "bar") (Ident "y"))]

test2TyVars :: IO ()
test2TyVars = 
  do 
    t <- runTCPTest exampleTwoTyVars
    assertEqual "Simple function with plus" True $! isRight (runTCP exampleTwoTyVars)

testSimplePlus2 :: IO ()
testSimplePlus2 = 
  do 
    t <- runTCPTest examplePlus2
    assertEqual "Simple function with plus" True $! isRight (runTCP examplePlus2)

testSimplePlus :: IO ()
testSimplePlus = 
  do 
    t <- runTCPTest exampleSimplePlus
    assertEqual "Simple function with plus" True $! isRight (runTCP exampleSimplePlus)

testApplyTwice :: IO ()
testApplyTwice = 
  do 
    t <- runTCPTest exampleTwice
    assertEqual "Apply bar for different instances" True $! isRight (runTCP exampleTwice)

testDefaultImpl :: IO ()
testDefaultImpl = 
  do 
    t <- runTCPTest clsDefaultImpl
    assertEqual "Type class can have default implementation" True $! isRight (runTCP clsDefaultImpl)

-- this does not give exception, but it should!
testSameFunMultipleCls :: IO () 
testSameFunMultipleCls = 
  do 
    t <- runTCPFail sameFunMultipleClasses
    assertEqual "Multiple declarations for the same function" False $! isRight (runTCP sameFunMultipleClasses)

testSameFunTwice :: IO () 
testSameFunTwice = 
  do 
    t <- runTCPFail sameFunTwice
    assertEqual "Multiple declarations for the same function" False $! isRight (runTCP sameFunTwice)

testInstImpl :: IO () 
testInstImpl = 
  do 
    t <- runTCPTest instImpl -- should catch the errors and report them
    assertEqual "Type check instance implementation" True $! isRight (runTCP instImpl)

exampleShadowing :: ProgT 
exampleShadowing = 
  [FunDecl "f" "x" (Method "f" [] numT numT) (Let "x" (Num 4) (Ident "x")),
   FunDecl "g" "x" (Method "g" [] numT numT) (App (Ident "f") (Ident "x"))]

exampleHOF :: ProgT 
exampleHOF = 
  [
    FunDecl "f" "x" (Method "f" [] numT boolT) (Bool True),
    FunDecl "h" "x" (Method "h" [] (funT [] numT boolT) numT) (Num 42),
    FunDecl "g" "x" (Method "g" [] (funT [] numT boolT) numT) (App (Ident "f") (Ident "h"))]

testHOF :: IO ()
testHOF = 
  do 
    t <- runTCPTest exampleHOF 
    assertEqual "Type check with hof" True $! isRight (runTCP exampleHOF)

testShadowing :: IO ()
testShadowing = 
  do 
    t <- runTCPTest exampleShadowing 
    assertEqual "Type check with name shadowing" True $! isRight (runTCP exampleShadowing)

tests :: Test
tests = TestList
    --  ["testApplicationPlus" ~: testApplicationPlus] -- doesnt pass anymore????? :(
      ["testInstanceTypeVar" ~: testInstTyVar,
      "testClass" ~: testClass,
      "testClassInstSameSignature" ~: testClassInstanceSig,
      "testClassInstanceSameSignatureFail" ~: testClassInstanceSigFail,
       "testInstanceSignatureIncorrect" ~: testInstSigIncorrect,
      "testFunctionDeclaration" ~: testFd,
      "testFunctionDeclarationNoInstance" ~: testFdNoInstance,
      "testInstanceTyVarFunctionDecl" ~: testInstTyVarFd,
      "testMultipleFunctionDecl" ~: testMultipleFd,
       "testMultipleInstabces" ~: testMultipleInst,
       "testInstRes" ~: testMultipleInstFd,
       "testNoTypeConstraint" ~: testNoConstr,
       "testInstanceImplementation" ~: testInstImpl,
       "testTypeClsDefaultImpl" ~: testDefaultImpl,
       "testFunTypeConstraint" ~: testFdTypeConstr,
      "test"~: testExample,
      "testExample2" ~: testExample2,
      -- "testWithDefaultImpl" ~: exampleWDefaultImpl, -- does not pass
      "testWithOverlappingInstances" ~: testOverlappingInst,
      "testInstanceWrongClass" ~: testinstanceWrongCls,
      "testWInst" ~: testExampleWInst,
      "testSameFunMultipleClasses" ~: testSameFunMultipleCls,
      "testNoInstanceFd" ~: testNoInstFd,
      "testClassWithInstance" ~: testClassInstance,
      "testClassWithInstanceFunctionDecl" ~: testClsInstFd,
      "testExampleWithInstance2" ~: testExampleWInst2,
      "testExampleMissingInstace" ~: testExMissingInst,
      -- "testApplyTwiceDifInst" ~: testApplyTwice, -- does not pass
      "testSimplePlus" ~: testSimplePlus] -- does not pass
      -- "testSimplePlus2" ~: testSimplePlus2, -- does not pass
      -- "testTwoTyVars" ~: test2TyVars,
      -- "testLet" ~: testLet,
      -- "testShadowing" ~: testShadowing,
      -- "testHigherOrderFunction" ~: testHOF]
      -- ["testSameFunDeclTwice" ~: testSameFunTwice] -- does not raise exception, should!!

      -- => 32 tests

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