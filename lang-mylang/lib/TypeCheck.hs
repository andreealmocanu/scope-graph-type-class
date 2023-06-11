{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeCheck where 

import Data.Functor ( (<&>) )
import Data.Regex
import Data.Term 
import Free
import Free.Logic.Exists
import Free.Logic.Equals
import Free.Scope hiding (edge, new, sink)
import qualified Free.Scope as S (edge, new, sink)
import Free.Error
import Syntax
import qualified Data.Map as Map
import Debug.Trace
import Control.Exception (SomeException, try)
import Free.Logic.Generalize (instantiate, Generalize, hGeneralize)

-- import Control.Monad.Except (catchError)

----------------------------
-- Scope Graph Parameters --
----------------------------

data Label
  = P -- Lexical Parent Label
  | TC -- Type Class Label
  | I -- instance declaration
  | D -- Declaration
  | TyV 
  deriving (Show, Eq)

data Decl
  = Decl String Ty   -- Variable declaration
  | ClassD String Sc   -- Type Class declaration
  | InstD Ty Sc    -- Instance declaration
  | MethodSignature String Ty Ty -- name, parameter(s) and return type
  -- MethodSignature String [String] String
  | TypeVarD String    -- Type variable declaration
  deriving (Eq)


instance Show Decl where
  show (Decl x t) = x ++ " : " ++ show t
  show (ClassD name _) = "Typeclass " ++ name 
  show (InstD types _) = "Instance " ++ show types 
  show (MethodSignature name param ret) = "Method " ++ name ++ " :: " ++ show param ++ " -> " ++ show ret 
  show (TypeVarD vars) = "Typevariable " ++ vars

projTy :: Decl -> Ty
projTy (Decl _ t) = t
projTy (ClassD name _) = typeclsT name 
projTy (MethodSignature _ pty rty) = funT pty rty 
projTy (TypeVarD a) = typeVar a

-- Scope Graph Library Convenience
wildcard = Atom P `Pipe` Atom D

edge :: Scope Sc Label Decl < f => Sc -> Label -> Sc -> Free f ()
edge = S.edge @_ @Label @Decl

new :: Scope Sc Label Decl < f => Free f Sc
new = S.new @_ @Label @Decl

sink :: Scope Sc Label Decl < f => Sc -> Label -> Decl -> Free f ()
sink = S.sink @_ @Label @Decl

-- Regular expression P*D
re :: RE Label
re = Dot (Star $ Atom P) $ Atom D

-- Regular expression P*I?M
-- re' :: RE Label
-- re' = Dot (Dot (Star $ Atom P) (Pipe Empty $ Atom I)) $ Atom M

-- Regular expression for function declaration P*TC?D
re' :: RE Label 
re' = Dot (Dot (Star $ Atom P) (Pipe Empty $ Atom TC)) $ Atom D

-- P*I?D
re'' :: RE Label 
re'' = Dot (Dot (Star $ Atom P) (Pipe Empty $ Atom I)) $ Atom D

-- Path order based on length
pShortest :: PathOrder Label Decl
pShortest p1 p2 = lenRPath p1 < lenRPath p2

-- Match declaration with particular name
matchDecl :: String -> Decl -> Bool
matchDecl x (Decl x' _) = x == x'
matchDecl x (ClassD x' _) = x == x'
matchDecl x (MethodSignature x' _ _) = x == x' 
matchDecl x _ = False

matchDeclTy x f (MethodSignature x' p r) = x == x' && f == funT p r 
matchDeclTy x f _ = False
  -- res <- matchDeclTy' x f m
  -- return res 


matchDeclTy' x f (MethodSignature x' p r) 
  | x == x' = do 
    equals f (funT p r)
    return True 
  | otherwise = return False 

-- checkFunTy f fty = equals f fty

-- matchMethod :: String -> Ty -> Decl -> Bool 
-- matchMethod name f (MethodSignature x' pty rty) 
--   -- | name == x'= equals f funT pty rty
--   | name == x' = 
--     case checkFunTy f (funT pty rty) of 
--       Pure () -> True 
--       _ -> False 
-- matchMethod name _ _ = False
-- see if any tests actually need matchDecl for type var d or instance delcarations
-- matchDecl x (TypeVarD xs) = length [ x == y | y <- xs] == 1 --at least one of the type variable names match

-- matchMethod :: (Functor f, Error String < f, Equals Ty < f) => Ty -> [Ty] -> Free f () 
-- -- matchMethod m ((MethodSignature name pty rty):ms) = pure ()
-- matchMethod m [] = err $ "No declaration found for method  " ++ show m
-- matchMethod m (f:fs) = do equals m f `catchError` equalsH matchMethod m fs 

------------------
-- Type Checker --
------------------

-- Function that handles each language construct
tc :: ( Functor f
      -- List of 'capabilities' of type checker
      -- No need for inference: Disable parts related to first-order unification and generalization
      , Exists Ty < f                   -- Introduce new meta-variables
      , Equals Ty < f                   -- First-order unification
      , Error String < f                  -- Emit String errors
      , Scope Sc Label Decl < f           -- Scope graph operations
      )
   => Expr -> Sc -> Ty -> Free f ()

tc (Num _) _ t = equals t numT
tc (Bool _) _ t =  equals t boolT 
tc (Plus e1 e2) sc t = do
  equals t numT
  tc e1 sc numT 
  tc e2 sc numT
tc (App e1 e2) sc t = do --e1 is function, e2 argument
  s <- exists -- arg type
  argty <- inspect s
  trace ("\n FOR APP THE ARGUMENT TYPE IS " ++ show argty) $ return ()
  tc e1 sc (funT s t) --t
  tc e2 sc s 
tc (Abs x e) sc t = do
  s <- exists
  t' <- exists
  sc' <- new
  trace ("\n T FOR APPLICATION PLUS " ++ show t ++ "\n T' FOR APP PLUS " ++ show t') $ return ()
  edge sc' P sc
  sink sc' D (Decl x s)
  tc e sc' t' --typechecking e with t for FunDecl
  equals t (funT s t')
-- tc (Abs x e) sc t = do
--   s <- exists 
--   t' <- exists
--   sc' <- new 
--   edge sc' P sc
--   sink sc' D $ Decl x s
--   tc e sc' t
--   equals t (funT s t')
tc (Ident x) sc t = do
  -- ds <- query
  --         sc
  --         (Star (Atom P) `Dot` Atom D)
  --         (\ p1 p2 -> lenRPath p1 < lenRPath p2)
  --         (\ (Decl y _) -> x == y)
  ds <- query sc re'' pShortest (matchDecl x) <&> map projTy
  
  --err $ "No matching declarations found for " ++ show x
  -- look for function declarations inside type classes
  -- ds <- query
  --         sc
  --         (Star (Atom P) `Dot` Atom D)
  --         (\ p1 p2 -> lenRPath p1 < lenRPath p2)
  --         (\ (Decl y _) -> x == y)
  -- if length ds == 1
  --   then do
  --     dt <- instantiate @[Int] (projTy (head ds))
  --     equals t dt
  --   else if null ds
  --        then err $ "Query failed: unbound identifier " ++ x
  --        else err $ "Query yielded ambiguous binders for " ++ x
  case ds of
    []  ->  do 
      res <- query sc re'' pShortest (matchDeclTy x t) <&> map projTy 
      case res of
      -- no matching declaration found in the global scope, look inside typeclasses 
        [] -> err $ "No matching declaration found for " ++ show x ++ " for type " ++ show t
        [tyFun] -> do 
          trace ("\n Found for function " ++ x ++ " the type tyFun " ++ show tyFun ++ " but t given to tc is " ++ show t) $ return ()
          equals t tyFun 
        _ -> err "Multiple declarations inside type classes" 
    [tyId] -> do
      trace ("\n  NOW IT GETS HERE WITH TYID " ++ show tyId) $ return()
      -- do 
      -- dt <- instantiate @[Int] (projTy (head ds))
      equals t tyId --dt
    _   -> err $ "Multiple declarations found for " ++ show x
tc (IdentFun name arg) sc t = do 
  -- s <- exists -- arg type
  -- tc arg sc 
  -- aty <- inspect s
  -- matchDeclTy name t
  -- t is now funT pty rty
  -- tc e sc t
  ds <- query sc re' pShortest (matchDeclTy name t) <&> map projTy 
  case ds of
    -- no matching declaration found in the global scope, look inside typeclasses 
    [] -> err $ "No matching function declaration found for " ++ show name ++ " for type " ++ show t
      -- ts <- query sc re' pShortest (matchDecl name) <&> map projTy
      -- case ts of 
      --   [] -> err $ "No matching declaration found for " ++ show name ++ " inside typeclasses"
      --   [tyf] -> equals tyf t
      --   _ -> err $ "Multiple declarations found for " ++ show name
    [tyFun] -> do 
      trace ("\n Found for function " ++ name ++ " the type tyFun " ++ show tyFun ++ " but t given to tc is " ++ show t) $ return ()
      -- err $ "\n Found for function " ++ name ++ " the type " ++ show tyFun ++ " but t given to tc is " ++ show t
      equals t tyFun 
    -- decls -> matchMethod t decls
    _ -> err "Multiple declarations"
tc (Let name e body) sc t = do 
  s <- exists -- introduce new type variable? represents unknown types
  tc e sc s 
  st <- inspect s -- get inferred type of term represented by type variable s?
  -- ds <- query
  --         sc 
  --         (Star wildcard `Dot` Atom D)
  --         (\ p1 p2 -> lenRPath p1 < lenRPath p2)
  --         (\ (_ :: Decl) -> True)
  -- st' <- generalize (concatMap (\ (Decl _ t) -> fv t) ds) st 
  sc' <- new 
  edge sc' P sc 
  sink sc' D (Decl name st) -- with generalize, it was st'
  tc body sc' t 

-- lookupIdent :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> String -> Free f Ty
-- lookupIdent sc x = do
--   ds <- query sc re pShortest (matchDecl x)
--   case ds of 
--     [] -> err $ "Variable " ++ show x ++ " could not be resolved from scope " ++ show sc
--     [Decl _ ty] -> return ty
--     [MethodSignature _ pty rty] -> return (funT pty rty) 
--     _   -> err $ "Variable " ++ show x ++ " could not be resolved to a single variable "
-- lookupIdent _ _ = err "Lookup failed" 

-- create LHS here
createDecls :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> DeclT -> Free f (Sc, DeclT)
createDecls sc x@(Method name pty rty) = do
  sink sc D $ MethodSignature name pty rty
  return (sc, x)
createDecls sc x@(ClassDecl name vars methods) = do 
  s' <- new 
  sink sc D $ ClassD name s'
  edge s' P sc
  edge sc TC s'
  mapM_ (createDecls s') methods
  return (s', x)
createDecls sc x@(InstDecl ty className fs) = do 
  -- find scope of type class (if Inst is not nested inside of TypeClass)
  -- tc <- query sc re' pShortest (matchDecl name) -- should not query when I declare no?
  -- add declaration there
  -- case tc of 
    -- [ClassD _ tcSc] -> 
  -- add the method signatures in the scope graph of the type class
    
    s' <- new 
    edge s' P sc 
    edge sc I s'
    sink sc D $ InstD ty s' 
    mapM_ (createDecls s') fs
    return (s', x)  
    -- mapM_ (createDecls sc) (map (\(FunDecl fName (Method f p r) body) -> (Method f ty r)) fs)
    -- _ -> err $ "Typeclass " ++ show name ++ " not found"
createDecls sc x@(FunDecl name p (Method _ pty rty) def) = do
  s' <- new 
  edge s' P sc
  sink s' D $ Decl p pty
  sink sc D $ MethodSignature name pty rty 
  return (s', x)
  -- sink sc D $ Decl name (funT pty rty)
createDecls _ _ = err "Trying to create incorrect declaration"


-- declarations have expressions in them, some do; tc those...
tcDecls :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> DeclT -> Free f ()
tcDecls sc (ClassDecl name vars methods) = do 
  mapM_ (checkMetTypeClass sc) methods
tcDecls sc (InstDecl tys tclass methods) = do
  tc <- query sc re' pShortest (matchDecl tclass) 
  case tc of 
    [ClassD _ tcSc] -> do 
      checkMethodsCorrespond tcSc methods
      mapM_ (tcDecls sc) methods 
    _ -> err $ "Typeclass " ++ show tclass ++ " not found"
tcDecls sc (FunDecl name p (Method _ pty rty) def) = do 
  -- s <- exists
  -- t <- inspect s
  -- t <- funT pty rty 
  trace ("\n Type of function decl: " ++ name ++ show (funT pty rty)) $ return ()
  -- equals t (funT _ _)
  tc def sc rty --(funT pty rty)
tcDecls sc (Method name pty rty) = pure ()
tcDecls sc _ = do 
  err "Declaration not correct"

-- checkMethod :: DeclT -> Bool
-- checkMethod (Method _ (toTy (NumT)) _) = True
-- checkMethod _ = False

checkMetTypeClass :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> DeclT -> Free f () 
checkMetTypeClass sc (Method _ param _) = do 
  equals param (toTy $ TyVar "a")
  -- | otherwise = err $ "Typeclasses should have type variables but " ++ show param ++ " was given"
checkMetTypeClass sc m = tcDecls sc m


checkMethodsCorrespond :: (Functor f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> [DeclT] -> Free f ()
checkMethodsCorrespond _ [] = pure ()
-- checkMethodsCorrespond tcSc ((FunDecl _ _ (Method name ((typeVar a) ret) _):ms)) = pure ()
checkMethodsCorrespond tcSc ((FunDecl _ _ (Method name param ret) _):ms) = do 
  if param == toTy (TyVar "a") then err $ "Instances can't instantiate type variables" else pure() 
  m <- query tcSc re' pShortest (matchDecl name)
  case m of 
    [MethodSignature _ p r] -> do 
      equals r ret 
      checkMethodsCorrespond tcSc ms
    _ -> err $ "Method " ++ name ++ " not found inside type class scope"  
checkMethodsCorrespond _ x = err $ "Incorrect methods in instance declaration " ++ show x 

-- checkMethodsCorrespond [] [] = pure ()
-- checkMethodsCorrespond ((Method name1 _ r1):ms1) ((Method name2 p2 r2):ms2) = 
--   if r1 == toTy (TyVar "a")
--     then do
--       equals p2 r2 
--       checkMethodsCorrespond ms1 ms2 
--     else do
--       equals r1 r2
--       checkMethodsCorrespond ms1 ms2

-- checkMethodsCorrespond ((Method name1 p1 r1):ms1) ((Method name2 p2 r2):ms2) 
--   | name1 == name2 = do 
--     equals p1 p2 
--     equals r1 r2
--     checkMethodsCorrespond ms1 ms2
--   | otherwise = err $ "Types don't match for methods in instance declaration"


tcProg :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => ProgT -> Sc -> Free f ()
tcProg p sc = do 
    -- decls <- createDecls sc p
    -- mapM_ (\(scope, ty, expr) -> tc expr scope ty) decls
    s <- mapM (createDecls sc) p
    mapM_ (\(scope, decl) -> tcDecls scope decl) s 

  -- edge s' P s 
  -- sink s' D $ Decl name ty 
  -- t' <- tc e s'
  -- sink s' D $ Var name (Forall [] ty) -- add declaration for variable in scope
  -- t'' <- tc body s'
  -- return t''

-- tcClsInst :: ( Functor f
--       , Exists Ty < f                   -- Introduce new meta-variables
--       , Equals Ty < f                   -- First-order unification
--       , Generalize [Int] Ty < f         -- HM-style generalization
--       , Error String < f                  -- Emit String errors
--       , Scope Sc Label Decl < f           -- Scope graph operations
--       )
--    => DeclT -> Sc -> Ty -> Free f ()
-- tcClsInst (ClassT className typeParams decls) s t = do 
--   s' <- exists

--   classSc <- new 
--   -- add the class name to the scope
--   --sink s D $ ClassD className classSc 
--   sink s D $ ClassD className classSc
--   edge classSc P s 
--   -- still need edge between class declaration and class scope(?)
--   sink classSc D $ ClassD className classSc
--   sink classSc D $ TypeVarD typeParams --change label to TyV
  -- return (TyClass className)
-- tcClsInst (VarT name tScheme@(Forall paramTy returnTy)) s = do 
--   sink s D $ MethodSignature name paramTy returnTy 
--   return (TyVar "example")
-- tcClsInst _ s t = err "No matching declaration found"

-- Tie it all together
-- without generalize
runTC :: Expr -> Either String (Graph Label Decl) --Ty)
runTC e =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) Map.empty
        $ handle_ hExists (
          do t <- exists 
             tc e 0 t 
        :: Free ( Exists Ty 
                + Equals Ty 
                + Scope Sc Label Decl 
                + Error String 
                + Nop)
                ()
          ) 0
  in case x of 
    Left err -> Left err 
    Right (Left (UnificationError t1 t2), _)  -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, _), s)                   -> Right s 

-- runTC :: Expr -> Either String (Graph Label Decl)
-- runTC e =
--   let x = un
--         $ handle hErr
--         $ flip (handle_ hScope) emptyGraph
--         $ flip (handle_ hEquals) Map.empty
--         $ flip (handle_ hExists) 0
--         $ handle (hGeneralize fv schemeT genT)
--         (do t <- exists
--             tc e 0 t
--         :: Free ( Generalize [Int] Ty
--                 + Exists Ty
--                 + Equals Ty
--                 + Scope Sc Label Decl
--                 + Error String
--                 + Nop )
--                 () )
--   in case x of 
--      Left err -> Left err 
--      Right (Left (UnificationError t1 t2), _)  -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
--      Right (Right (_, _), s)                   -> Right s 

-- tcProg :: (Functor f, Exists Ty < f, Equals Ty < f, Generalize [Int] Ty < f, Error String < f, Scope Sc Label Decl < f) => ProgT -> Sc -> Free f ()


-- removed Ty from what it is returning:
-- used to be (Graph Label Decl, Ty)
runTCD :: DeclT -> Either String (Graph Label Decl)
runTCD decl =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) Map.empty
        $ handle_ hExists (tcProg [decl] 0
        :: Free ( Exists Ty 
                + Equals Ty 
                + Scope Sc Label Decl 
                + Error String 
                + Nop)
                ()
          ) 0
  in case x of 
    Left err -> Left err 
    Right (Left (UnificationError t1 t2), _)  -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, _), s)                   -> Right s
       

runTCP :: ProgT -> Either String (Graph Label Decl)
runTCP prog = 
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) Map.empty
        $ handle_ hExists (tcProg prog 0
        :: Free ( Exists Ty 
                + Equals Ty 
                + Scope Sc Label Decl 
                + Error String 
                + Nop)
                ()
          ) 0
  in case x of 
    Left err ->
      do  
      trace ("\n ERROR IS HERE!!!!!!!!!!!!!!!!!!!!!1 " ++ show err) $ return ()
      Left err

    Right (Left (UnificationError t1 t2), _)  -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, _), s)                   -> Right s

-- runTCP :: ProgT -> Either String (Graph Label Decl)
-- runTCP e =
--   let x = un
--         $ handle hErr
--         $ flip (handle_ hScope) emptyGraph
--         $ flip (handle_ hEquals) Map.empty
--         $ flip (handle_ hExists) 0
--         $ handle (hGeneralize fv schemeT genT)
--         (do t <- exists
--             tc e 0 t
--         :: Free ( Generalize [Int] Ty
--                 + Exists Ty
--                 + Equals Ty
--                 + Scope Sc Label Decl
--                 + Error String
--                 + Nop )
--                 () )
--   in case x of
--     Left s                                   -> Left s
--     Right (Left (UnificationError t1 t2), _) -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
--     Right (Right (_, u), sg)                  -> 
--       let t' = inspectVar u 0
--           vs = fv t'
--        in Right (sg, schemeT vs t')
--   where
--     genT t = do
--       t <- inspect t
--       case t of
--         Term "∀" ts -> 
--             let gens = init ts
--                 t' = last ts 
--             in do
--               substs <- mapM (\case
--                                 Const i -> do y <- exists; return (i,y)
--                                 _       -> err "Bad quantifier" 
--                              )
--                         gens
--               return $ substsIn substs t'
--         _ -> return t