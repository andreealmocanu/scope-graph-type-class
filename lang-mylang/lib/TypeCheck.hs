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
  | InstD Ty String Sc    -- Instance declaration: type, type class name, scope
  | MethodSignature String String Ty Ty -- name, type constraint, parameter(s) and return type
  deriving (Eq)


instance Show Decl where
  show (Decl x t) = x ++ " : " ++ show t
  show (ClassD name _) = "Typeclass " ++ name 
  show (InstD types _ _) = "Instance " ++ show types 
  show (MethodSignature name c param ret) = "Method " ++ name ++ " :: " ++ c ++ " => " ++ show param ++ " -> " ++ show ret 

projTy :: Decl -> Ty
projTy (Decl _ t) = t
projTy (ClassD name _) = typeclsT name 
projTy (MethodSignature name c pty rty) = funT c pty rty 
projTy (InstD t _ _) = t

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

-- Regular expression for function declaration P*TC?D
re' :: RE Label 
re' = Dot (Dot (Star $ Atom P) (Pipe Empty $ Atom TC)) $ Atom D

-- P*I?D
re'' :: RE Label 
-- re'' = Dot (Dot (Star $ Atom P) (Pipe Empty $ Atom I)) $ Atom D
re'' = Dot (Dot (Star $ Atom P) (Star $ Atom I)) $ Atom D
-- re'' = Dot (Star $ Atom P) $ Atom I

-- Path order based on length
pShortest :: PathOrder Label Decl
pShortest p1 p2 = lenRPath p1 < lenRPath p2

-- Match declaration with particular name
matchDecl :: String -> Decl -> Bool
matchDecl x (Decl x' _) = x == x'
matchDecl x (ClassD x' _) = x == x'
matchDecl x (MethodSignature x' _ _ _) = x == x' 
matchDecl _ _ =   False


matchInstance :: Ty -> Ty -> Decl -> Bool 
matchInstance ty (Term className []) (InstD t typeClass _) = t == ty && className == typeClass
matchInstance ty className _ = False


resolveInst argty typecls sc = do 
  res <- query sc re'' pShortest (matchInstance argty typecls) <&> map projTy
  case res of 
    [] -> -- there is no instance, check if the type constraint and type class correspond
      do
      cons <- query sc re' pShortest (matchInstance argty typecls) <&> map projTy 
      case cons of 
        [] -> err $ "No instance found for type " ++ show argty ++ " in typeclass " ++ show typecls
        [c] -> pure () -- ok 
        _ -> err $ "Multiple type classes match for one constraint"
    [inst] -> 
      trace ("\n It's been resolved to " ++ show inst ++ " for type class " ++ show typecls) $ return ()
      -- pure () 
    _ -> err $ "Multiple instances found for type " ++ show argty



substTv :: Term c -> Term c -> Term c
substTv x t = do 
  case t of 
    Term "->" list -> do  
      let newList = map fun list 
      Term "->" newList
      where 
        fun (Term "TyVar" []) = x; 
        fun y = y
    _ -> t 

compat :: (Functor f, Exists Ty < f, Equals Ty < f) => Ty -> Expr -> Free f ()
compat p a = do
  ta <- exists  
  equals p ta

getConstraint :: Term c -> Maybe (Term c) 
getConstraint fun = do 
  case fun of 
    Term "->" [c, Term "TyVar" [constr], r] -> Just constr
    _ -> Nothing 

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
tc (App f a) sc t = do 
  t' <- exists 
  ta <- exists 
  tc f sc t'
  tty <- inspect t' 
  x <- exists 
  let t'' = substTv x tty 
  trace ("\n t'' is " ++ show t'') $ return ()
  tc a sc ta
  taty <- inspect ta 
  let c = getConstraint t''
  trace ("\n type constraint-ul este " ++ show c) $ return ()
  case c of 
    Nothing -> return () -- no type constraint
    Just typeclass -> resolveInst taty typeclass sc -- handle constraint here
tc (Abs x e) sc t = do
  s <- exists
  t' <- exists
  tc e sc t' 
  equals t (funT [] s t')
tc (Ident x) sc t = do
  ds <- query sc re' pShortest (matchDecl x) <&> map projTy 
  case ds of
    []  ->  do 
        err $ "No matching declaration found for " ++ show x
    [f] -> do
      trace  ("\n T IS " ++ show t ++ " and F IS " ++ show f ++ " for x " ++ show x) $ return ()
      equals t f
    _   -> err $ "Multiple declarations found for " ++ show x
tc (Let name e body) sc t = do 
  s <- exists 
  tc e sc s 
  st <- inspect s 
  sc' <- new 
  edge sc' P sc 
  sink sc' D (Decl name st) 
  tc body sc' t 

-- create LHS here
createDecls :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> DeclT -> Free f (Sc, DeclT)
createDecls sc x@(Method name c pty rty) = do
  sink sc D $ MethodSignature name c pty rty
  return (sc, x)
createDecls sc x@(ClassDecl name vars methods) = do 
  s' <- new 
  sink sc D $ ClassD name s'
  -- careful, edit, only first vars taken now
  sink s' D $ InstD (head vars) name s'
  edge s' P sc
  edge sc TC s'
  mapM_ (createDecls s') methods
  return (s', x)
createDecls sc x@(InstDecl ty className fs) = do 
    s' <- new 
    edge s' P sc 
    edge sc I s'
    sink sc D $ InstD ty className s' 
    resfuns <- mapM (createDecls s') fs
    return (s', x)  
createDecls sc x@(FunDecl name p (Method _ c pty rty) def) = do
  s' <- new 
  edge s' P sc
  edge sc I s'
  sink s' D $ Decl p pty
  trace ("\n Declaration for y: " ++ show pty ++ " and p is" ++ show p) $ return ()
  sink sc D $ MethodSignature name c pty rty 
  return (s', x)
createDecls _ _ = err "Trying to create incorrect declaration"


tcDecls :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> DeclT -> Free f ()
tcDecls sc (ClassDecl name vars methods) = do 
  mapM_ (checkMetTypeClass name sc) methods
tcDecls sc (InstDecl tys tclass methods) = do
  tc <- query sc re' pShortest (matchDecl tclass) 
  case tc of 
    [ClassD _ tcSc] -> do 
      checkMethodsCorrespond tcSc methods
      mapM_ (tcDecls sc) methods 
    _ -> err $ "Typeclass " ++ show tclass ++ " not found"
tcDecls sc (FunDecl name p (Method _ c pty rty) def) = do  
  trace ("\n Type of function decl: " ++ name ++ " " ++ show (funT c pty rty)) $ return ()
  tc def sc rty
tcDecls sc (Method name tys pty rty) = pure ()
tcDecls sc _ = do 
  err "Declaration not correct"



checkMetTypeClass :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => String -> Sc -> DeclT -> Free f () 
checkMetTypeClass tycls _ (Method _ _ param _) = do 
  equals param (typeVar tycls)
checkMetTypeClass _ sc m = tcDecls sc m


checkMethodsCorrespond :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> [DeclT] -> Free f ()
checkMethodsCorrespond _ [] = pure ()
checkMethodsCorrespond tcSc ((FunDecl _ _ (Method name tys param ret) _):ms) = do 
  -- not general enough, this is just tyvar with no constraint!!
  if param == (Term "TyVar" []) then err $ "Instances can't instantiate type variables" else pure() 
  m <- query tcSc re' pShortest (matchDecl name)
  case m of 
    [MethodSignature _ _ p r] -> do 
      if r == (typeVar "C") then pure() else do 
        equals r ret 
      checkMethodsCorrespond tcSc ms
    _ -> err $ "Method " ++ name ++ " not found inside type class scope"  
checkMethodsCorrespond _ x = err $ "Incorrect methods in instance declaration " ++ show x 

tcProg :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => ProgT -> Sc -> Free f ()
tcProg p sc = do 
    s <- mapM (createDecls sc) p
    mapM_ (\(scope, decl) -> tcDecls scope decl) s 


-- Tie it all together
runTC :: Expr -> Either String (Graph Label Decl) 
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
      Left err

    Right (Left (UnificationError t1 t2), _)  -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, _), s)                   -> Right s