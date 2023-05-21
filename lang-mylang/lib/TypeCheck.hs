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
import Free.Logic.Generalize 
import Free.Logic.Equals
import Free.Scope hiding (edge, new, sink)
import qualified Free.Scope as S (edge, new, sink)
import Free.Error
import Syntax
import Control.Monad
import Control.Applicative ((<|>))
import qualified Data.Map as Map
import Data.Maybe

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
  | InstD [Type] Sc    -- Instance declaration
  | MethodSignature String [String] String -- name, parameters and return type
  | TypeVarD [String]    -- Type variable declaration
  deriving (Eq)


instance Show Decl where
  show (Decl x t) = x ++ " : " ++ show t

projTy :: Decl -> Ty
projTy (Decl _ t) = t

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

-- Path order based on length
pShortest :: PathOrder Label Decl
pShortest p1 p2 = lenRPath p1 < lenRPath p2

-- Match declaration with particular name
matchDecl :: String -> Decl -> Bool
matchDecl x (Decl x' _) = x == x'

------------------
-- Type Checker --
------------------

-- Function that handles each language construct
tc :: ( Functor f
      -- List of 'capabilities' of type checker
      -- No need for inference: Disable parts related to first-order unification and generalization
      , Exists Ty < f                   -- Introduce new meta-variables
      , Equals Ty < f                   -- First-order unification
      , Generalize [Int] Ty < f         -- HM-style generalization
      , Error String < f                  -- Emit String errors
      , Scope Sc Label Decl < f           -- Scope graph operations
      )
   => Expr -> Sc -> Ty -> Free f ()

tc (Num _) _ t = equals t numT
tc (Bool _) _ t = equals t boolT 
tc (Plus e1 e2) sc t = do
  equals t numT
  tc e1 sc numT 
  tc e2 sc numT
tc (App e1 e2) sc t = do --e1 is function, e2 argument
  s <- exists -- arg type
  tc e1 sc (funT s t)
  tc e2 sc s
tc (Abs x e) sc t = do
  s <- exists 
  t' <- exists
  sc' <- new 
  edge sc' P sc
  sink sc' D $ Decl x s
  tc e sc' t' 
  equals t (funT s t')
tc (Ident x) sc t = do
  ds <- query 
          sc 
          (Star (Atom P) `Dot` Atom D)
          (\ p1 p2 -> lenRPath p1 < lenRPath p2)
          (\ (Decl y _) -> x == y) 
  if length ds == 1 
    then do 
      dt <- instantiate @[Int] (projTy (head ds))
      equals t dt 
    else if null ds 
        then err $ "Query failed: unbound identifier " ++ x 
        else err $ "Query yielded ambiguous binders for " ++ x 
  -- query s re pShortest (matchDecl x) <&> map projTy
tc (Let name e body) sc t = do 
  s <- exists -- introduce new type variable? represents unknown types
  tc e sc s 
  st <- inspect s -- get inferred type of term represented by type variable s?
  ds <- query
          sc 
          (Star wildcard `Dot` Atom D)
          (\ p1 p2 -> lenRPath p1 < lenRPath p2)
          (\ (_ :: Decl) -> True)
  st' <- generalize (concatMap (\ (Decl _ t) -> fv t) ds) st 
  sc' <- new 
  edge sc' P sc 
  sink sc' D (Decl name st')
  tc body sc' t  

-- create LHS here
createDecls :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => Sc -> [DeclT] -> Free f [(Sc, Ty, Expr)]
createDecls sc decls = do 
  do catMaybes <$> mapM (create sc) decls
  where
    create sc (VarT name typeSch) = do
      t <- exists
      sink sc D $ Decl name t
      return $ Just (sc, t, name)
    create sc (ClassT name vars methods) = do 
      t <- exists 
      s' <- new 
      sink sc D $ ClassD name s'
      edge sc P s'
      return $ Just (sc, t, methods) 
    create _ _ = return Nothing

tcProg :: (Functor f, Exists Ty < f, Equals Ty < f, Error String < f, Scope Sc Label Decl < f) => ProgT -> Sc -> Free f ()
tcProg p sc = do 
  decls <- createDecls 
  mapM_ (\(scope, ty, expr) -> tc expr scope ty) decls

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
runTC :: Expr -> Either String (Graph Label Decl, Ty)
runTC e =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) Map.empty
        $ flip (handle_ hExists) 0
        $ handle (hGeneralize fv schemeT genT)
        (do t <- exists
            tc e 0 t
        :: Free ( Generalize [Int] Ty
                + Exists Ty
                + Equals Ty
                + Scope Sc Label Decl
                + Error String
                + Nop )
                () )
  in case x of
    Left s                                   -> Left s
    Right (Left (UnificationError t1 t2), _) -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, u), sg)                  -> 
      let t' = inspectVar u 0
          vs = fv t'
       in Right (sg, schemeT vs t')
  where
    genT t = do
      t <- inspect t
      case t of
        Term "∀" ts -> 
            let gens = init ts
                t' = last ts 
            in do
              substs <- mapM (\case
                                Const i -> do y <- exists; return (i,y)
                                _       -> err "Bad quantifier" 
                             )
                        gens
              return $ substsIn substs t'
        _ -> return t

runTCD :: DeclT -> Either String (Graph Label Decl, Ty)
runTCD decl =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) Map.empty
        $ flip (handle_ hExists) 0
        $ handle (hGeneralize fv schemeT genT)
        (do t <- exists
            tcClsInst decl 0 t
        :: Free ( Generalize [Int] Ty
                + Exists Ty
                + Equals Ty
                + Scope Sc Label Decl
                + Error String
                + Nop )
                () )
  in case x of
    Left s                                   -> Left s
    Right (Left (UnificationError t1 t2), _) -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, u), sg)                  -> 
      let t' = inspectVar u 0
          vs = fv t'
       in Right (sg, schemeT vs t')
  where
    genT t = do
      t <- inspect t
      case t of
        Term "∀" ts -> 
            let gens = init ts
                t' = last ts 
            in do
              substs <- mapM (\case
                                Const i -> do y <- exists; return (i,y)
                                _       -> err "Bad quantifier" 
                             )
                        gens
              return $ substsIn substs t'
        _ -> return t


-- Var className $ Forall (map TyVar typeParams) (TyClass className (map TyVar typeParams))
  -- sink classSc D (Decl className (TyClass className varTypes))
  -- type check all the declarations inside the class
  --mapM_ (\decl -> tcClsInst decl classSc) decls 

  -- tcClsInst (InsT typeArgs (TyCon className ty) decls) s = do
--   -- look up the class name in the scope
--   classDecl <- query s re pShortest (matchDecl className) 
--   case classDecl of
--     (Var _ (Forall typeParams (TyClass _ classArgs))) ->
--       -- check that the number of type arguments matches
--       if (length typeArgs /= length classArgs) then 
--         err $ "Expected " ++ show (length classArgs) ++ " type arguments, got " ++ show (length typeArgs)
--         else 
--       -- create a new scope node for the instance 
--         do 
--         s' <- new
--       -- add the type arguments to the scope
--         -- forM_ (zip typeParams typeArgs) $ \(typeParam, typeArg) ->
--         --   sink s' D $ Var typeParam $ Forall [] typeArg
--         forM_ (zip typeParams typeArgs) $ \(typeParam, typeArg) ->
--           sink s' D $ InstD typeArgs s'
--           --DeclT $ Var typeParam $ Forall [] typeArg
--       -- type check all the declarations inside the instance
--         mapM_ (\decl -> tcClsInst decl s') decls
--     _ -> err $ "'" ++ show className ++ "' is not a type class"
--   -- -> err $ "Type class '" ++ show className ++ "' not in scope"

-- tcTypeClassesInstances decls sc = mapM_ tcDecl decls
--   where
--     tcDecl (ClassT className varNames decls') = do
--       -- create a new scope node for the class and add it to the scope graph
--       classNode <- new
--       sink classNode D (Decl className TyClass)
--       -- typecheck the declarations in the class, using the class scope
--       let classScope = modifyScope (\s -> extendScope classNode s) sc
--       mapM_ (tcDeclWithScope classScope) decls'
--     tcDecl (InsT typeArgs className decls') = do
--       -- look up the class declaration
--       classDecls <- query sc re pShortest (matchDecl className)
--       case classDecls of
--         -- [Var _ (Forall varNames (FunT (FunT classArg (TyVar _)) classRes))] -> do 
--         [Var _ (Forall varNames (classType _))] -> do
--           -- create a new scope node for the instance and add it to the scope graph
--           instanceNode <- new
--           sink instanceNode D (Decl className (instanceType typeArgs varNames))
--           -- typecheck the declarations in the instance, using the instance scope
--           let instanceScope = modifyScope (\s -> extendScope instanceNode s) sc
--           mapM_ (tcDeclWithScope instanceScope) decls'
--         _ -> err $ "No class declaration found for instance " ++ className
--     tcDecl (Var _ _) = return () -- ignore Var declarations
--     -- typecheck a declaration with a given scope
--     tcDeclWithScope scope (Var _ (Forall varNames ty)) =
--       sink scope D (Decl "_" (instantiate ty varNames))
--     -- helper functions for building type constructors for classes and instances
--     classType varNames = foldr FunT (TyCon className (map TyVar varNames))
--     instanceType typeArgs varNames = foldr FunT (TyCon className (map TyVar varNames ++ typeArgs))
--     -- instantiate a type scheme with a list of type variables
--     instantiate (Forall vs t) ts = substTypeVars (zip vs ts) t
--     -- substitute type variables in a type expression
--     substTypeVars substs (TyVar name) = fromMaybe (TyVar name) (lookup name substs)
--     substTypeVars substs (FunT t1 t2) = FunT (substTypeVars substs t1) (substTypeVars substs t2)
--     substTypeVars substs (TyCon name t) = TyCon name (substTypeVars substs t)
--     -- modified tc function that only checks identifier references
--     tcIdent :: String -> Sc -> Free f Type
--     tcIdent x s = do
--       ds <- query s re pShortest (matchDecl x) <&> map projTy
--       case ds of
--         []  -> err "No matching declarations found"
--         [t] -> return t
--         _   -> err "BUG: Multiple declarations found" 
