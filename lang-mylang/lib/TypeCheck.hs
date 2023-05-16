module TypeCheck where 

import Data.Functor ( (<&>) )
import Data.Regex

import Free
import Free.Scope hiding (edge, new, sink)
import qualified Free.Scope as S (edge, new, sink)
import Free.Error
import Syntax
import Control.Monad
import Control.Applicative ((<|>))
import qualified Data.Map as Map

----------------------------
-- Scope Graph Parameters --
----------------------------

data Label
  = P -- Lexical Parent Label
  | TC -- Type Class Label
  | D -- Declaration
  | TyV 
  deriving (Show, Eq)

data Decl
  = Decl String Type   -- Variable declaration
  | ClassD String Sc   -- Type Class declaration
  | InstD [Type] Sc    -- Instance declaration
  | MethodSignature String [String] String -- name, parameters and return type
  | TypeVarD [String]    -- Type variable declaration
  deriving (Eq)


instance Show Decl where
  show (Decl x t) = x ++ " : " ++ show t

projTy :: Decl -> Type
projTy (Decl _ t) = t

-- Scope Graph Library Convenience
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

-- match a given Var with a given String and return the Var's type
-- matchVar :: DeclT -> String -> Maybe Type
-- matchVar (Var x t) s = if x == s then Just t else Nothing

-- extract the declaration from a given scope
-- projDecl :: Sc -> String -> Maybe Decl
-- projDecl s x = do
--   d <- proj s x
--   case d of
--     DeclT t -> Just $ Decl x t
--     _       -> Nothing

-- projDecl :: DeclT -> Maybe Decl
-- projDecl (Var _ _) = Nothing
-- projDecl (InsT _ _ decls) = foldr ((<|>) . projDecl) Nothing decls
-- projDecl (ClassT _ _ decls) = foldr ((<|>) . projDecl) Nothing decls

------------------
-- Type Checker --
------------------

-- Function that handles each language construct
tc :: ( Functor f
      -- List of 'capabilities' of type checker
      -- No need for inference: Disable parts related to first-order unification and generalization
      -- , Exists Type < f                   -- Introduce new meta-variables
      -- , Equals Type < f                   -- First-order unification
      -- , Generalize [Int] Type < f         -- HM-style generalization
      , Error String < f                  -- Emit String errors
      , Scope Sc Label Decl < f           -- Scope graph operations
      )
   => Expr -> Sc -> Free f Type

tc (Num _) _ = return NumT
tc (Bool _) _ = return BoolT 
tc (Plus e1 e2) sc = do
  t1 <- tc e1 sc
  t2 <- tc e2 sc
  case (t1, t2) of
    (NumT, NumT) -> return NumT
    (t1', NumT)  -> err $ "Expected left operand of plus expression to have type 'num', got '" ++ 
                          show t1' ++ "'"
    (NumT, t2')  -> err $ "Expected right operand of plus expression to have type 'num', got '" ++ 
                          show t2' ++ "'"
    (t1', t2')   -> err $ "Expected operands of plus expression to have type 'num', got '" ++ 
                          show t1' ++ "' and '" ++
                          show t2' ++ "'"
tc (App e1 e2) sc = do
  t1 <- tc e1 sc
  t2 <- tc e2 sc
  case t1 of
    (FunT t t') | t == t2 -> return t'
    (FunT t _)            -> err $ "Expected argument of type '" ++ show t ++ "' got '" ++ show t2 ++ "'"
    t                     -> err $ "Expected arrow type, got '" ++ show t ++ "'"
tc (Abs x t e) s = do
  s' <- new -- create new scope node
  edge s' P s
  sink s' D $ Decl x t
  t' <- tc e s'
  return $ FunT t t'
tc (Ident x) s = do
  ds <- query s re pShortest (matchDecl x) <&> map projTy
  case ds of
    []  -> err "No matching declarations found"
    [t] -> return t
    _   -> err "BUG: Multiple declarations found" -- cannot happen for STLC
tc (Let (name, ty, e) body) s = do 
  s' <- new 
  edge s' P s 
  sink s' D $ Decl name ty 
  tc e s' 
-- tc (Let (name, ty, e) body) s = do 
--   s' <- new 
--   edge s' P s 
--   sink s' D $ Decl name ty 
--   t' <- tc e s'
--   sink s' D $ Var name (Forall [] ty) -- add declaration for variable in scope
--   t'' <- tc body s'
--   return t''

tcClsInst :: ( Functor f
              , Error String < f
              , Scope Sc Label Decl < f
              )
            => DeclT -> Sc -> Free f Type 
tcClsInst (ClassT className typeParams decls) s = do 
  -- add new scope for the class
  classSc <- new 
  -- add the class name to the scope
  --sink s D $ ClassD className classSc 
  sink s D $ ClassD className classSc
  edge classSc P s 
  -- still need edge between class declaration and class scope(?)
  sink classSc D $ ClassD className classSc
  sink classSc D $ TypeVarD typeParams --change label to TyV
  return (TyClass className)
tcClsInst (Var name tScheme@(Forall paramTy returnTy)) s = do 
  sink s D $ MethodSignature name paramTy returnTy 
  return (TyVar "example")

tcClsInst _ s = err "No matching declaration found"

-- Tie it all together
runTC :: Expr -> Either String (Type, Graph Label Decl)
runTC e = un
        $ handle hErr
        $ handle_ hScope (tc e 0) emptyGraph

runTCD :: DeclT -> Either String (Type, Graph Label Decl)
runTCD decl = un 
        $ handle hErr 
        $ handle_ hScope (tcClsInst decl 0) emptyGraph


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
