{-# LANGUAGE FlexibleInstances #-} 

module Syntax where 

import Data.Term 
import Data.List (nub, (\\))

type Ty = Term Int

data Expr
  = Num Int -- number
  | Bool Bool -- boolean
  | Plus Expr Expr -- plus
  | App Expr Expr -- function application
  | Ident String -- identifier
  | Abs String Expr -- lambdas; param, (omitted) type, body
  | Let String Expr Expr 
  -- | IdentFun String Expr -- function declaration identifier; name of function to be applied and argument(s)
  -- let s be e1 in e2 
  -- let ((bounds)) body, where bounds: name, type, expr
  -- | If Expr Expr Expr -- if then else
  -- | ClassDecl String [(String, Type)] -- class name, list of method names and their types
  deriving (Eq, Show)

data DeclT = ClassDecl String [Ty] [DeclT] -- name, type variables, methods
      -- ClassT String [String] [DeclT]
      | InstDecl Ty String [DeclT] -- types that are instantiates, type class name 
       -- I don't need methods' implementation for now 
      -- used to be Ty as the typeclass, but do I really need a type class type?
      | Method String String Ty Ty -- method signature: name, changed to one (list of type constraints), param types (only one parameter for now), return type
      | FunDecl String String DeclT Expr -- function declaration: name, parameter, method signature, implementation
      -- VarT String TypeScheme
    deriving (Show, Eq)

data TypeScheme = TypeScheme [Int] Ty 
    deriving Eq

type ProgT = [DeclT]

toTy :: Type -> Ty
toTy NumT = numT
toTy BoolT = boolT
toTy (FunT c p t) = funT c (toTy p) (toTy t)
  -- funT param (toTy t)
  -- where 
  --   param = map toTy f
toTy (TyClass name) = typeclsT name
toTy (TyVar c) = typeVar c 

instance Show TypeScheme where
  show (TypeScheme [] t) = show t
  show (TypeScheme vars t) = "(∀ "
                      ++ unwords (map (\i' -> "α" ++ show i') vars) 
                      ++ ". " 
                      ++ show t
                      ++ ")"

sfv :: TypeScheme -> [Int]
sfv (TypeScheme vars t) = fv t \\ vars

instance Show Ty where
  show (Const i) = "α" ++ show i
  show (Var i) = "αVar" ++ show i
  -- show (Term "∀" ts) = "(∀ " ++ unwords (map show (init ts)) ++ ". " ++ show (last ts) ++ ")"
  show (Term "->" [c, t1, t2]) = show c ++ " " ++ show t1 ++ " -> " ++ show t2
  show (Term "Num" []) = "Num"
  show (Term "Bool" []) = "Bool"
  show (Term name []) = show name
  show (Term "TyVar" name) = "TyVar " ++ show name
  show _ = "undefined term "
  -- show (Term )
  -- show (Term f ts) = "(" ++ f ++ unwords (map show ts) ++ ")"

-- type construction
numT :: Term c
numT = Term "Num" []
boolT :: Term c
boolT = Term "Bool" []
funT :: [Char] -> Term c -> Term c -> Term c 
funT c p r = Term "->" [typeclsT c, p, r]
-- typeConstr :: [Char] -> Term c 
-- typeConstr typecls = Term typecls []
typeclsT :: [Char] -> Term c
typeclsT name = Term name []
-- add the constraint to the type variable
-- typeVar :: Int -> Term c
-- typeVar i = Var i
typeVar :: [Char] -> Term c
typeVar tycls = Term "TyVar" [typeclsT tycls]
-- typeVar :: Term c -> [Char] -> Term c
-- typeVar a name = Term "TyVar" [a]
schemeT :: [c] -> Term c -> Term c
schemeT xs t | not (null xs) = Term "∀" (map Const xs ++ [t])
             | otherwise = t

data Type = NumT
    | BoolT
    | FunT String Type Type -- constraint, parameter type, return type
    | TyVar String -- type variable 
    -- | TyCon String [Type] -- type constructor
    | TyClass String --[Type] -- type classes
    deriving (Eq, Show)

-- instance Eq Type where 
--   NumT == NumT = True 
--   BoolT == BoolT = True 
--   FunT a b == FunT x y = x == a && b == y 
--   TyClass a == TyClass b = a == b 
--   TyVar == _ = True 
--   _ == TyVar = True

-- Free variables
fv :: Term Int -> [Int]
fv (Const _) = []
fv (Var i) = [i]
fv (Term f ts) | f /= "∀" = nub $ concatMap fv ts
               | otherwise = let bs = concatMap c2fv (init ts)
                 in nub (fv (last ts) \\ bs)
  where
    c2fv (Const i) = [i]
    c2fv _ = []