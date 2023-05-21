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
  | Abs String Expr -- lambdas
  | Let String Expr Expr 
  -- let s be e1 in e2 
  -- let ((bounds)) body, where bounds: name, type, expr
  -- | If Expr Expr Expr -- if then else
  -- | ClassDecl String [(String, Type)] -- class name, list of method names and their types
  deriving (Eq, Show)

data DeclT = ClassT String [String] [DeclT] -- name, type variables, methods
      | InsT [Ty] Ty [DeclT] -- types that are instantiates, type class, methods
      | VarT String TypeScheme
    deriving (Show, Eq)

data TypeScheme = TypeScheme [Int] Ty 
    deriving Eq

type ProgT = [DeclT]

toTy :: Type -> Ty
toTy NumT = numT
toTy BoolT = boolT
toTy (FunT f t) = funT (toTy f) (toTy t)
toTy (TyClass name) = typeclsT name

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
  show (Var i) = "α" ++ show i
  -- show (Term "∀" ts) = "(∀ " ++ unwords (map show (init ts)) ++ ". " ++ show (last ts) ++ ")"
  show (Term "->" [t1, t2]) = show t1 ++ " -> " ++ show t2
  show (Term "Num" []) = "Num"
  show (Term "Bool" []) = "Bool"
  show (Term "TypeClass" []) = "TypeClass"
  show _ = "undefined term"
  -- show (Term )
  -- show (Term f ts) = "(" ++ f ++ unwords (map show ts) ++ ")"

-- type construction
numT = Term "Num" []
boolT = Term "Bool" []
funT p r = Term "->" [p, r]
typeclsT name = Term ("TypeClass" ++ name) []
schemeT xs t | not (null xs) = Term "∀" (map Const xs ++ [t])
             | otherwise = t

data Type = NumT
    | BoolT
    | FunT Type Type
    | TyVar String -- type variable 
    | TyCon String [Type] -- type constructor
    | TyClass String --[Type] -- type classes
    deriving (Eq, Show)

-- example :: Expr
-- example = App (Abs "x" NumT (Plus (Ident "x") (Ident "x"))) (Num 21)

-- example1 = ClassT "Eq" ["a"] [(Var "==") [TyVar "a", TyVar "a"] (TyCon "Bool"), 
--   DeclT (Var "/=") [TyVar "a", TyVar "a"] (TyCon "Bool") ])

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


-- example1 :: DeclT
-- example1 = ClassT "Eq" ["a"] 
--   [VarT "==" (Forall ["a", "a"] "Bool"),
--    VarT "/=" (Forall ["a", "a"] "Bool")]