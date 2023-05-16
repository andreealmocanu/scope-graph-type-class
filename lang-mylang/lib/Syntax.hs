module Syntax where 

data Type
  = NumT
  | BoolT
  | FunT Type Type
  | TyVar String -- type variable 
  | TyCon String [Type] -- type constructor
  | TyClass String --[Type] -- type classes
  deriving Eq
-- To use inference, replace `Type` with
-- type Ty = Term Int
-- (Term imported from Data.Term)
-- See also `lang-hm/Syntax` for an example.

data Expr
  = Num Int -- number
  | Bool Bool -- boolean
  | Plus Expr Expr -- plus
  | App Expr Expr -- function application
  | Ident String -- identifier
  | Abs String Type Expr -- lambdas
  | Let (String, Type, Expr) Expr -- let ((bounds)) body, where bounds: name, type, expr
  -- | If Expr Expr Expr -- if then else
  -- | ClassDecl String [(String, Type)] -- class name, list of method names and their types
  deriving (Eq, Show)

data DeclT = ClassT String [String] [DeclT] -- name, type variables, methods
      | InsT [Type] Type [DeclT] -- types that are instantiates, type class, methods
      | Var String TypeScheme
    deriving (Show, Eq)

-- newtype TypeVar = TypeVar String -- use newtype instead of data recommended 
--     deriving (Show, Eq)

data TypeScheme = Forall [String] String
    deriving (Eq, Show)

instance Show Type where
  show NumT = "num"
  show BoolT = "bool"
  show (TyVar tv) = "α" ++ tv
  show (TyCon name ty) = name ++ show ty   
  show (FunT ti to) = "(" ++ show ti ++ " -> " ++ show to ++ ")"

example :: Expr
example = App (Abs "x" NumT (Plus (Ident "x") (Ident "x"))) (Num 21)

-- example1 = ClassT "Eq" ["a"] [(Var "==") [TyVar "a", TyVar "a"] (TyCon "Bool"), 
--   DeclT (Var "/=") [TyVar "a", TyVar "a"] (TyCon "Bool") ])

example1 :: DeclT
example1 = ClassT "Eq" ["a"] 
  [Var "==" (Forall ["a", "a"] "Bool"),
   Var "/=" (Forall ["a", "a"] "Bool")]