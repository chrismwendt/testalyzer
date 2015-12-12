module Grammar where

import Types
import Data.List
import Prelude hiding (showList)

instance Show E where
  show (EVal v) = show v
  show (EVar name) = name
  show (ETuple es) = showTuple es
  show (ECall e es) = show e ++ showList es
  show (EFun ns e) = "fun(" ++ intercalate ", " ns ++ ") -> " ++ show e
  show (ELet n e1 e2) = "let " ++ show n ++ " = " ++ show e1 ++ " in " ++ show e2
  show (ELetRec bs e) = "letrec " ++ concatMap (\(n, e) -> n ++ " = " ++ show e ++ ";") bs ++ " in " ++ show e
  show (ECase e pges) = "case " ++ show e ++ " of " ++ concatMap (\(p, g, e) -> show p ++ " when " ++ show g ++ " -> " ++ show e ++ "; ") pges ++ "end"

instance Show V where
  show (VBool b) = if b then "true" else "false"
  show (VInt i) = show i
  show (VAtom s) = s

instance Show Pat where
  show (PVal v) = show v
  show (PName n) = n
  show (PTuple ps) = showTuple ps

instance Show T where
  show (TNone) = "none()"
  show (TAny) = "any()"
  show (TVar v) = "t" ++ show v
  show (TTuple ts) = showTuple ts
  show (TFun ts t) = showList ts ++ " -> " ++ show t
  show (TUnion l r) = show l ++ " U " ++ show r
  -- TODO figure out what to do with bound constraints
  -- show (TWhen t c) = show t ++ " when " ++ case c of Nothing -> "{}"; Just c' -> show c'
  show (TVal v) = show v
  show (TBool) = "bool()"
  show (TInt) = "int()"
  show (TAtom) = "atom()"
  show (TFloat) = "float()"

instance Show C where
  show (CSubtype l r) = "(" ++ show l ++ " < " ++ show r ++ ")"
  show (CConj l r) = "(" ++ show l ++ " ^ " ++ show r ++ ")"
  show (CDisj l r) = "(" ++ show l ++ " v " ++ show r ++ ")"
  show (CEq l r) = "(" ++ show l ++ " = " ++ show r ++ ")"

showTuple :: Show a => [a] -> String
showTuple as = "<" ++ sep ", " as ++ ">"

showList :: Show a => [a] -> String
showList as = "(" ++ sep ", " as ++ ")"

showListWith :: Show a => String -> [a] -> String
showListWith s as = "(" ++ sep s as ++ ")"

sep :: Show a => String -> [a] -> String
sep s as = intercalate s (map show as)
