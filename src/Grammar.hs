{-# LANGUAGE TemplateHaskell, TypeOperators, OverloadedStrings #-}

module Grammar
    ( module Grammar
    , module Text.Megaparsec
    ) where

import Prelude hiding (print, showList)
import Types
import Text.Megaparsec hiding (parse, oneOf)
import Text.Megaparsec.String
import Text.Megaparsec.Lexer
import Data.String
import Control.Applicative
import Data.Functor
import Data.List
import Data.Tree

parse :: Stream s t => Parsec s a -> s -> Either ParseError a
parse p = runParser (p <* eof) ""

s :: String -> Parser String
s = string

listOf :: Parser a -> Parser [a]
listOf p = between (s "(") (s ")") $ p `sepBy` s ","

tupleOf :: Parser a -> Parser [a]
tupleOf p = between (s "<") (s ">") $ p `sepBy` s ","

name :: Parser String
name = some letterChar

oneOf :: [Parser a] -> Parser a
oneOf = foldr1 (\a b -> try a <|> b)

v :: Parser V
v = oneOf [ VInt . fromIntegral <$> integer
          , VBool False         <$  s "false"
          , VBool True          <$  s "true" ]

p :: Parser P
p = oneOf [ PVal   <$> v
          , PName  <$> name
          , PTuple <$> tupleOf p
          ]

e :: Parser E
e = oneOf [ EVal    <$> v
          , ETuple  <$> tupleOf e
          , ECall   <$  s "!" <*> e <*> listOf e
          , EFun    <$  s "fun" <*> listOf name <* s " -> " <*> e
          , ELet    <$  s "let " <*> name <* s " = " <*> e <* s " in " <*> e
          , ELetRec <$  s "letrec " <*> ((,) <$> name <* s " = " <*> e) `sepBy` s ";" <* s " in " <*> e
          , ECase   <$  s "case " <*> e <* s " of " <*> ((,,) <$> p <* s " when " <*> e <* s " -> " <*> e) `sepBy` s ";" <* s " end"
          , EVar    <$> name
          ]

t :: Parser T
t = oneOf [ TNone  <$  s "none()"
          , TAny   <$  s "any()"
          , TBool  <$  s "bool()"
          , TInt   <$  s "int()"
          , TVar   <$> name
          , TTuple <$> tupleOf t
          , TFun   <$> listOf t <* s " -> " <*> t
          , TUnion <$  s "U " <*> t <* s " " <*> t
          ]

c :: Parser C
c = oneOf [ uncurry CSubtype <$> t `sepPair` " < "
          , uncurry CEq      <$> t `sepPair` " = "
          , CConj            <$> c `sepBy` s " ^ "
          , CDisj            <$> c `sepBy` s " v "
          ]
    where
    sepPair v sp = (,) <$ s "(" <*> v <* s sp <*> v <* s ")"

sepString :: Show a => String -> [a] -> String
sepString s as = intercalate s (map show as)

showPair :: Show a => a -> String -> a -> String
showPair l sep r = "(" ++ show l ++ sep ++ show r ++ ")"

showTuple :: Show a => [a] -> String
showTuple as = "<" ++ sepString "," as ++ ">"

showList :: Show a => [a] -> String
showList as = "(" ++ sepString "," as ++ ")"

showListWith :: Show a => String -> [a] -> String
showListWith s as = "(" ++ sepString s as ++ ")"

instance Show E where
    show (EVal v)       = show v
    show (EVar name)    = name
    show (ETuple es)    = showTuple es
    show (ECall e es)   = "!" ++ show e ++ showList es
    show (EFun ns e)    = "fun(" ++ intercalate "," ns ++ ") -> " ++ show e
    show (ELet n e1 e2) = "let " ++ show n ++ " = " ++ show e1 ++ " in " ++ show e2
    show (ELetRec bs e) = "letrec " ++ concatMap (\(n, e) -> n ++ " = " ++ show e ++ ";") bs ++ " in " ++ show e
    show (ECase e pges) = "case " ++ show e ++ " of " ++ concatMap (\(p, g, e) -> show p ++ " when " ++ show g ++ " -> " ++ show e ++ ";") pges ++ "end"

instance Show V where
    show (VBool b) = if b then "true" else "false"
    show (VInt i)  = show i

instance Show P where
    show (PVal v)    = show v
    show (PName n)   = n
    show (PTuple ps) = showTuple ps

instance Show T where
    show (TNone)      = "none()"
    show (TAny)       = "any()"
    show (TVar v)     = "t" ++ v
    show (TTuple ts)  = showTuple ts
    show (TFun ts t)  = showList ts ++ " -> " ++ show t
    show (TUnion l r) = "(U " ++ show l ++ " " ++ show r
    show (TBool)      = "bool()"
    show (TInt)       = "int()"

cToTree :: C -> Tree String
cToTree (CTrivial) = Node "trivial" []
cToTree (CSubtype l r) = Node (show l ++ " < " ++ show r) []
cToTree (CEq      l r) = Node (show l ++ " = " ++ show r) []
cToTree (CConj    cs) = Node "conj" $ map cToTree cs
cToTree (CDisj    cs) = Node "disj" $ map cToTree cs

instance Show C where
    show c = drawTree $ cToTree c
