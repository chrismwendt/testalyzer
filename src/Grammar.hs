{-# LANGUAGE TemplateHaskell, TypeOperators, OverloadedStrings #-}

module Grammar (e, v, p, t, c, parseString, unparseString) where

import Types
import Prelude hiding (showList, (.), id)
import Control.Category ((.))
import Text.Boomerang
import Text.Boomerang.String
import Text.Boomerang.Combinators
import Text.Boomerang.TH
import Data.Maybe

$(makeBoomerangs ''E)
$(makeBoomerangs ''V)
$(makeBoomerangs ''Pat)
$(makeBoomerangs ''T)
$(makeBoomerangs ''C)

name :: StringBoomerang r (String :- r)
name = rList1 alpha

rTriple :: Boomerang e tok (a :- b :- c :- r) ((a, b, c) :- r)
rTriple = xpure (arg (arg (arg (:-))) (\a b c -> (a, b, c))) $ \(abc :- t) -> do (a, b, c) <- Just abc; Just (a :- b :- c :- t)

e :: StringBoomerang r (E :- r)
e = foldr1 (<>) [ rEVal    . v
                , rEVar    . name
                , rETuple  . "<" . rListSep e "," . ">"
                , rECall   . "!" {- to avoid left recursion -} . e . "(" . rListSep e "," . ")"
                , rEFun    . "fun(" . rListSep name "," . ") -> " . e
                , rELet    . "let " . name . " = " . e . " in " . e
                , rELetRec . "letrec " . rListSep (rPair . name . " = " . e) "; " . " in " . e
                , rECase   . "case " . e . " of " . rListSep (rTriple . p . " when " . e . " -> " . e) "; " . " end"
                ]

v :: StringBoomerang r (V :- r)
v = foldr1 (<>) [ rVBool . rBool "true" "false"
                , rVInt  . int
                , rVInt  . int
                ]

p :: StringBoomerang r (Pat :- r)
p = foldr1 (<>) [ rPVal   . v
                , rPName  . name
                , rPTuple . "<" . rListSep p "," . ">"
                ]

t :: StringBoomerang r (T :- r)
t = foldr1 (<>) [ rTNone  . "none()"
                , rTAny   . "any()"
                , rTVar   . "t" . integer
                , rTTuple . "<" . rListSep t "," . ">"
                , rTFun   . "(" . rListSep t "," . ") -> " . t
                , rTUnion . "U " . t . " " . t
                , rTBool  . "bool()"
                , rTInt   . "int()"
                ]

c :: StringBoomerang r (C :- r)
c = foldr1 (<>) [ rCSubtype . "(" . t . " < " . t . ")"
                , rCConj    . "(" . c . " ^ " . c . ")"
                , rCDisj    . "(" . c . " v " . c . ")"
                , rCEq      . "(" . t . " = " . t . ")"
                ]

instance Show E where
  show = fromJust . unparseString e

instance Show V where
  show = fromJust . unparseString v

instance Show Pat where
  show = fromJust . unparseString p

instance Show T where
  show = fromJust . unparseString t

instance Show C where
  show = fromJust . unparseString c
