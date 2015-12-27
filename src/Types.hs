module Types where

import qualified Data.Map as M

type Name = String

data E =
    EVal V
  | EVar Name
  | ETuple [E]
  | ECall E [E]
  | EFun [Name] E
  | ELet Name E E
  | ELetRec [(Name, E)] E
  | ECase E [(P, E, E)]
  deriving (Eq, Ord)

data V =
    VBool Bool
  | VInt Int
  deriving (Eq, Ord)

data P =
    PVal V
  | PName Name
  | PTuple [P]
  deriving (Eq, Ord)

data T =
    TNone
  | TAny
  | TVar Name
  | TTuple [T]
  | TFun [T] T
  | TUnion T T
  -- TODO figure out what to do with bound constraints
  -- | TWhen T (Maybe C)
  | TBool
  | TInt
  deriving (Eq, Ord)

data C =
    CSubtype T T
  | CEq T T
  | CConj C C
  | CDisj C C
  deriving (Eq, Ord)

-- environment lookups default to any()
-- Just M.empty represents a solution that maps all type expressions to any()
-- Nothing represents bottom, a solution that maps all type expressions to none()
type Sol = Maybe (M.Map T T)
