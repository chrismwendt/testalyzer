{-# LANGUAGE LambdaCase #-}

module Lib
    ( someFunc
    , combineMaybes
    ) where

import Prelude hiding (showList)
import Data.List
import qualified Data.Map as M
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.Except
import Data.Maybe

-- let "x" = fun("a", "b") -> case <a, b> of <true, true> -> true; end in x(3, true)
bad :: E
bad = ELet "x" (EFun ["a", "b"] (ECase (ETuple [EVar "a", EVar "b"]) [(PTuple [PVal (VBool True), PVal (VBool True)], EVal (VBool True), EVal (VBool True))])) (ECall (EVar "x") [EVal (VInt 3), EVal (VBool True)])

-- let "x" = fun("a", "b") -> case <a, b> of <3, true> -> true; end in x(3, true)
good :: E
good = ELet "x" (EFun ["a", "b"] (ECase (ETuple [EVar "a", EVar "b"]) [(PTuple [PVal (VInt 3), PVal (VBool True)], EVal (VBool True), EVal (VBool True))])) (ECall (EVar "x") [EVal (VInt 3), EVal (VBool True)])

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- TODO initialize environment with primitive functions like is_atom

solve :: C -> Sol
solve c = solve' (Just $ foldr (`M.insert` TAny) M.empty $ varsInC c) c
  where
  solve' Nothing _ = Nothing
  solve' msol (CEq l r) = solve' msol (CSubtype l r `CConj` CSubtype r l)
  solve' (Just sol) (CSubtype l r)
    | (sol # l) `isSubtype` (sol # r) = Just sol
    | t /= TNone = Just $ M.insert l t sol
    | otherwise = Nothing
    where
    t = (sol # l) `glb` (sol # r)
  solve' sol conj@(CConj _ _)
    | sol == sol' = sol
    | otherwise = solve' sol' conj
    where
    sol' = solveConj sol conj
  solve' sol (CDisj l r)
    | null sol'= Nothing
    | otherwise = Just $ M.unionsWith lub sol'
    where
    sol' = catMaybes [solve' sol l, solve' sol r]

  solveConj :: Sol -> C -> Sol
  solveConj Nothing _ = Nothing
  solveConj sol (CConj l r) = solveConj (solve' sol l) r
  solveConj sol c = solve' sol c

  (#) sol t@(TVar _) = fromMaybe (error "y var not defined?") (M.lookup t sol)
  (#) sol (TTuple ts) = TTuple (map (sol #) ts)
  (#) sol (TFun ts t) = TFun (map (sol #) ts) (sol # t)
  (#) sol (TUnion l r) = TUnion (sol # l) (sol # r)
  (#) sol (TWhen t c) = TWhen (sol # t) Nothing -- TODO figure out what to do with bound constraints
  (#) sol t = t

constraints :: E -> Either String (Maybe C)
constraints = flip runReader M.empty . runGenT . runExceptT . (fmap snd <$> collect)
  where
  collect :: E -> ExceptT String (GenT Integer (Reader (M.Map Name T))) (T, Maybe C)
  collect (EVal v) = return (valType v, Nothing)
  collect (EVar name) = asks (M.lookup name) >>= \case Just y -> return (y, Nothing)
                                                       Nothing -> throwError $ "Undefined variable " ++ name
  collect (ETuple es) = do (types, constraints) <- unzip <$> mapM collect es
                           return (TTuple types, combineMaybes CConj constraints)
  collect (ECall e es) = do
    (tau, c) <- collect e
    (taus, cs) <- unzip <$> mapM collect es
    beta <- TVar <$> gen
    alpha <- TVar <$> gen
    alphas <- mapM (const (TVar <$> gen)) taus
    let c0 = Just $ tau `CEq` TFun taus alpha
        c1 = Just $ beta `CSubtype` alpha
        c2 = Just $ foldr1 CConj $ zipWith CSubtype taus alphas
        c3 = combineMaybes CConj (c : cs)
    return (beta, combineMaybes CConj [c0, c1, c2, c3])
  collect (EFun ns e) = do
    taus <- mapM (const (TVar <$> gen)) ns
    (taue, cs) <- local (\env -> foldr (uncurry M.insert) env (zip ns taus)) $ collect e
    tau <- TVar <$> gen
    return (tau, Just (tau `CEq` (TFun taus taue `TWhen` cs)))
  collect (ELet n e1 e2) = do
    (tau1, c1) <- collect e1
    (tau2, c2) <- local (M.insert n tau1) (collect e2)
    return (tau2, combineMaybes CConj [c1, c2])
  collect (ELetRec bs e) = do
    let (names, es) = unzip bs
    taus <- mapM (const $ TVar <$> gen) names
    env <- ask
    let env' = foldr (uncurry M.insert) env (zip names taus)
    (tau's, constraints) <- unzip <$> local (const env') (mapM collect es)
    (taue, constrainte) <- local (const env') (collect e)
    return (taue, combineMaybes CConj (zipWith (\l r -> Just $ l `CEq` r) tau's taus ++ constrainte : constraints))
  collect (ECase e pges) = do
    let (ps, gs, es) = unzip3 pges
    (tau, ce) <- collect e
    beta <- TVar <$> gen
    env <- ask
    let psvars = map patVars ps
    taus <- mapM (const (TVar <$> gen)) pges
    let env's = map (\pi -> foldr (uncurry M.insert) env (zip pi taus)) psvars
    (ais, cpis) <- unzip <$> mapM (\(env'i, pi, gi) -> local (const env'i) (collectPat pi gi)) (zip3 env's ps gs)
    (bis, cbis) <- unzip <$> mapM (\(env'i, bi) -> local (const env'i) (collect bi)) (zip env's es)
    let ci ai bi cpi cbi = combineMaybes CConj [Just (beta `CEq` bi), Just (tau `CEq` ai), cpi, cbi]
    return (beta, combineMaybes CConj [ce, combineMaybes CDisj (zipWith4 ci ais bis cpis cbis)])

  collectPat pat guard = do
    tau <- patType pat
    (tg, cg) <- collect guard
    return (tau, combineMaybes CConj [cg, Just (tg `CEq` TBool)])

type Name = String

data E =
    EVal V
  | EVar Name
  | ETuple [E]
  | ECall E [E]
  | EFun [Name] E
  | ELet Name E E
  | ELetRec [(Name, E)] E
  | ECase E [(Pat, E, E)]
  deriving (Eq, Ord)

data V =
    VBool Bool
  | VInt Int
  | VAtom String
  | VFloat Float
  deriving (Eq, Ord)

data Pat =
    PVal V
  | PName Name
  | PTuple [Pat]
  deriving (Eq, Ord)

data T =
    TNone
  | TAny
  | TVar Integer
  | TTuple [T]
  | TFun [T] T
  | TUnion T T
  | TWhen T (Maybe C)
  | TVal V
  | TBool
  | TInt
  | TAtom
  | TFloat
  deriving (Eq, Ord)

data C =
    CSubtype T T
  | CEq T T
  | CConj C C
  | CDisj C C
  deriving (Eq, Ord)

varsInT :: T -> [T]
varsInT v@(TVar _) = [v]
varsInT (TTuple ts) = concatMap varsInT ts
varsInT (TFun ts t) = concatMap varsInT ts ++ varsInT t
varsInT (TUnion l r) = varsInT l ++ varsInT r
varsInT (TWhen t c) = varsInT t ++ concatMap varsInC (maybeToList c)
varsInT _ = []

varsInC :: C -> [T]
varsInC (CSubtype l r) = varsInT l ++ varsInT r
varsInC (CEq l r) = varsInT l ++ varsInT r
varsInC (CConj l r) = varsInC l ++ varsInC r
varsInC (CDisj l r) = varsInC l ++ varsInC r

-- environment lookups default to any()
-- Just M.empty represents a solution that maps all type expressions to any()
-- Nothing represents bottom, a solution that maps all type expressions to none()
type Sol = Maybe (M.Map T T)

isStrictSubtype :: T -> T -> Bool
isStrictSubtype l r | l == r = False
isStrictSubtype other (TUnion l r) = other `isSubtype` l || other `isSubtype` r
isStrictSubtype TNone _ = True
isStrictSubtype TAny other = False
isStrictSubtype _ TAny = True
isStrictSubtype (TTuple ls) (TTuple rs) = length ls <= length rs && and (zipWith isSubtype ls rs) && or (zipWith isStrictSubtype ls rs)
isStrictSubtype (TFun largs le) (TFun rargs re) = TTuple rargs `isSubtype` TTuple largs && le `isSubtype` re
isStrictSubtype (TUnion l r) other = l `isSubtype` other && r `isSubtype` other
isStrictSubtype _ _ = False

isSubtype :: T -> T -> Bool
isSubtype l r = l == r || l `isStrictSubtype` r

-- TODO figure out if this is correct
lub :: T -> T -> T
lub l r | l `isSubtype` r = r
lub l r | r `isSubtype` l = l
lub l r = TUnion l r

glb :: T -> T -> T
glb l r | l `isSubtype` r = l
glb l r | r `isSubtype` l = r
glb l r = TNone

patVars :: Pat -> [Name]
patVars (PVal _) = []
patVars (PName n) = [n]
patVars (PTuple ps) = concatMap patVars ps

patType :: Pat -> ExceptT String (GenT Integer (Reader (M.Map Name T))) T
patType (PVal v) = return $ valType v
patType (PName _) = TVar <$> gen
patType (PTuple ps) = TTuple <$> mapM patType ps

valType :: V -> T
valType (VBool _) = TBool
valType (VInt _) = TInt
valType (VAtom _) = TAtom
valType (VFloat _) = TFloat

combineMaybes :: (a -> a -> a) -> [Maybe a] -> Maybe a
combineMaybes f as = case catMaybes as of
  [] -> Nothing
  as' -> Just $ foldr1 f as'

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
  show (VFloat f) = show f

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
  show (TWhen t c) = show t ++ " when " ++ case c of Nothing -> "{}"; Just c' -> show c'
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
