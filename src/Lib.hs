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
  -- TODO restrict to (T = ((T1,...,Tn) -> Te when C)
  collect (EFun ns e) = do
    taus <- mapM (const (TVar <$> gen)) ns
    (taue, cs) <- local (\env -> foldr (uncurry M.insert) env (zip ns taus)) $ collect e
    tau <- TVar <$> gen
    return (tau, combineMaybes CConj [Just (tau `CEq` TFun taus taue), cs])
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

data V =
    VBool Bool
  | VInt Int
  | VAtom String
  | VFloat Float

data Pat =
    PVal V
  | PName Name
  | PTuple [Pat]

data T =
    TNone
  | TAny
  | TVar Integer
  | TTuple [T]
  | TFun [T] T
  | TUnion T T
  | TWhen T C
  | TVal V
  | TBool
  | TInt
  | TAtom
  | TFloat

data C =
    CSubtype T T
  | CEq T T
  | CConj C C
  | CDisj C C

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
  show (EFun ns e) = "fun" ++ showList ns ++ " -> " ++ show e
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
  show (TWhen t c) = show t ++ " when " ++ show c
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
