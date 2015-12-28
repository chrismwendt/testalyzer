{-# LANGUAGE LambdaCase #-}

module Lib
    ( module Lib
    , module Grammar
    ) where

import Data.List
import qualified Data.Map as M
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.Except
import Data.Maybe
import Types
import Grammar
import Control.Arrow
import Data.Foldable
import Data.Either

main :: IO ()
main = do
    a <- readFile "0.txt"
    forM_ (lines a) $ \line -> do
        let p = left show (parse e line)
        let cs = simplify <$> (p >>= constraints)
        let thing = cs >>= solve
        print cs
        putStrLn (either id (maybe "No solution" prettyMap) thing)

-- TODO initialize environment with primitive functions like is_atom

solve :: C -> Either String Sol
solve c = solve' (Just $ foldr (`M.insert` TAny) M.empty $ varsInC c) c
  where
  solve' :: Sol -> C -> Either String Sol
  solve' Nothing _ = Right Nothing
  solve' sol CTrivial = Right sol
  solve' sol c@(CEq l r) = solveReason sol $ CConj [l `CSubtype` r, r `CSubtype` l]
  solve' sol c@(CConj cs) = do
    sol' <- foldrM (flip solveReason) sol cs
    if sol == sol' then Right sol else solveReason sol' c
  solve' sol (CDisj cs) = do
    sols <- mapM (solveReason sol) cs
    case catMaybes sols of
      [] -> Right Nothing
      sols' -> Right $ Just $ M.unionsWith lub sols'

  solve' (Just sol) c@(CSubtype l@(TVar _) r) = return $ Just $ M.insert l (glb (sol # l) (sol # r)) sol
  solve' (Just sol) c@(CSubtype (TTuple ls) r) | (TTuple rs) <- sol # r, length ls == length rs = solveReason (Just sol) $ CConj $ zipWith CSubtype ls rs
  solve' (Just sol) c@(CSubtype (TFun la lb) r) | (TFun ra rb) <- sol # r, length la == length ra = solveReason (Just sol) $ CConj $ (lb `CSubtype` rb) : zipWith CSubtype la ra
  solve' (Just sol) c@(CSubtype l r) | (sol # l) `isSubtype` (sol # r) = return $ Just sol
  solve' (Just sol) c@(CSubtype l r) = Left $ show l ++ " is not a subtype of " ++ show r

  solveReason sol c = left (\x -> "Can't solve " ++ show c ++ " because:\n\n" ++ x) $ solve' sol c

  (#) sol t@(TVar _) = sol # fromMaybe (error "y var not defined?") (M.lookup t sol)
  (#) sol (TTuple ts) = TTuple (map (sol #) ts)
  (#) sol (TFun ts t) = TFun (map (sol #) ts) (sol # t)
  -- (#) sol (TUnion l r) = TUnion (sol # l) (sol # r)
  (#) sol t = t

glb l r = fst $ pwglblub l r
lub l r = snd $ pwglblub l r

pwglblub (TVar _) _ = error "pwglblub of tvar"
pwglblub _ (TVar _) = error "pwglblub of tvar"
pwglblub (TUnion _ _) _ = error "pwglblub of union"
pwglblub _ (TUnion _ _) = error "pwglblub of union"
pwglblub l r | l == r = (l, r)
pwglblub TAny other = (other, TAny)
pwglblub other TAny = (other, TAny)
pwglblub TNone other = (TNone, other)
pwglblub other TNone = (TNone, other)
pwglblub l r | any (`elem` [TBool, TInt]) [l, r] = (TNone, TAny)
pwglblub (TTuple l) (TTuple r) | length l == length r = (TTuple (zipWith (\l r -> fst $ pwglblub l r) l r), TTuple (zipWith (\l r -> snd $ pwglblub l r) l r))
pwglblub (TTuple _) _ = (TNone, TAny)
pwglblub (TFun la lb) (TFun ra rb) | length la == length ra = (TFun (zipWith (\l r -> fst $ pwglblub l r) la ra) (fst $ pwglblub lb rb), TFun (zipWith (\l r -> snd $ pwglblub l r) la ra) (snd $ pwglblub lb rb))
pwglblub (TFun _ _) _ = (TNone, TAny)

constraints :: E -> Either String C
constraints = flip runReader M.empty . runGenT . runExceptT . (fmap snd <$> collect)
  where
  collect :: E -> ExceptT String (GenT Integer (Reader (M.Map Name T))) (T, C)
  collect (EVal v) = return (valType v, CTrivial)
  collect (EVar name) = asks (M.lookup name) >>= \case Just y -> return (y, CTrivial)
                                                       Nothing -> throwError $ "Undefined variable " ++ name
  collect (ETuple es) = do (types, constraints) <- unzip <$> mapM collect es
                           return (TTuple types, CConj constraints)
  collect (ECall e es) = do
    (tau, c) <- collect e
    (taus, cs) <- unzip <$> mapM collect es
    beta <- tVar
    alpha <- tVar
    alphas <- mapM (const tVar) taus
    let c0 = tau `CEq` TFun taus alpha
        c1 = beta `CSubtype` alpha
        c2 = CConj $ zipWith CSubtype taus alphas
        c3 = CConj (c : cs)
    return (beta, CConj [c0, c1, c2, c3])
  collect (EFun ns e) = do
    taus <- mapM (const tVar) ns
    (taue, cs) <- local (\env -> foldr (uncurry M.insert) env (zip ns taus)) $ collect e
    tau <- tVar
    -- TODO figure out what to do with bound constraints
    -- return (tau, Just (tau `CEq` (TFun taus taue `TWhen` cs)))
    return (tau, CConj [tau `CEq` TFun taus taue, cs])
  collect (ELet n e1 e2) = do
    (tau1, c1) <- collect e1
    (tau2, c2) <- local (M.insert n tau1) (collect e2)
    trace <- tVarOf n
    return (tau2, CConj [c1, c2, trace `CEq` tau1])
  collect (ELetRec bs e) = do
    let (names, es) = unzip bs
    taus <- mapM (const tVar) names
    env <- ask
    let env' = foldr (uncurry M.insert) env (zip names taus)
    (tau's, constraints) <- unzip <$> local (const env') (mapM collect es)
    (taue, constrainte) <- local (const env') (collect e)
    return (taue, CConj (zipWith CEq tau's taus ++ constrainte : constraints))
  collect (ECase e pges) = do
    let (ps, gs, es) = unzip3 pges
    (tau, ce) <- collect e
    beta <- tVar
    env <- ask
    let psvars = map patVars ps
    taus <- mapM (const tVar) pges
    let env's = map (\pi -> foldr (uncurry M.insert) env (zip pi taus)) psvars
    (ais, cpis) <- unzip <$> mapM (\(env'i, pi, gi) -> local (const env'i) (collectP pi gi)) (zip3 env's ps gs)
    (bis, cbis) <- unzip <$> mapM (\(env'i, bi) -> local (const env'i) (collect bi)) (zip env's es)
    let ci ai bi cpi cbi = CConj [beta `CEq` bi, tau `CEq` ai, cpi, cbi]
    return (beta, CConj [ce, CDisj (zipWith4 ci ais bis cpis cbis)])

  collectP pat guard = do
    tau <- patType pat
    (tg, cg) <- collect guard
    return (tau, CConj [cg, tg `CEq` TBool])

  tVar :: ExceptT String (GenT Integer (Reader (M.Map Name T))) T
  tVar = TVar . show <$> gen

  tVarOf :: String -> ExceptT String (GenT Integer (Reader (M.Map Name T))) T
  tVarOf name = TVar . (name ++) . show <$> gen

varsInT :: T -> [T]
varsInT v@(TVar _) = [v]
varsInT (TTuple ts) = concatMap varsInT ts
varsInT (TFun ts t) = concatMap varsInT ts ++ varsInT t
varsInT (TUnion l r) = varsInT l ++ varsInT r
-- TODO figure out what to do with bound constraints
-- varsInT (TWhen t c) = varsInT t ++ concatMap varsInC (maybeToList c)
varsInT _ = []

varsInC :: C -> [T]
varsInC (CTrivial) = []
varsInC (CSubtype l r) = varsInT l ++ varsInT r
varsInC (CEq l r) = varsInT l ++ varsInT r
varsInC (CConj cs) = concatMap varsInC cs
varsInC (CDisj cs) = concatMap varsInC cs

isStrictSubtype :: T -> T -> Bool
isStrictSubtype l r | l == r = False
-- TODO figure out what to do with bound constraints
-- isStrictSubtype other (TWhen t c) = isStrictSubtype other t
-- isStrictSubtype (TWhen t c) other = isStrictSubtype t other
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

patVars :: P -> [Name]
patVars (PVal _) = []
patVars (PName n) = [n]
patVars (PTuple ps) = concatMap patVars ps

patType :: P -> ExceptT String (GenT Integer (Reader (M.Map Name T))) T
patType (PVal v) = return $ valType v
patType (PName n) = TVar . (n ++) . show <$> gen
patType (PTuple ps) = TTuple <$> mapM patType ps

valType :: V -> T
valType (VBool _) = TBool
valType (VInt _) = TInt

simplify :: C -> C
simplify (CConj cs) = let cs' = map simplify cs
                          _  = [c | c@(CTrivial)     <- cs']
                          ss = [c | c@(CSubtype _ _) <- cs']
                          es = [c | c@(CEq _ _)      <- cs']
                          ns = [n | c@(CConj n)      <- cs']
                          ds = [c | c@(CDisj _)      <- cs']
                      in CConj $ ss ++ es ++ concat ns ++ ds
simplify (CDisj cs) = CDisj (map simplify cs)
simplify c@(CEq l r) | l == r = CTrivial
                     | otherwise = c
simplify c = c
    where
    isConj (CConj _) = True
    isConj _         = False

prettyMap :: (Show a, Show b) => M.Map a b -> String
prettyMap m = unlines $ map (\(k, v) -> show k ++ " = " ++ show v) $ M.assocs m
