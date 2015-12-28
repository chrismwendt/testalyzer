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

main :: IO ()
main = do
    a <- readFile "0.txt"
    forM_ (lines a) $ \line -> do
        let thing = left show (parse e line) >>= constraints
        print thing

-- TODO initialize environment with primitive functions like is_atom

solve :: C -> Either String Sol
solve c = solve' (Just $ foldr (`M.insert` TAny) M.empty $ varsInC c) c
  where
  solve' :: Sol -> C -> Either String Sol
  solve' Nothing _ = Right Nothing
  solve' sol c@(CEq l r) = solve' sol ((l `CSubtype` r) `CConj` (r `CSubtype` l))
  solve' sol c@(CConj l r) = do
    sol' <- solve' sol l >>= flip solve' r
    if sol == sol' then Right sol else solve' sol' c
  solve' sol (CDisj l r) = do
    soll <- solve' sol l
    solr <- solve' sol r
    case catMaybes [soll, solr] of
      [] -> Right Nothing
      sols -> Right $ Just $ M.unionsWith lub sols

  solve' (Just sol) c@(CSubtype l@(TVar _) r) = return $ Just $ M.insert l (glb (sol # l) (sol # r)) sol
  solve' (Just sol) c@(CSubtype (TTuple ls) r) | (TTuple rs) <- sol # r, length ls == length rs = solve' (Just sol) $ foldr1 CConj $ zipWith CSubtype ls rs
  solve' (Just sol) c@(CSubtype (TFun la lb) r) | (TFun ra rb) <- sol # r, length la == length ra = solve' (Just sol) $ foldr1 CConj (zipWith CSubtype la ra) `CConj` (lb `CSubtype` rb)
  solve' (Just sol) c@(CSubtype l r) | (sol # l) `isSubtype` (sol # r) = return $ Just sol
  solve' (Just sol) c@(CSubtype _ _) = Left $ "Can't solve " ++ show c ++ " with sol " ++ show sol

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
    beta <- tVar
    alpha <- tVar
    alphas <- mapM (const tVar) taus
    let c0 = Just $ tau `CEq` TFun taus alpha
        c1 = Just $ beta `CSubtype` alpha
        c2 = Just $ foldr1 CConj $ zipWith CSubtype taus alphas
        c3 = combineMaybes CConj (c : cs)
    return (beta, combineMaybes CConj [c0, c1, c2, c3])
  collect (EFun ns e) = do
    taus <- mapM (const tVar) ns
    (taue, cs) <- local (\env -> foldr (uncurry M.insert) env (zip ns taus)) $ collect e
    tau <- tVar
    -- TODO figure out what to do with bound constraints
    -- return (tau, Just (tau `CEq` (TFun taus taue `TWhen` cs)))
    return (tau, combineMaybes CConj [Just (tau `CEq` TFun taus taue), cs])
  collect (ELet n e1 e2) = do
    (tau1, c1) <- collect e1
    (tau2, c2) <- local (M.insert n tau1) (collect e2)
    trace <- tVarOf n
    return (tau2, combineMaybes CConj [c1, c2, Just (trace `CEq` tau1)])
  collect (ELetRec bs e) = do
    let (names, es) = unzip bs
    taus <- mapM (const tVar) names
    env <- ask
    let env' = foldr (uncurry M.insert) env (zip names taus)
    (tau's, constraints) <- unzip <$> local (const env') (mapM collect es)
    (taue, constrainte) <- local (const env') (collect e)
    return (taue, combineMaybes CConj (zipWith (\l r -> Just $ l `CEq` r) tau's taus ++ constrainte : constraints))
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
    let ci ai bi cpi cbi = combineMaybes CConj [Just (beta `CEq` bi), Just (tau `CEq` ai), cpi, cbi]
    return (beta, combineMaybes CConj [ce, combineMaybes CDisj (zipWith4 ci ais bis cpis cbis)])

  collectP pat guard = do
    tau <- patType pat
    (tg, cg) <- collect guard
    return (tau, combineMaybes CConj [cg, Just (tg `CEq` TBool)])

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
varsInC (CSubtype l r) = varsInT l ++ varsInT r
varsInC (CEq l r) = varsInT l ++ varsInT r
varsInC (CConj l r) = varsInC l ++ varsInC r
varsInC (CDisj l r) = varsInC l ++ varsInC r

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

combineMaybes :: (a -> a -> a) -> [Maybe a] -> Maybe a
combineMaybes f as = case catMaybes as of
  [] -> Nothing
  as' -> Just $ foldr1 f as'
