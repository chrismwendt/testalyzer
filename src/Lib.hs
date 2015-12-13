{-# LANGUAGE LambdaCase #-}

module Lib
    ( combineMaybes
    , module Grammar
    ) where

import Prelude hiding (showList, (.), id)
import Control.Category ((.))
import Data.List
import qualified Data.Map as M
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.Except
import Data.Maybe
import Types
import Grammar

bad :: E
bad = case parseString e "let x = fun(a,b) -> case <a,b> of <true,true> when true -> true end in !x(3,true)" of
  Left r -> error $ show r
  Right v -> v

good :: E
good = case parseString e "let x = fun(a,b) -> case <a,b> of <3,true> when true -> true end in !x(3,true)" of
  Left r -> error $ show r
  Right v -> v

-- TODO initialize environment with primitive functions like is_atom

solve :: C -> Either String Sol
solve c = solve' (Just $ foldr (`M.insert` TAny) M.empty $ varsInC c) c
  where
  solve' :: Sol -> C -> Either String Sol
  solve' Nothing _ = Right Nothing
  solve' (Just sol) c@(CEq l r) = case solve' (Just sol) (CSubtype l r `CConj` CSubtype r l) of
    Left _ -> Left $ "Can't solve " ++ show c
    Right r -> Right r
  solve' (Just sol) c@(CSubtype l r)
    | (sol # l) `isSubtype` (sol # r) = Right $ Just sol
    | t /= TNone = Right $ Just $ M.insert l t sol
    | otherwise = Left $ "Can't solve " ++ show c
    where
    t = l `glb` r
    glb :: T -> T -> T
    glb l r | (sol # l) `isSubtype` (sol # r) = l
    glb l r | (sol # r) `isSubtype` (sol # l) = r
    glb l r = TNone
  solve' sol c@(CConj l r) = do
    sol' <- solve' sol l
    sol'' <- solve' sol' r
    if sol == sol''
      then Right sol
      else solve' sol'' c
  solve' (Just sol) (CDisj l r) = case catMaybes <$> sequence [solve' (Just sol) l, solve' (Just sol) r] of
    Left _ -> Left $ "Can't solve " ++ show c
    Right r -> Right $ Just $ M.unionsWith lub r
    where
    -- TODO figure out if this is correct
    lub :: T -> T -> T
    lub l r | (sol # l) `isSubtype` (sol # r) = r
    lub l r | (sol # r) `isSubtype` (sol # l) = l
    lub l r = TUnion l r

  (#) sol t@(TVar _) = sol # fromMaybe (error "y var not defined?") (M.lookup t sol)
  (#) sol (TTuple ts) = TTuple (map (sol #) ts)
  (#) sol (TFun ts t) = TFun (map (sol #) ts) (sol # t)
  (#) sol (TUnion l r) = TUnion (sol # l) (sol # r)
  -- TODO figure out what to do with bound constraints
  -- (#) sol (TWhen t c) = TWhen (sol # t) c
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
    -- TODO figure out what to do with bound constraints
    -- return (tau, Just (tau `CEq` (TFun taus taue `TWhen` cs)))
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

combineMaybes :: (a -> a -> a) -> [Maybe a] -> Maybe a
combineMaybes f as = case catMaybes as of
  [] -> Nothing
  as' -> Just $ foldr1 f as'
