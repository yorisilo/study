{-# OPTIONS_GHC -fglasgow-exts #-}
module Eval(step,normalize,eval,evalResult,decompose,plug) where

import Data.Maybe

import Lang

boolToADT True = Cons "True" []
boolToADT False = Cons "False" []

builtinOps = [
    ("+", \x y -> IntLit $ x + y),
    ("-", \x y -> IntLit $ x - y),
    ("*", \x y -> IntLit $ x * y),
    ("/", \x y -> IntLit $ x `div` y),
    ("==", \x y -> boolToADT $ x == y),
    ("/=", \x y -> boolToADT $ x /= y),
    ("%<=", \x y -> boolToADT $ x <= y),
    ("%>=", \x y -> boolToADT $ x >= y),
    ("%<", \x y -> boolToADT $ x < y),
    ("%>", \x y -> boolToADT $ x > y)]

reduce (Fix v e) = Just $ substBind (Fix v e) e
reduce (App (Var (FVar "-")) (IntLit k)) = Just $ IntLit $ -k
reduce (App (App (Var (FVar s)) (IntLit k1)) (IntLit k2)) | Just f <- lookup s builtinOps = 
    Just $ f k1 k2
reduce (App (Lam _ e) v) | isValue v = Just $ substBind v e
reduce (Rst e) | isValue e = Just e
               | (k, Sft _ e', True) <- decompose e = Just $
                    substBind (Lam "x" $ substVar (FVar "") (Var $ BVar 0) $ renumber 1 $ Rst $ plug (Var (FVar "")) k) e'
reduce (Case _ []) = Nothing
reduce (Case (Cons s es) ((n,v,e):os)) | all isValue es =
    if s == n && length es == length v 
        then Just $ foldr (.) id (map substBind es) e
        else reduce (Case (Cons s es) os)
reduce _ = Nothing

isRedex = isJust . reduce

ctxPC CEmpty = True
ctxPC (CRst _) = False
ctxPC (CAppr _ k) = ctxPC k
ctxPC (CAppl k _) = ctxPC k
ctxPC (CCons _ _ k _) = ctxPC k
ctxPC (CCase k _) = ctxPC k

decompose (App (App (Var (FVar fv)) v) e) | isValue v && not (isValue e) && fv `elem` map fst builtinOps = (CAppr (App (Var (FVar fv)) v) k, r, b)
    where (k, r, b) = decompose e
decompose ee@(App (App (Var (FVar fv)) v) e) | isValue v && isValue e && fv `elem` map fst builtinOps = (CEmpty, ee, True)
decompose (App v v') | isValue v && isValue v' = (CEmpty, App v v', True)
decompose (App v e) | isValue v = (CAppr v k, r, b)
    where (k, r, b) = decompose e
decompose (App e e') = (CAppl k e', r, b)
    where (k, r, b) = decompose e
decompose (Rst e) | isValue e = (CEmpty, Rst e, True)
                  | Sft _ _ <- r, ctxPC k = (CEmpty, Rst e, True)
                  | otherwise = (CRst k, r, False)
    where (k, r, b) = decompose e
decompose (Cons s es) | (vs, (e:es')) <- break (not . isValue) es
                      , let (k, r, b) = decompose e = 
        (CCons s vs k es', r, b)
decompose (Case v es) | isValue v = (CEmpty, Case v es, True)
decompose (Case e es) = (CCase k es, r, b)
    where (k, r, b) = decompose e
decompose e = (CEmpty, e, True)

plug e CEmpty = e
plug e (CAppl k e') = App (plug e k) e'
plug e (CAppr e' k) = App e' (plug e k)
plug e (CRst k) = Rst (plug e k)
plug e (CCons s es1 k es2) = Cons s (es1 ++ [plug e k] ++ es2)
plug e (CCase k es) = Case (plug e k) es

step e = do
    let (k, e', _) = decompose e
    e'' <- reduce e'
    return $ plug e'' k

iterateMaybe f s | Just s' <- f s = s : iterateMaybe f s'
                 | otherwise = [s]

eval = iterateMaybe step

evalResult = last . eval

normalize = normalizeSubterms . evalResult where
    normalizeSubterms (App e1 e2) = App (normalize e1) (normalize e2)
    normalizeSubterms (Lam x e) = Lam x (normalize e)
    normalizeSubterms (Sft x e) = Sft x (normalize e)
    normalizeSubterms (Rst e) = Rst (normalize e)
    normalizeSubterms (Var v) = Var v
    normalizeSubterms (IntLit k) = IntLit k
    normalizeSubterms (Cons s es) = Cons s (map normalize es)
    normalizeSubterms (Case e es) = Case (normalize e) (map nce es) where
        nce (n,v,e) = (n,v,normalize e)


