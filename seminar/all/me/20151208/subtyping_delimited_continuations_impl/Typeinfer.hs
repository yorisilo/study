{-# OPTIONS_GHC -fglasgow-exts #-}
module Typeinfer(inf, infFull) where

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error

import PrettyPrint

import Data.Maybe
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.List(sortBy)

import Lang

--import Debug.Trace

trace _ = id

type Ctx = Map Var Type

data RSt = RSt { depth :: Int, ctx :: Ctx, adtEnvs :: ADTEnvs }

adtEnv = fst . adtEnvs
adtConsEnv = snd . adtEnvs

data St = St { 
        subst :: Subst,
        vcnt :: Int, 
        tcsub_subst :: Map String TCSub,    -- TCSubVar -> TCSub
        ineq_constr :: Map String (TC, TC), -- TCSubVar -> (TC, TC)
        comp_constr :: [(TC, [TC])] -- TCVar -> [[TCVar]]
    } deriving (Show)

type InferMonad = ErrorT String (ReaderT RSt (State St))

extend t m = local (\s -> s { depth = depth s + 1, ctx = Map.insert (BVar (depth s + 1)) t (ctx s) }) m

typeOf (FVar s) = maybe (fail "x") return =<< Map.lookup (FVar s) `fmap` (ctx `fmap` ask)
typeOf (BVar k) = maybe (fail "x") return =<< Map.lookup `fmap` (BVar `fmap` ((+(-k)) `fmap` (depth `fmap` ask))) `ap` (ctx `fmap` ask)

lookupCons consname = maybe (fail "x") return =<< Map.lookup consname `fmap` (adtConsEnv `fmap` ask)
lookupADT adtname = maybe (fail "x") return =<< Map.lookup adtname `fmap` (adtEnv `fmap` ask)

incrVCnt = modify $ \s -> s { vcnt = vcnt s + 1 }

newXVar f = incrVCnt >> ((f . show . vcnt) `fmap` get)

newTVar = newXVar (TVar . ('V':))
newTCVar = newXVar (TCVar . ('C':))
newTRVar = (,) `fmap` newTVar `ap` newTCVar
newTCSubVar = newXVar (TCSubVar . ('S':))

applySubst x = flip substWT x `fmap` (subst `fmap` get)

{-
tcComp tcs trs = do
    tcs' <- mapM applySubst tcs
    case tcs' of
        [TCVar s] -> -- nothing to sequence
                return (TCVar s, map (const id) trs)
        _ | any isChg tcs' -> do -- must be impure
                undefined
          | all isInd tcs' -> do -- must be pure
                return (Ind, map (const id) trs)
          | otherwise -> do -- postpone the decision
                tc <- newTCVar
                modify (\s -> s { 
                            constr = Map.insert tc tcs' (constr s),
                            rconstr = })
                return (tc, undefined)-}

solveComp xtc xtcs = do
    tcsp <- applySubst (xtc, xtcs)
    trace ("Solving composition " ++ show tcsp) $ case tcsp of
        (tc, [tc']) -> unifyEq tc tc' >> return True
        (tc@(TCVar v), tcs)
            | any isChg tcs -> do -- must be impure
                trss <- replicateM (length tcs + 1) newTRVar
                unifyEq tcs (zipWith (flip Chg) trss (tail trss))
                unifyEq tc $ last trss `Chg` head trss
                return True
            | any isInd tcs -> do -- must be pure
                unifyEq (tc:tcs) (repeat Ind)
                return True
            | otherwise -> -- still don't know
                return False
        (Ind, tcs) -> do
                unifyEq tcs (repeat Ind)
                return True
        (tr1 `Chg` tr2, tcs) -> do
                trs <- replicateM (length tcs - 1) newTRVar
                let trss = [tr2] ++ trs ++ [tr1]
                unifyEq tcs (zipWith (flip Chg) trss (tail trss)) 
                return True

solveIneq tcsv tcp = do
    tcp' <- applySubst tcp
    r <- trace ("Solving inequality " ++ tcsv ++ " " ++ show tcp') $ case tcp' of
        (Ind, Ind) -> return $ Just TCSubRefl
        (Ind, tr1 `Chg` tr2) -> Just `fmap` (TCSubInd `fmap` unify tr1 tr2)
        (_ `Chg` _, Ind) -> fail "Constraint not satisfiable"
        (tr1 `Chg` tr2, tr1' `Chg` tr2') -> Just `fmap` (TCSubChg `fmap` unify tr1' tr1 `ap` unify tr2 tr2')
        (TCVar v, Ind) -> do
            unifyEq (TCVar v) Ind
            return (Just TCSubRefl)
        (tr1 `Chg` tr2, TCVar v) -> do
            [tr1', tr2'] <- replicateM 2 newTRVar
            unifyEq (TCVar v) (tr1' `Chg` tr2')
            Just `fmap` (TCSubChg `fmap` unify tr1' tr1 `ap` unify tr2 tr2')
        (TCVar v, TCVar w) | v == w -> return $ Just TCSubRefl
        _ -> return Nothing
    case r of
        Nothing -> return False
        Just tcs -> do
            modify $ \s -> s { tcsub_subst = Map.insert tcsv tcs $ substTCSub (Map.singleton tcsv tcs) $ tcsub_subst s }
            return True

insertMapList k v = Map.insertWith (++) k [v]
appendMapList k v = Map.insertWith (++) k v

addComp [] = return Ind
addComp tcs = do
    tc@(TCVar v) <- newTCVar
    modify $ \s -> s { comp_constr = (tc, tcs):comp_constr s }
    return tc

addIneq t1 t2 = do
    tcs@(TCSubVar v) <- newTCSubVar
    modify $ \s -> s { ineq_constr = Map.insert v (t1, t2) $ ineq_constr s }
    return tcs

class InferUnify t where
    type SubFor t
    type VarFor t
    unify :: t -> t -> InferMonad (SubFor t)
    unifyEq :: t -> t -> InferMonad ()
    extendSubst :: VarFor t -> t -> InferMonad ()

instance (InferUnify a, InferUnify b) => InferUnify (a, b) where
    type SubFor (a, b) = (SubFor a, SubFor b)
    type VarFor (a, b) = (VarFor a, VarFor b)
    unify (a, b) (a', b') = (,) `fmap` unify a a' `ap` unify b b'
    unifyEq (a, b) (a', b') = unifyEq a a' >> unifyEq b b'

instance InferUnify a => InferUnify [a] where
    type SubFor [a] = [SubFor a]
    type VarFor [a] = [VarFor a]
    unify as as' = mapM (uncurry unify) $ zip as as'
    unifyEq as as' = mapM_ (uncurry unifyEq) $ zip as as'

instance InferUnify Type where
    type SubFor Type = TPSub
    type VarFor Type = String
    unify t1 t2 = join $ unify' `fmap` applySubst t1 `ap` applySubst t2
        where
        unify' (Fun t tr) (Fun t' tr') = 
            TPSubFun `fmap` unify t' t `ap` unify tr tr'
        unify' TInt TInt = return TPSubRefl
        unify' (TADT _ ts) (TADT _ ts') = do
            subs <- mapM (uncurry unify) $ zip ts ts'
            guard $ all isSubRefl subs -- simplify - invariant typing for ADTs
            return TPSubRefl
        unify' (TVar v) (TVar w) | v == w = return TPSubRefl
        unify' (TVar v) t = extendSubst v t >> return TPSubRefl
        unify' t (TVar v) = extendSubst v t >> return TPSubRefl
        unify' t1 t2 = fail $ "Head mismatch: " ++ show t1 ++ " " ++ show t2
    unifyEq t1 t2 = join $ unify' `fmap` applySubst t1 `ap` applySubst t2
        where
        unify' (Fun t tr) (Fun t' tr') = 
            unifyEq t t' >> unifyEq tr tr'
        unify' TInt TInt = return ()
        unify' (TADT _ ts) (TADT _ ts') = 
            mapM_ (uncurry unifyEq) $ zip ts ts'
        unify' (TVar v) (TVar w) | v == w = return ()
        unify' (TVar v) t = extendSubst v t
        unify' t (TVar v) = extendSubst v t 
        unify' t1 t2 = fail $ "Head mismatch: " ++ show t1 ++ " " ++ show t2
    extendSubst v t | t /= TVar v && v `Set.member` freeTPvars t = fail $ "Occurs check: " ++ v ++ " occurs in " ++ show t
                    | otherwise = modify $ \s -> 
                        s { subst = substExtTP v t $ subst s }

instance InferUnify TC where
    type SubFor TC = TCSub
    type VarFor TC = String
    unify tc1 tc2 = join $ unify' `fmap` applySubst tc1 `ap` applySubst tc2
        where
        unify' Ind Ind = return TCSubRefl
        unify' Ind (tr1 `Chg` tr2) = TCSubInd `fmap` unify tr1 tr2
        unify' Ind (TCVar v) = addIneq Ind (TCVar v)
        unify' (_ `Chg` _) Ind = 
            fail $ "Cannot unify " ++ show tc1 ++ " with " ++ show tc2
        unify' (tr1 `Chg` tr2) (tr1' `Chg` tr2') = 
            TCSubChg `fmap` unify tr1' tr1 `ap` unify tr2 tr2'
        unify' (tr1 `Chg` tr2) (TCVar v) = 
            extendSubst v (tr1 `Chg` tr2) >> return TCSubRefl
        unify' (TCVar v) Ind = extendSubst v Ind >> return TCSubRefl
        unify' (TCVar v) (tr1 `Chg` tr2) =
            addIneq (TCVar v) (tr1 `Chg` tr2)
        unify' (TCVar v) (TCVar w) 
            | v == w    = return TCSubRefl
            | otherwise = addIneq (TCVar v) (TCVar w)
    unifyEq tc1 tc2 = join $ unify' `fmap` applySubst tc1 `ap` applySubst tc2
        where
        unify' Ind Ind = return ()
        unify' (tr1 `Chg` tr2) (tr1' `Chg` tr2') = 
            unifyEq tr1 tr1' >> unifyEq tr2 tr2'
        unify' (TCVar v) (TCVar w) | v == w = return ()
        unify' (TCVar v) tc = extendSubst v tc
        unify' tc (TCVar v) = extendSubst v tc
        unify' tc1 tc2 = fail $ "Head mismatch: " ++ show tc1 ++ " " ++ show tc2
    extendSubst v t | t /= TCVar v && v `Set.member` freeTCvars t = 
                        fail $ "Occurs check: " ++ v ++ " occurs in " ++ show t
                    | otherwise = do
                        modify $ \s -> s { subst = substExtTC v t $ subst s }

unifyTR_sub tr1 tr2 = do
    trs <- simplifySub `fmap` unify tr1 tr2
    return $ if isSubRefl trs then id else \x -> SubOf tr2 x trs

mytrace e x = trace (x ++ " " ++ pp e)

returnI tof = return (termOfTR tof, tof)

infer zz@(Var v) = mytrace zz "Infer" $ do
    t <- typeOf v
    returnI $ VarOf (t, Ind)
infer zz@(Lam _ e) = mytrace zz "Infer" $ do
    t <- newTVar
    (tr, d) <- extend t $ infer e
    returnI $ LamOf (Fun t tr, Ind) d
infer zz@(Sft _ e) = mytrace zz "Infer" $ do
    t <- newTVar
    tr <- newTRVar
    (tr', d) <- extend (Fun t tr) $ infer e
    returnI $ SftOf (t, tr `Chg` tr') d
infer zz@(Rst e) = mytrace zz "Infer" $ do
    (tr, d) <- infer e
    tv <- newTVar
    trv <- newTRVar
    trs <- unifyTR_sub tr (tv, (tv, Ind) `Chg` trv)
    returnI $ RstOf trv (trs d)
infer zz@(App e1 e2) = mytrace zz "Infer" $ do
    (tr1, d1) <- infer e1
    (tr2, d2) <- infer e2
    [tc1, tc2, tc3] <- replicateM 3 newTCVar
    [t1, t2] <- replicateM 2 newTVar
    tps1 <- unifyTR_sub tr1 (Fun t1 (t2, tc3), tc1)
    tps2 <- unifyTR_sub tr2 (t1, tc2)
    tc <- addComp [tc1, tc2, tc3]
    returnI $ AppOf (t2, tc) (tps1 d1) (tps2 d2)
infer zz@(IntLit _) = mytrace zz "Infer" $  returnI $ IntLitOf (TInt, Ind)
infer zz@(Cons consname es) = mytrace zz "Infer" $ do
    (adt, adtcons) <- lookupCons consname
    guard $ length es == length (adtConsParams adtcons)
    rs <- mapM infer es
    ts <- replicateM (length $ adtParams adt) newTVar
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    let pts = map (substWT subst) $ adtConsParams adtcons
    ptcs <- replicateM (length pts) newTCVar
    tpss <- forM (zip (map fst rs) (zip pts ptcs)) $ uncurry unifyTR_sub
    tc <- addComp ptcs
    returnI $ ConsOf (TADT (adtName adt) ts, tc) $ zipWith ($) tpss $ map snd rs
infer zz@(Case e es) = mytrace zz "Infer" $ do
    (adt, _) <- lookupCons ((\(consname,_,_) -> consname) (head es))
    let adtname = adtName adt
    ts <- replicateM (length $ adtParams adt) $ newTVar
    (tr, d) <- infer e
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    rs <- forM es $ \(consname,vars,e') -> do
        (adt', adtcons) <- lookupCons consname
        guard $ adtName adt == adtName adt'
        guard $ length vars == length (adtConsParams adtcons)
        foldr (.) id (map (extend . substWT subst) $ adtConsParams adtcons) $ infer e'
    t <- newTVar
    [tc1, tc2] <- replicateM 2 newTCVar
    tps <- unifyTR_sub tr (TADT adtname ts, tc1)
    tpss <- forM (zip (map fst rs) (repeat (t, tc2))) $ uncurry unifyTR_sub
    tc <- addComp [tc1, tc2]
    returnI $ CaseOf (t, tc) (tps d) $ zipWith ($) tpss $ map snd rs
infer zz@(Fix s e) = mytrace zz "Infer" $ do
    t <- newTVar
    ((t', Ind), d) <- extend t $ infer e
    tps <- unifyTR_sub (t', Ind) (t, Ind)
    returnI $ FixOf (t, Ind) (tps d) 

tryM f [] = return Nothing
tryM f (h:t) = do
    r <- f h
    if r then return $ Just h else tryM f t

-- inefficient, but works.
solveConstraints = do
    st <- get
    trace (unlines $ dumpConstraints st) $ return ()
    comps <- comp_constr `fmap` get
    res1 <- tryM (uncurry solveComp) comps
    case res1 of
        Just q -> do
            modify $ \s -> s { comp_constr = filter (/= q) $ comp_constr s }
            solveConstraints
        Nothing -> do
            ineqs <- ineq_constr `fmap` get
            res2 <- tryM (uncurry solveIneq) $ Map.toList ineqs
            case res2 of
                Just q -> do
                    modify $ \s -> s { ineq_constr = Map.delete (fst q) $ ineq_constr s }
                    solveConstraints
                Nothing -> return ()

dumpConstraints st = 
    map (\(k, l) -> pptc k ++ " =" ++ foldr (++) " " (map ((' ':) . pptc) l)) (substWT (subst st) $ comp_constr st) ++
    map (\(k, (v1, v2)) -> k ++ " =" ++ pptc v1 ++ " <=" ++ pptc v2) (map (id *** substWT (subst st)) $ Map.toList $ ineq_constr st)

infer' t = do
    r@(tr,_) <- infer t
    t <- newTVar
    unifyEq tr (t,Ind)
    trace "Solving" $ solveConstraints
    applySubst r

infFull :: ADTEnvs -> Term -> Either String (TR, TermOf, [(TC,[TC])], Map String (TC, TC))
infFull e t = case runState (runReaderT (runErrorT $ infer' t) (RSt 0 builtinTypeEnv e)) (St (Map.empty, Map.empty) 0 Map.empty Map.empty []) of
    (Left xx, _) -> Left xx
    (Right (tr, d), st) -> Right (tr, substTCSub (tcsub_subst st) d, substWT (subst st) $ comp_constr st, substWT (subst st) $ ineq_constr st)

backtracking [] = fail "Options exhausted"
backtracking (k:ks) = do
    ss <- get
    k `catchError` \k -> put ss >> backtracking ks

tcSize (TCVar _) = 1
tcSize Ind = 2
tcSize (tr1 `Chg` tr2) = 3 + trSize tr1 + trSize tr2

trSize (a, b) = tpSize a + tcSize b

tpSize TInt = 2
tpSize (TADT _ ts) = 2 + sum (map tpSize ts)
tpSize (Fun t tr) = 2 + tpSize t + trSize tr
tpSize (TVar _) = 1

compIneqs (tr1, tr2) (tr1', tr2') = (tcSize tr1' + tcSize tr2') `compare` (tcSize tr1 + tcSize tr2)

mkGround = do
    solveConstraints
    ineqs <- ineq_constr `fmap` get
    case Map.toList ineqs of
        [] -> return ()
        l -> do
            (h:al) <- sortBy compIneqs `fmap` applySubst (map snd l)
            opts <- trace (show h) $ case h of
                    (Ind, TCVar v) -> 
                        return [
                            unifyEq (TCVar v) Ind,
                            do [tr1, tr2] <- replicateM 2 newTRVar
                               unifyEq (TCVar v) (tr1 `Chg` tr2)
                        ]
                    (TCVar v, _ `Chg` _) -> 
                        return [
                         unifyEq (TCVar v) Ind,
                         do [tr1, tr2] <- replicateM 2 newTRVar
                            unifyEq (TCVar v) (tr1 `Chg` tr2)
                        ]
--                    (TCVar v, TCVar w) -> return [unifyEq (TCVar v) (TCVar w)]
                    _ -> return []
            let opts' = case opts of
                    [] -> map (uncurry unifyEq) (h:al)
                    o -> o
            backtracking $ map (\x -> x >> mkGround) opts

makeGround (t, tr) = trace "Grounding" $ do
    mkGround
    tcss <- tcsub_subst `fmap` get
    trace (show tcss) $ trace (show tr) $ trace (show $ substTCSub tcss tr) $ applySubst (t, substTCSub tcss tr)

inf :: ADTEnvs -> Term -> Either String (TR, TermOf)
inf e t = evalState (runReaderT (runErrorT $ makeGround =<< infer' t) (RSt 0 builtinTypeEnv e)) (St (Map.empty, Map.empty) 0 Map.empty Map.empty []) 

{-
inf :: ADTEnvs -> Term -> Either String (TR, TermOf)
inf e t = case infFull e t of
    Left xx -> Left xx
    Right (tr, d, x, y) -> Right (tr, d)
-}
