module Typecheck(chk) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Error

import Data.Maybe
import qualified Data.Map as Map
import Data.Map(Map)

import Lang
import PrettyPrint

guard' = flip unless . fail

type Ctx = Map Var Type

data St = St { depth :: Int, ctx :: Ctx, adtEnvs :: ADTEnvs }

adtEnv = fst . adtEnvs
adtConsEnv = snd . adtEnvs

extend t m = local (\s -> s { depth = depth s + 1, ctx = Map.insert (BVar (depth s + 1)) t (ctx s) }) m

typeOf (FVar s) = maybe (fail "x") return =<< Map.lookup (FVar s) `fmap` (ctx `fmap` ask)
typeOf (BVar k) = maybe (fail "x") return =<< Map.lookup `fmap` (BVar `fmap` ((+(-k)) `fmap` (depth `fmap` ask))) `ap` (ctx `fmap` ask)

lookupCons consname = maybe (fail "x") return =<< Map.lookup consname `fmap` (adtConsEnv `fmap` ask)
lookupADT adtname = maybe (fail "x") return =<< Map.lookup adtname `fmap` (adtEnv `fmap` ask)

checkTRSub (tps, tcs) (t, s) (t', s') = 
    checkTPSub tps t t' && checkTCSub tcs s s'

checkTPSub TPSubRefl t t' = t == t'
checkTPSub (TPSubFun tps trs) (Fun t tr) (Fun t' tr') =
    checkTPSub tps t' t && checkTRSub trs tr tr'
checkTPSub _ _ _ = False

checkTCSub TCSubRefl tc tc' = tc == tc'
checkTCSub (TCSubInd trs) Ind (tr `Chg` tr') = checkTRSub trs tr tr'
checkTCSub (TCSubChg trs1 trs2) (tr1 `Chg` tr2) (tr1' `Chg` tr2') = 
    checkTRSub trs1 tr1' tr1 && checkTRSub trs2 tr2 tr2'
checkTCSub _ _ _ = False

returnC cname otr tr = guard' (cname ++ ": Return: " ++ pptr otr ++ " not equals " ++ pptr tr) (otr == tr) >> return tr

check (Var v) (VarOf otr) = do
    t <- typeOf v
    returnC "Var" otr (t, Ind)
check (Lam _ e) (LamOf otr@(Fun t _, _) d) = do
    tr <- extend t $ check e d
    returnC "Lam" otr (Fun t tr, Ind)
check (App e1 e2) (AppOf otr d1 d2) = do
    (Fun t1 (t2, tc3), tc1) <- check e1 d1
    (t3, tc2) <- check e2 d2
    guard' "app" $ t3 == t1
    case (tc1, tc2, tc3) of
        (Ind, Ind, Ind) -> returnC "App" otr (t2, Ind)
        (tr1 `Chg` tr2, tr3 `Chg` tr4, tr5 `Chg` tr6) -> do
            guard' "app" $ tr1 == tr4 && tr3 == tr6
            returnC "App" otr (t2, tr5 `Chg` tr2)
        z -> fail $ show z
check (Rst e) (RstOf otr d) = do
    (t1, (t2, Ind) `Chg` tr) <- check e d
    guard' "rst" $ t1 == t2
    returnC "Rst" otr tr
check (Sft _ e) (SftOf otr@(t, tr `Chg` _) d) = do
    tr' <- extend (Fun t tr) $ check e d
    returnC "Sft" otr (t, tr `Chg` tr')
check (IntLit _) (IntLitOf otr) = returnC "IntLit" otr (TInt, Ind)
check (Cons consname es) (ConsOf otr@(TADT _ ts, _) ds) = do
    (adt, adtcons) <- lookupCons consname
    guard' "cons" $ length ts == length (adtParams adt)
    guard' "cons" $ length es == length (adtConsParams adtcons)
    guard' "cons" $ length es == length ds
    rs <- forM (zip es ds) $ uncurry check 
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    guard' "cons" $ all (uncurry (==)) $ zip (map fst rs) (map (substWT subst) $ adtConsParams adtcons)
    case map snd rs of
        tcs | all isInd tcs ->
                returnC "Cons" otr (TADT (adtName adt) ts, Ind)
            | all isChg tcs -> do
                let tcs' = map (\(tr1 `Chg` tr2) -> (tr1, tr2)) tcs
                guard' "cons" $ all (uncurry (==)) $ zip (map fst tcs') (tail $ map snd tcs')
                returnC "Cons" otr (TADT (adtName adt) ts, (fst $ last tcs') `Chg` (snd $ head tcs'))
{-
check (Cons consname es) (ConsPOf ts ds) = do
    (adt, adtcons) <- lookupCons consname
    guard $ length ts == length (adtParams adt)
    guard $ length es == length (adtConsParams adtcons)
    guard $ length es == length ds
    rs <- forM (zip es ds) $ \(e,d) -> do
        (t, Ind) <- check e d
        return t
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    guard $ all (uncurry (==)) $ zip rs (map (substWT subst) $ adtConsParams adtcons)
    return (TADT (adtName adt) ts, Ind)
check (Case e es) (CasePOf d ds) = do
    (TADT adtname ts, Ind) <- check e d
    adt <- lookupADT adtname
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    rs <- forM (zip es ds) $ \((consname,vars,e),d) -> do
        (adt', adtcons) <- lookupCons consname
        guard $ adtName adt == adtName adt'
        guard $ length vars == length (adtConsParams adtcons)
        (t, Ind) <- foldr (.) id (map (extend . substWT subst) $ adtConsParams adtcons) $ check e d
        return t
    guard $ all (uncurry (==)) $ zip rs (tail rs)
    return (head rs, Ind)
-}
check (Case e es) (CaseOf otr d ds) = do
    (TADT adtname ts, tc1) <- check e d
    adt <- lookupADT adtname
    let subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
    rs <- forM (zip es ds) $ \((consname,vars,e),d) -> do
        (adt', adtcons) <- lookupCons consname
        guard' "Case" $ adtName adt == adtName adt'
        guard' "Case" $ length vars == length (adtConsParams adtcons)
        foldr (.) id (map (extend . substWT subst) $ adtConsParams adtcons) $ check e d
    guard' "Case" $ all (uncurry (==)) $ zip rs (tail rs)
    case (tc1, snd $ head rs) of
        (Ind, Ind) -> returnC "Case" otr (fst $ head rs, Ind)
        (tr1 `Chg` tr2, tr3 `Chg` tr4) -> do
            guard $ tr1 == tr4
            returnC "Case" otr (fst $ head rs, tr3 `Chg` tr2)
check zz@(Fix s e) (FixOf otr@(t, _) d) = do
    (t', Ind) <- extend t $ check e d
    guard' ("Fix: " ++ pp zz ++ ": " ++ ppt t' ++ "not equals " ++ ppt t) $ t' == t
    returnC "Fix" otr (t, Ind)
check e (SubOf otr d sub) = do
    tr' <- check e d
    guard' ("Sub: " ++ pp e ++ ": " ++ pptr tr' ++ " <= " ++ pptr otr ++ " not witnessed by " ++ show sub) $ checkTRSub sub tr' otr
    return otr
check _ _ = fail "y"

chk :: ADTEnvs -> Term -> TermOf -> Either String TR
chk e t to = runReader (runErrorT $ check t to) (St 0 builtinTypeEnv e)

