{-# OPTIONS_GHC -fglasgow-exts #-}
module Lang where

import Control.Arrow
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe

data Var = FVar String | BVar Int deriving (Show, Ord, Eq)

type TR = (Type, TC)

data TC = TCVar String | Ind | TR `Chg` TR deriving (Show, Eq)

data Type = TVar String 
          | Fun Type TR 
          | TInt 
          | TADT String [Type] deriving (Show, Eq)

data ADT = ADT { 
        adtName :: String, 
        adtParams :: [String], 
        adtCons :: [ADTCons]
    }

data ADTCons = ADTCons {
        adtConsName :: String,
        adtConsParams :: [Type]
    }

type ADTEnv = Map String ADT
type ADTConsEnv = Map String (ADT, ADTCons)

type ADTEnvs = (ADTEnv, ADTConsEnv)

data TCSub = TCSubRefl
           | TCSubInd TRSub 
           | TCSubChg TRSub TRSub 
           | TCSubVar String
       deriving (Show, Eq)

data TPSub = TPSubRefl 
           | TPSubFun TPSub TRSub 
        deriving (Show, Eq)

type TRSub = (TPSub, TCSub)

type CaseOpt = (String, [String], Term)

data Term = Var Var 
          | Lam String Term
          | App Term Term
          | Rst Term
          | Sft String Term
          | IntLit Integer
          | Cons String [Term]
          | Case Term [CaseOpt]
          | Fix String Term
        deriving (Show, Eq)

data ECtx = CEmpty | CAppl ECtx Term | CAppr Term ECtx | CRst ECtx 
          | CCons String [Term] ECtx [Term]
          | CCase ECtx [CaseOpt]
    deriving (Show, Eq)

data TermOf = VarOf TR
            | LamOf TR TermOf
            | AppOf TR TermOf TermOf
            | RstOf TR TermOf
            | SftOf TR TermOf
            | SubOf TR TermOf TRSub 
            | IntLitOf TR
            | ConsOf TR [TermOf]
            | CaseOf TR TermOf [TermOf]
            | FixOf TR TermOf 
        deriving (Show, Eq)

tcVarName (TCVar v) = v

termOfTR (VarOf tr) = tr
termOfTR (LamOf tr _) = tr
termOfTR (AppOf tr _ _) = tr
termOfTR (RstOf tr _) = tr
termOfTR (SftOf tr _) = tr
termOfTR (SubOf tr _ _) = tr
termOfTR (IntLitOf tr) = tr
termOfTR (ConsOf tr _) = tr
termOfTR (CaseOf tr _ _) = tr
termOfTR (FixOf tr _) = tr

termOfDerivs _ _ (VarOf _) = []
termOfDerivs _ (Lam x e) (LamOf (Fun t _, _) d) = [([(x,t)],e,d)]
termOfDerivs _ (App e1 e2) (AppOf _ d1 d2) = [([],e1,d1), ([],e2,d2)]
termOfDerivs _ (Rst e) (RstOf _ d) = [([],e,d)]
termOfDerivs _ (Sft x e) (SftOf (t, tr `Chg` _) d) = [([(x,Fun t tr)],e,d)]
termOfDerivs _ e (SubOf _ d _) = [([],e,d)]
termOfDerivs _ _ (IntLitOf _) = []
termOfDerivs _ (Cons _ es) (ConsOf _ ds) = map (\(e,d) -> ([],e,d)) (zip es ds)
termOfDerivs a (Case e os) (CaseOf _ cd ds) = ([],e,cd):map varsFor (zip ds os)
    where varsFor (d, (cname, vnames, e)) = (zip vnames vtypes, e, d) where
            vtypes = map (substWT subst) $ adtConsParams adtcons
            (adt, adtcons) = fromJust $ Map.lookup cname (snd a)
            (TADT _ ts, _) = termOfTR cd
            subst = (Map.fromList $ zip (adtParams adt) ts, Map.empty)
termOfDerivs _ (Fix x e) (FixOf (t, _) d) = [([(x,t)],e,d)]

stdadt = [
    ADT "Unit" [] [
        ADTCons "Unit" []
    ],
    ADT "Bool" [] [
        ADTCons "True" [],
        ADTCons "False" []
    ],
    ADT "Tuple2" ["t1","t2"] [
        ADTCons "Tuple2" [TVar "t1", TVar "t2"]
    ],
    ADT "Tuple3" ["t1","t2","t3"] [
        ADTCons "Tuple3" [TVar "t1", TVar "t2", TVar "t3"]
    ],
    ADT "List" ["t"] [
        ADTCons "Nil" [],
        ADTCons "Cons" [TVar "t", TADT "List" [TVar "t"]]
    ],
    ADT "Maybe" ["t"] [
        ADTCons "Nothing" [],
        ADTCons "Just" [TVar "t"]
    ],
    ADT "Tree" ["t"] [
        ADTCons "Leaf" [],
        ADTCons "Node" [TADT "Tree" [TVar "t"], TVar "t", TADT "Tree" [TVar "t"]]
    ]]

adtToEnvs adts = (Map.fromList adtl, Map.fromList adtcl) where
    adtl = map (adtName &&& id) adts
    adtcl = concat $ flip map adts $ \adt -> map (adtConsName &&& (const adt &&& id)) $ adtCons adt

builtinTypes = [
    ("+", (Fun TInt ((Fun TInt (TInt, Ind)), Ind))),
    ("-", (Fun TInt ((Fun TInt (TInt, Ind)), Ind))),
    ("*", (Fun TInt ((Fun TInt (TInt, Ind)), Ind))),
    ("/", (Fun TInt ((Fun TInt (TInt, Ind)), Ind))),
    ("==", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind))),
    ("/=", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind))),
    ("%<=", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind))),
    ("%>=", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind))),
    ("%<", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind))),
    ("%>", (Fun TInt ((Fun TInt (TADT "Bool" [], Ind)), Ind)))]

builtinTypeEnv = Map.fromList (map (FVar *** id) builtinTypes)

isInd Ind = True
isInd _ = False

isChg (_ `Chg` _) = True
isChg _ = False

freevars (Var (FVar s)) = Set.singleton s
freevars (Var _) = Set.empty
freevars (Lam _ e) = freevars e
freevars (App e1 e2) = freevars e1 `Set.union` freevars e2
freevars (Rst e) = freevars e
freevars (Sft _ e) = freevars e
freevars (IntLit _) = Set.empty
freevars (Cons _ es) = Set.unions (map freevars es)
freevars (Case e es) = freevars e `Set.union` (Set.unions $ map (\(_,_,x) -> freevars x) es)
freevars (Fix _ e) = freevars e

type SubstTP = Map String Type
type SubstTC = Map String TC
type Subst = (SubstTP, SubstTC)

substExtTP v t (st, stc) = substWT1TP v t (Map.insert v t st, stc)
substExtTC v t (st, stc) = substWT1TC v t (st, Map.insert v t stc)

substWT1TP v t = substWT (Map.singleton v t, Map.empty) 
substWT1TC v t = substWT (Map.empty, Map.singleton v t) 

class WithTypes t where
    substWT :: Subst -> t -> t
    freeTPvars :: t -> Set String
    freeTCvars :: t -> Set String

instance WithTypes a => WithTypes (Map x a) where
    substWT s = Map.map (substWT s)
    freeTPvars = undefined
    freeTCvars = undefined

instance (WithTypes a, WithTypes b) => WithTypes (a, b) where
    substWT s (a, b) = (substWT s a, substWT s b)
    freeTPvars (a, b) = freeTPvars a `Set.union` freeTPvars b
    freeTCvars (a, b) = freeTCvars a `Set.union` freeTCvars b

instance WithTypes a => WithTypes [a] where
    substWT s l = map (substWT s) l
    freeTPvars l = Set.unions $ map freeTPvars l
    freeTCvars l = Set.unions $ map freeTCvars l

instance WithTypes Type where
    substWT (ts, _) (TVar s) = maybe (TVar s) id $ Map.lookup s ts
    substWT s (Fun t tr) = Fun (substWT s t) (substWT s tr)
    substWT _ TInt = TInt
    substWT s (TADT n ts) = TADT n (map (substWT s) ts)
    freeTPvars (TVar s) = Set.singleton s
    freeTPvars (Fun t tr) = freeTPvars t `Set.union` freeTPvars tr
    freeTPvars TInt = Set.empty
    freeTPvars (TADT _ ts) = Set.unions (map freeTPvars ts)
    freeTCvars (TVar _) = Set.empty
    freeTCvars (Fun t tr) = freeTCvars t `Set.union` freeTCvars tr
    freeTCvars TInt = Set.empty
    freeTCvars (TADT _ ts) = Set.unions (map freeTCvars ts)

instance WithTypes TC where
    substWT (_, tcs) (TCVar s) = maybe (TCVar s) id $ Map.lookup s tcs
    substWT _ Ind = Ind
    substWT s (tr1 `Chg` tr2) = substWT s tr1 `Chg` substWT s tr2
    freeTPvars (TCVar _) = Set.empty
    freeTPvars Ind = Set.empty
    freeTPvars (tr1 `Chg` tr2) = freeTPvars tr1 `Set.union` freeTPvars tr2
    freeTCvars (TCVar s) = Set.singleton s
    freeTCvars Ind = Set.empty
    freeTCvars (tr1 `Chg` tr2) = freeTCvars tr1 `Set.union` freeTCvars tr2

instance WithTypes TermOf where
    substWT s (VarOf tr) = VarOf (substWT s tr)
    substWT s (LamOf tr d) = LamOf (substWT s tr) (substWT s d)
    substWT s (AppOf tr d1 d2) = AppOf (substWT s tr) (substWT s d1) (substWT s d2)
    substWT s (RstOf tr d) = RstOf (substWT s tr) (substWT s d)
    substWT s (SftOf tr d) = SftOf (substWT s tr) (substWT s d)
    substWT s (SubOf tr d sub) = SubOf (substWT s tr) (substWT s d) sub
    substWT s (IntLitOf tr) = IntLitOf (substWT s tr)
    substWT s (ConsOf tr ds) = ConsOf (substWT s tr) (map (substWT s) ds)
    substWT s (CaseOf tr d ds) = CaseOf (substWT s tr) (substWT s d) (map (substWT s) ds)
    substWT s (FixOf tr d) = FixOf (substWT s tr) (substWT s d)
    freeTPvars = error "not implemented"
    freeTCvars = error "not implemented"

class WithTCSub t where
    substTCSub :: Map String TCSub -> t -> t

instance WithTCSub a => WithTCSub (Map x a) where
    substTCSub s = Map.map (substTCSub s)

instance WithTCSub TermOf where
    substTCSub _ (VarOf tr) = VarOf tr
    substTCSub s (LamOf tr d) = LamOf tr (substTCSub s d)
    substTCSub s (AppOf tr d1 d2) = AppOf tr (substTCSub s d1) (substTCSub s d2)
    substTCSub s (RstOf tr d) = RstOf tr (substTCSub s d)
    substTCSub s (SftOf tr d) = SftOf tr (substTCSub s d)
    substTCSub s (SubOf tr d sub) | isSubRefl sub' = substTCSub s d
                                  | otherwise = SubOf tr (substTCSub s d) sub'
        where
        sub' = substTCSub s sub
    substTCSub _ (IntLitOf tr) = IntLitOf tr
    substTCSub s (ConsOf tr ds) = ConsOf tr (map (substTCSub s) ds)
    substTCSub s (CaseOf tr d ds) = CaseOf tr (substTCSub s d) (map (substTCSub s) ds)
    substTCSub s (FixOf tr d) = FixOf tr (substTCSub s d)

instance WithTCSub TCSub where
    substTCSub s (TCSubVar v) | Just tcs <- Map.lookup v s = tcs
                              | otherwise = TCSubVar v
    substTCSub s TCSubRefl = TCSubRefl
    substTCSub s (TCSubInd trs) = TCSubInd (substTCSub s trs)
    substTCSub s (TCSubChg trs1 trs2) = TCSubChg (substTCSub s trs1) (substTCSub s trs2)

instance WithTCSub TPSub where
    substTCSub s TPSubRefl = TPSubRefl
    substTCSub s (TPSubFun tps trs) = TPSubFun (substTCSub s tps) (substTCSub s trs)

instance (WithTCSub a, WithTCSub b) => WithTCSub (a, b) where
    substTCSub s (a, b) = (substTCSub s a, substTCSub s b)

class Subtyping s where
    simplifySub :: s -> s
    isSubRefl :: s -> Bool

instance (Subtyping a, Subtyping b) => Subtyping (a, b) where
    simplifySub (a, b) = (simplifySub a, simplifySub b)
    isSubRefl (a, b) = isSubRefl a && isSubRefl b

instance Subtyping TPSub where
    simplifySub TPSubRefl = TPSubRefl
    simplifySub (TPSubFun tps trs) | isSubRefl (tps', trs') = TPSubRefl
                                   | otherwise = TPSubFun tps' trs'
        where (tps', trs') = simplifySub (tps, trs)
    isSubRefl TPSubRefl = True
    isSubRefl (TPSubFun tps trs) = isSubRefl tps && isSubRefl trs

instance Subtyping TCSub where
    simplifySub (TCSubVar v) = TCSubVar v
    simplifySub TCSubRefl = TCSubRefl
    simplifySub (TCSubInd trs) = TCSubInd (simplifySub trs)
    simplifySub (TCSubChg trs1 trs2) | isSubRefl (trs1, trs2) = TCSubRefl
                                     | otherwise = TCSubChg trs1' trs2'
        where (trs1', trs2') = simplifySub (trs1, trs2)
    isSubRefl (TCSubVar v) = False
    isSubRefl TCSubRefl = True
    isSubRefl (TCSubInd _) = False
    isSubRefl (TCSubChg trs1 trs2) = isSubRefl trs1 && isSubRefl trs2

isValue (Lam _ _) = True
isValue (Var _) = True
isValue (Cons _ es) = all isValue es
isValue (IntLit _) = True
isValue _ = False

substBind e = renumber (-1) . substVar (BVar 0) (renumber 1 e)

renVar _ (FVar s) = FVar s
renVar k (BVar n) = BVar $ n + k

substVar v x (Var v') | v == v' = x
                   | otherwise = Var v'
substVar v x (App e1 e2) = App (substVar v x e1) (substVar v x e2)
substVar v x (Rst e) = Rst (substVar v x e)
substVar v x (Lam z e) = Lam z (substVar (renVar 1 v) (renumber 1 x) e) where
substVar v x (Sft z e) = Sft z (substVar (renVar 1 v) (renumber 1 x) e) where
substVar v x (Fix z e) = Fix z (substVar (renVar 1 v) (renumber 1 x) e) where
substVar _ _ (IntLit k) = IntLit k
substVar v x (Cons s es) = Cons s (map (substVar v x) es)
substVar v x (Case e es) = Case (substVar v x e) (map scase es) where
    scase (s, p, e) = (s, p, substVar (renVar k v) (renumber k x) e)
        where k = length p

renumber n e = renumber' 0 e where
    renumber' _ (Var (FVar s)) = Var $ FVar s
    renumber' b (Var (BVar k)) | k < b     = Var $ BVar k
                               | otherwise = Var $ BVar $ k + n
    renumber' b (App e1 e2) = App (renumber' b e1) (renumber' b e2)
    renumber' b (Rst e) = Rst (renumber' b e)
    renumber' b (Lam x e) = Lam x (renumber' (b+1) e)
    renumber' b (Sft x e) = Sft x (renumber' (b+1) e)
    renumber' b (Fix x e) = Fix x (renumber' (b+1) e)
    renumber' _ (IntLit k) = IntLit k
    renumber' b (Cons s es) = Cons s (map (renumber' b) es)
    renumber' b (Case e es) = Case (renumber' b e) (map ren es) where
        ren (s, p, e) = (s, p, renumber' (b+length p) e)

