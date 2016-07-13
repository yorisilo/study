{-# OPTIONS_GHC -fglasgow-exts #-}
module PrettyPrint(pp,ppV,ppt,pptr,pptc) where

import Control.Monad
import Control.Monad.Reader

import qualified Data.Set as Set
import Data.Set(Set)
import Data.Char

import Lang

data St = St { vars :: [String], fvars :: Set String }

output s = return (s ++) 
varName k = ((!! k) . (++ repeat "U")) `fmap` (vars `fmap` ask)

infixr 0 +++

a +++ b = (.) `fmap` a `ap` b
isTaken v = Set.member v `fmap` (fvars `fmap` ask)
avoid v = do
	b <- isTaken v
	if b then avoid (v++"'") else return v
extend v m = do
	v' <- avoid v
	local (\s -> s { vars = v':vars s, fvars = v' `Set.insert` fvars s }) m
parens False m = m
parens True m = output "(" +++ m +++ output ")"

listTerm (Cons "Nil" []) = Just []
listTerm (Cons "Cons" [h,t]) | Just l <- listTerm t = Just (h:l)
listTerm _ = Nothing

sepBy [] _ = output ""
sepBy [k] _ = k
sepBy (k:ks) sep = k +++ sep +++ sepBy ks sep

builtinBinaryOps = [
    ("==",(1,2,2)),
    ("/=",(1,2,2)),
    ("%<=",(1,2,2)),
    ("%>=",(1,2,2)),
    ("%<",(1,2,2)),
    ("%>",(1,2,2)),
    ("+",(2,2,3)),
    ("-",(2,2,3)),
    ("*",(3,3,4)),
    ("/",(3,3,4))]

ppTerm pr (Var (FVar s)) = output s
ppTerm pr (Var (BVar k)) = output =<< varName k
ppTerm pr (Lam v e) = parens (pr > 0) $ extend v $
	output "\\" +++ output =<< varName 0 +++ output ". " +++ ppTerm 0 e
ppTerm pr (App (App (Var (FVar s)) e1) e2) | Just (k,l,m) <- lookup s builtinBinaryOps = parens (pr > k) $
    ppTerm l e1 +++ output (" " ++ s ++ " ") +++ ppTerm m e2
ppTerm pr (App e1 e2) = parens (pr > 4) $
	ppTerm 4 e1 +++ output " " +++ ppTerm 5 e2
ppTerm pr (Rst e) = output "<" +++ ppTerm 0 e +++ output ">"
ppTerm pr (Sft v e) = parens (pr > 0) $ extend v $
	output "@" +++ output =<< varName 0 +++ output ". " +++ ppTerm 0 e
ppTerm pr (Fix v e) = parens (pr > 0) $ extend v $
	output "fix " +++ output =<< varName 0 +++ output ". " +++ ppTerm 0 e
ppTerm pr (IntLit k) = output $ show k
ppTerm pr e | Just es <- listTerm e = output "[" +++ sepBy (map (ppTerm 0) es) (output ", ") +++ output "]"
ppTerm pr (Cons "Unit" []) = output "()"
ppTerm pr (Cons ('T':'u':'p':'l':'e':s) es) | all isDigit s && read s == length es = 
    output "(" +++ sepBy (map (ppTerm 0) es) (output ", ") +++ output ")"
ppTerm pr (Cons s []) = output s
ppTerm pr (Cons s es) = output s +++ output "(" +++ sepBy (map (ppTerm 0) es) (output ", ") +++ output ")"
ppTerm pr (Case e [("True",[],e1),("False",[],e2)]) = parens (pr > 0) $
    output "if " +++ ppTerm 0 e +++ output " then " +++ ppTerm 0 e1 +++ output " else " +++ ppTerm 0 e2
ppTerm pr (Case e es) = output "case " +++ ppTerm pr e +++ output " { " +++ sepBy (map ppcase es) (output " | ") +++ output " }" where
    ppcase (s,[],e) = output s +++ output " -> " +++ ppTerm 0 e
    ppcase (s,vs,e) = output s +++ output "(" +++ sepBy (map output vs) (output ", ") +++ output ") -> "  +++ (foldr (.) id (map extend vs) $ ppTerm 0 e)

pp t = runReader (ppTerm 0 t) (St [] (freevars t)) ""

ppV v t = runReader (ppTerm 0 t) (St v (freevars t)) ""

ppTR (t, tc) = ppType 1 t . ppTC tc

ppTC Ind = id
ppTC (tr1 `Chg` tr2) = (" ["++) . ppTR tr1 . ("] "++) . ppTR tr2
ppTC (TCVar v) = (" "++) . (v++)

ppType pr (Fun t tr) = showParen (pr > 0) $ ppType 1 t . (" -> "++) . ppTR tr
ppType pr TInt = ("int"++)
ppType pr (TADT s ts) = (s++) . foldr (.) id (map (\t -> (" "++) . ppType 1 t) ts)
ppType pr (TVar s) = (s++)

ppt t = ppType 0 t ""

pptr tr = ppTR tr ""

pptc tr = ppTC tr ""

