{-# OPTIONS_GHC -fglasgow-exts #-}
module PrintDeriv(ppof) where

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import qualified Data.Map as Map
import Data.Map(Map)
import Data.List(intersperse)

import Lang
import PrettyPrint

data RSt = RSt { 
    vars :: [(String, Type)], 
    depth :: Int, 
    ldepth :: Int,
    ddepth :: Int,
    adtEnvs :: ADTEnvs }

data St = St { branches :: Map Int Char }

type DerivMonad = WriterT [String] (ReaderT RSt (State St))

subderiv m = local (\s -> s { ddepth = ddepth s + 1, ldepth = depth s }) $ do
    d <- ddepth `fmap` ask
    modify $ \s -> s { branches = Map.insert d ' ' $ branches s }
    m
    modify $ \s -> s { branches = Map.delete d $ branches s }

extend x t = local (\s -> s { depth = depth s + 1, vars = (x,t):vars s })

linelen = 100

ruleName (VarOf _) = "VAR"
ruleName (LamOf _ _) = "ABS"
ruleName (AppOf _ _ _) = "APP"
ruleName (RstOf _ _) = "RST"
ruleName (SftOf _ _) = "SFT"
ruleName (SubOf _ _ trsub) = "SUB " ++ show trsub
ruleName (IntLitOf _) = "INT"
ruleName (ConsOf _ _) = "CONS"
ruleName (CaseOf _ _ _) = "CASE"
ruleName (FixOf _ _) = "FIX"

printFinal rn l = do
    d <- ddepth `fmap` ask
    modify $ \s -> s { branches = Map.update (`lookup` [(' ',','),('|','+')]) d $ branches s }
    br <- (map snd . Map.toList . branches) `fmap` get
    let ln = intersperse ' ' br ++ "--- " ++ l
    tell [ln ++ replicate (80 - length ln) ' ' ++ rn]
    modify $ \s -> s { branches = Map.insert d '|' $ branches s }

printJudgement e d = do
    num <- (-) `fmap` (depth `fmap` ask) `ap` (ldepth `fmap` ask)
    vs <- (map (id *** ppt) . vars) `fmap` ask
    let vsp = concat $ intersperse ", " $ map (\(x,y) -> x ++ " : " ++ y) (take num vs) ++ map fst (drop num vs)
    printFinal (ruleName d) $ vsp ++ (if vsp == [] then "" else " ") ++ "|- " ++ ppV (map fst vs) e ++ " : " ++ pptr (termOfTR d)

printDeriv e d = do
    a <- adtEnvs `fmap` ask
    subderiv $ forM_ (termOfDerivs a e d) $ \(vs,e,d) -> 
        foldr (.) id (map (uncurry extend) vs) $ printDeriv e d
    printJudgement e d

ppof a e d = concat $ map (++"\n") $ snd $ evalState (runReaderT (runWriterT (printDeriv e d)) (RSt [] 0 0 0 a)) (St Map.empty)

