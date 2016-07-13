module Main where

import Lang
import Parse
import PrettyPrint
import PrintDeriv
import Typecheck
import Typeinfer
import Eval

import Control.Monad

import qualified Data.Map

main = do
    d <- getContents
    e <- either (fail . show) return $ pr d
    (t, d, c1, c2) <- either (fail . ("Infer error: " ++)) return $ infFull (adtToEnvs stdadt) e
    putStrLn $ ppof (adtToEnvs stdadt) e d
    forM c1 $ \(k, l) ->
        putStrLn $ pptc k ++ " =" ++ foldr (++) " " (map ((' ':) . pptc) l)
    forM (Data.Map.toList c2) $ \(k, (v1, v2)) ->
        putStrLn $ k ++ " =" ++ pptc v1 ++ " <=" ++ pptc v2
    (t, d) <- either (fail . ("Infer error: " ++)) return $ inf (adtToEnvs stdadt) e
    putStrLn $ ppof (adtToEnvs stdadt) e d
    t' <- either (fail . ("Check error: " ++)) return $ chk (adtToEnvs stdadt) e d
    guard $ t == t'
    putStrLn $ pp e ++ " : " ++ pptr t
    forM (eval e) $ putStrLn . pp
