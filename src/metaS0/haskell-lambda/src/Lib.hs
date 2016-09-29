module Lib
    ( someFunc
    ) where

import qualified Data.Map as M

someMap :: M.Map String String
someMap = M.fromList [("stack exec", "Hello, world!")]

someFunc :: IO ()
someFunc = print $ M.lookup "stack exec" someMap
