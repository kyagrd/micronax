module Main where

import Prelude hiding (exp)
import Parser
import Language.LBNF

e = [exp| 1 + 1 |]

e1 = [exp| 1 + {-2 +-} 3 |]

-- | The main entry point.
main :: IO ()
main = do
    putStrLn "Welcome to FP Haskell Center!"
    putStrLn "Input a line:"
    putStrLn $ show e1
    putStrLn $ printTree e1