{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Foil
import Data.String (fromString)
import Language.Lambda.Impl.FoilTH

-- >>> printFoilTerm (nf emptyScope (fromString "λx. x"))
-- "λ x . x"
example1 :: String
example1 = printFoilTerm (nf emptyScope (fromString "λx. x"))

-- >>> printFoilTerm (nf emptyScope (fromString "((λx. x) y)"))
-- "y"
example2 :: String
example2 = printFoilTerm (nf emptyScope (fromString "((λx. x) y)"))

-- >>> printFoilTerm (nf emptyScope (fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)"))
-- "λ x1 . λ x2 . x1"
example3 :: String
example3 = printFoilTerm (nf emptyScope (fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)"))

main :: IO ()
main = do
  putStrLn example1
  putStrLn example2
  putStrLn example3
