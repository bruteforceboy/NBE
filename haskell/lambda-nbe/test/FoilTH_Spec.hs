{-# LANGUAGE OverloadedStrings #-}

module FoilTH_Spec (spec) where

import Control.Monad.Foil
import Data.String (fromString)
import Language.Lambda.Impl.FoilTH
import Test.Hspec

spec :: Spec
spec = describe "nf normalization tests" $ do
  it "Test 1: nf of identity" $
    printFoilTerm (nf emptyScope (fromString "λx. x")) `shouldBe` printFoilTerm (fromString "λx. x")
  it "Test 2: nf of ((λx. x) y)" $
    printFoilTerm (nf emptyScope (fromString "((λx. x) y)")) `shouldBe` "y"
  it "Test 3: nf of nested lambda (1)" $ do
    let term = fromString "(λx. λy. x) a b"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
  it "Test 4: nf of nested lambda (2)" $ do
    let term = fromString "(λx. (λy. y)) a b"
    printFoilTerm (nf emptyScope term) `shouldBe` "b"
  it "Test 5: nf with multiple applications" $ do
    let term = fromString "((λx. x) ((λy. y) z))"
    printFoilTerm (nf emptyScope term) `shouldBe` "z"
  --   it "Test 6: nf of self application" $ do
  --     -- gets stuck
  --     let term = fromString "(λx. x x) (λx. x x)"
  --     printFoilTerm (nf emptyScope term) `shouldSatisfy` (not . null)
  it "Test 7: nf of constant function" $ do
    let term = fromString "(λx. λy. x) a b"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
  it "Test 8: nf of function with unused argument" $ do
    let term = fromString "(λx. λy. x) a ((λz. z) b)"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
  it "Test 9: nf of chained applications" $ do
    let term = fromString "((λx. x) ((λx. x) ((λx. x) y)))"
    printFoilTerm (nf emptyScope term) `shouldBe` "y"
  it "Test 10: nf of complex term (example 1)" $ do
    let term = fromString "(λs. λz. s (s z)) (λs. λz. s z) a"
    printFoilTerm (nf emptyScope term) `shouldSatisfy` (not . null)
  it "Test 11: nf of complex term (example 2)" $ do
    let term = fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)"
    printFoilTerm (nf emptyScope term) `shouldBe` "λ x1 . λ x2 . x1"
  it "Test 12: nf with extra parentheses" $ do
    let term = fromString "(((λx. x)))"
    printFoilTerm (nf emptyScope term) `shouldBe` printFoilTerm (fromString "λx. x")
  it "Test 13: nf of a term with multiple lambdas" $ do
    let term = fromString "(λx. λy. λz. x) a b c"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
  --   it "Test 14: nf of non-terminating term (should remain neutral)" $ do
  --     -- gets stuck
  --     let term = fromString "(λx. x x) (λx. x x)"
  --     printFoilTerm (nf emptyScope term) `shouldSatisfy` (not . null)
  it "Test 15: nf of application with nested lambdas" $ do
    let term = fromString "((λx. λy. y) a) b"
    printFoilTerm (nf emptyScope term) `shouldBe` "b"
  it "Test 16: nf of application order" $ do
    let term = fromString "((λx. x) ((λy. y) a))"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
  it "Test 17: nf of term with repeated variables" $ do
    let term = fromString "(λx. x x) (λx. x)"
    printFoilTerm (nf emptyScope term) `shouldSatisfy` (not . null)
  it "Test 18: nf of term with no applications" $ do
    let term = fromString "λx. λy. x"
    printFoilTerm (nf emptyScope term) `shouldBe` printFoilTerm term
  it "Test 19: nf of deeply nested application" $ do
    let term = fromString "((((λx. x) a) b) c) d"
    printFoilTerm (nf emptyScope term) `shouldSatisfy` (not . null)
  it "Test 20: nf of term with redundant lambda" $ do
    let term = fromString "(λx. (λy. x)) a b"
    printFoilTerm (nf emptyScope term) `shouldBe` "a"
