{-# LANGUAGE OverloadedStrings #-}

module BNFC_Spec (spec) where

import Control.Monad.Foil
import qualified Data.Map as Map
import Language.Lambda.Impl.FoilTH
import qualified Language.Lambda.Syntax.Abs as Raw
import qualified Language.Lambda.Syntax.Lex as Raw
import qualified Language.Lambda.Syntax.Par as Raw
import qualified Language.Lambda.Syntax.Print as Print
import Test.Hspec

spec :: Spec
spec = describe "BNFC conversion tests" $ do
  let rawTerms =
        [ "(λx. x) y",
          "λx. x",
          "((λx. x) y)",
          "(λx. λy. x) a b",
          "(λx. (λy. y)) a b",
          "((λx. x) ((λy. y) z))",
          "((λx. x) ((λx. x) y))",
          "(λx. x x) (λx. x x)",
          "λx. λy. λz. x",
          "((λs. s (λx. x)) (λy. y))",
          "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)",
          "λx. (λy. x) y",
          "((λx. x) a) b",
          "(λx. x) ((λx. x) ((λx. x) y))",
          "λx. λy. x y",
          "λx. (λy. (λz. x))",
          "((λx. x x) (λx. x x))",
          "λx. x x",
          "((λx. x) a) ((λy. y) b)",
          "λx. (λy. (λz. z))"
        ]
  sequence_
    [ it ("Raw round-trip test " ++ show n) $ do
        let rawTerm = case Raw.pTerm (Raw.tokens t) of
              Left err -> error $ "Parsing failed: " ++ err
              Right term -> term
            foilTerm = toFoilTerm' emptyScope Map.empty rawTerm
            backRaw = fromFoilTermClosed [] foilTerm
        Print.printTree backRaw `shouldBe` Print.printTree rawTerm
      | (n, t) <- zip [1 .. 20] rawTerms
    ]
