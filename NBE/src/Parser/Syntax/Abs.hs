-- File generated by the BNF Converter (bnfc 2.9.5).

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language Syntax.

module Parser.Syntax.Abs where

import Prelude (String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

import qualified Data.Data    as C (Data, Typeable)
import qualified GHC.Generics as C (Generic)

type Program = Program' BNFC'Position
data Program' a = AProgram a [Command' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable, C.Data, C.Typeable, C.Generic)

type Command = Command' BNFC'Position
data Command' a
    = CommandCheck a (Term' a) (Term' a)
    | CommandCompute a (Term' a) (Term' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable, C.Data, C.Typeable, C.Generic)

type Term = Term' BNFC'Position
data Term' a
    = Var a VarIdent
    | Lam a (Pattern' a) (ScopedTerm' a)
    | App a (Term' a) (Term' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable, C.Data, C.Typeable, C.Generic)

type ScopedTerm = ScopedTerm' BNFC'Position
data ScopedTerm' a = AScopedTerm a (Term' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable, C.Data, C.Typeable, C.Generic)

type Pattern = Pattern' BNFC'Position
data Pattern' a
    = PatternWildcard a
    | PatternVar a VarIdent
    | PatternPair a (Pattern' a) (Pattern' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable, C.Data, C.Typeable, C.Generic)

newtype VarIdent = VarIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Data, C.Typeable, C.Generic, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    AProgram p _ -> p

instance HasPosition Command where
  hasPosition = \case
    CommandCheck p _ _ -> p
    CommandCompute p _ _ -> p

instance HasPosition Term where
  hasPosition = \case
    Var p _ -> p
    Lam p _ _ -> p
    App p _ _ -> p

instance HasPosition ScopedTerm where
  hasPosition = \case
    AScopedTerm p _ -> p

instance HasPosition Pattern where
  hasPosition = \case
    PatternWildcard p -> p
    PatternVar p _ -> p
    PatternPair p _ _ -> p

