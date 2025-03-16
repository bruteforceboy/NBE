{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Lambda.Impl.FreeFoilTH where

import qualified Control.Monad.Foil as Foil
import Control.Monad.Foil.Internal
import Control.Monad.Foil.TH
import Control.Monad.Free.Foil
  ( AST (..),
    ScopedAST (..),
    convertFromAST,
    convertToAST,
    substitute,
  )
import Control.Monad.Free.Foil.TH
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString (..))
import Data.ZipMatchK
import qualified GHC.Generics as GHC
import qualified GHC.Stack as Foil
import Generics.Kind.TH (deriveGenericK)
import qualified Language.Lambda.Syntax.Abs as Raw
import qualified Language.Lambda.Syntax.Lex as Raw
import qualified Language.Lambda.Syntax.Par as Raw
import qualified Language.Lambda.Syntax.Print as Raw

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

-- ** Signature

mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
deriveBifunctor ''Term'Sig
deriveBifoldable ''Term'Sig
deriveBitraversable ''Term'Sig

-- ** Pattern synonyms

mkPatternSynonyms ''Term'Sig

-- ** Conversion helpers

mkConvertToFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
mkConvertFromFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- ** Foil.Scope-safe patterns

mkFoilPattern ''Raw.VarIdent ''Raw.Pattern'
deriveGenericK ''FoilPattern'

instance Foil.SinkableK (FoilPattern' a)

instance Foil.HasNameBinders (FoilPattern' a)

instance Foil.CoSinkable (FoilPattern' a)

mkToFoilPattern ''Raw.VarIdent ''Raw.Pattern'
mkFromFoilPattern ''Raw.VarIdent ''Raw.Pattern'

instance Foil.UnifiablePattern (FoilPattern' a)

-- | Ignoring location information when unifying patterns.
instance Foil.UnifiableInPattern Raw.BNFC'Position where
  unifyInPattern _ _ = True

-- | Deriving 'GHC.Generic' and 'GenericK' instances.
deriving instance GHC.Generic (Term'Sig a scope term)

deriveGenericK ''Term'Sig

-- -- | Match 'Raw.Ident' via 'Eq'.
-- instance ZipMatchK Raw.Ident where zipMatchWithK = zipMatchViaEq

-- | Ignore 'Raw.BNFC'Position' when matching terms.
instance ZipMatchK Raw.BNFC'Position where zipMatchWithK = zipMatchViaChooseLeft

-- | Generic 'ZipMatchK' instance.
instance (ZipMatchK a) => ZipMatchK (Term'Sig a)

-- | Generic annotated scope-safe \(\lambda\Pi\)-terms with patterns.
type Term' a = AST (FoilPattern' a) (Term'Sig a)

-- data Neutral n where
--   NVar :: Foil.Name n -> Neutral n
--   NApp :: Neutral n -> Value' n -> Neutral n

-- data Value n where
--   VClosure :: Foil.Substitution Value i o -> Foil.NameBinder i l -> Term' a l -> Value o
--   VNeutral :: Neutral n -> Value n

data Closure pat sig n where
  VarC ::
    Foil.Name n -> Closure pat sig n
  Closure ::
    (Foil.Distinct n) =>
    Foil.Substitution (Closure pat sig) n o -> -- Environment (values of captured variables).
    sig (ScopedAST pat sig n) (Closure pat sig n) ->
    Closure pat sig o

type Value' a = Closure (FoilPattern' a) (Term'Sig a)

noLocation :: Raw.BNFC'Position
noLocation = error "no location"

-- class QuoteSig pat sig where
--   quoteSig
--     :: (Foil.Distinct o)
--     => Foil.Scope o
--     -> Foil.Substitution (Closure pat sig) n o
--     -> sig (ScopedAST pat sig n) (Closure pat sig n)
--     -> sig (ScopedAST pat sig o) (AST pat sig o)

-- instance QuoteSig (FoilPattern' a) (Term'Sig a) where
--   quoteSig scope env = \case
--     LamSig annotation (ScopedAST (FoilPatternVar _ binder) body) ->
--       Foil.withRefreshed scope (Foil.nameOf binder) $ \binder' ->
--           let scope' = Foil.extendScope binder' scope
--               env' = Foil.addRename (Foil.sink env) binder (Foil.nameOf binder')
--            in LamSig annotation $ ScopedAST (FoilPatternVar annotation binder') $
--                 (quote' scope' (eval scope' env' body))
--     _ -> error "Unsupported signature in Closure"

-- class EvalSig pat sig where
--   evalSig
--     :: Foil.Scope o
--     -> sig (ScopedAST pat sig o) (AST pat sig o)
--     -> sig (ScopedAST pat sig n) (Closure pat sig n)

-- instance EvalSig (FoilPattern' a) (Term'Sig a) where
--   evalSig scope = \case
--     AppSig t1 t2 ->
--       case eval t1 of -- ???
--         _ -> _

-- TODO:
-- 1. Complete the generic quote' (keep eval' as a parameter, use eval in tests).
-- 2. Ensure that it works for untype lambda calculus.
-- 3. Extend untyped lambda calculus with pairs ({t1, t2}) and projections (first, second).
-- 4. Extend untyped lambda calculus with let-binding (let x = t1 in t2)
-- 5. Add doctests (examples) for eval/quote/etc.
-- 6. Set up hspec with hspec-discover to write more tests separately.
-- 7. Use QuickCheck to be able to generate random terms and perform property-testing with them (which properties are we interested in?).
-- 8. Use Criterion to set up a benchmark suite OR fork lambda-n-ways and use your package with it.

-- MIGHT BE OUT OF REACH:
-- 1. Generalized eval
-- 2. Typed NbE
-- 3a. Extend untyped lambda calculus with booleans (false, true) and if-expression (if t1 then t2 else t3).
--      - untyped NBE is not easy (I think):
--            if x then y else y  ->  y ??
--
--            if x then (if y then true else false) else (if y then false else true)
--             ==
--            if y then (if x then true else false) else (if x then false else true)
--             ==
--            case {x, y} of
--                {true, true} -> true
--              | {true, false} -> false
--              | {false, true} -> false
--              | {false, false} -> true
--
-- 3b. Extend untyped lambda calculus with sums (inl(t1), inr(t2)) and pattern-matching (case t1 of inl(x) -> t2 | inr(y) -> t3).
--      - untyped NBE is not easy (I think):
--
substituteClosure ::
  (Foil.Distinct o, Foil.CoSinkable pat, ExtEndo o) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Closure pat sig n ->
  Closure pat sig o
substituteClosure scope env = \case
  VarC x -> Foil.lookupSubst env x
  Closure env' sig ->
    Closure (Foil.sink env') sig

quote' ::
  (Foil.Distinct n, Bifunctor sig, ExtEndo n, HasNameBinder pat, Foil.CoSinkable pat) =>
  ( forall l m.
    (Foil.Distinct m) =>
    Foil.Scope m ->
    Foil.Substitution (Closure pat sig) l m ->
    AST pat sig l ->
    Closure pat sig m
  ) ->
  Foil.Scope n ->
  Closure pat sig n ->
  AST pat sig n
quote' eval scope = \case
  VarC x -> Var x
  Closure (env :: Foil.Substitution (Closure pat sig) i n) node ->
    Node $
      -- node                   :: sig (ScopedAST pat sig i) (Closure pat sig i)
      -- substituteClosure scope env
      --                        :: Closure pat sig i -> Closure pat sig n
      -- quote' scope           :: Closure pat sig n -> AST pat sig n
      -- bimap ... ... node     :: sig (ScopedAST pat sig n) (AST pat sig n)
      bimap
        (quoteScoped eval scope env patternToNameBinder)
        (quote' eval scope . substituteClosure scope env)
        node

class HasNameBinder pat where
  patternToNameBinder :: pat n l -> Foil.NameBinder n l

instance HasNameBinder (FoilPattern' a) where
  patternToNameBinder (FoilPatternVar _ binder) = binder
  patternToNameBinder _ = error "Unsupported pattern in patternToNameBinder"

-- Foil.Scope o -> Foil.Substitution (Value' a) i o -> Term' a i -> Value' a o

quoteScoped ::
  ( Foil.Distinct n,
    Foil.Distinct o,
    Bifunctor sig,
    Foil.CoSinkable pat,
    ExtEndo o,
    HasNameBinder pat
  ) =>
  ( forall l m.
    (Foil.Distinct m) =>
    Foil.Scope m ->
    Foil.Substitution (Closure pat sig) l m ->
    AST pat sig l ->
    Closure pat sig m
  ) ->
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  (forall m l. pat m l -> Foil.NameBinder m l) ->
  ScopedAST pat sig n ->
  ScopedAST pat sig o
quoteScoped eval scope env patternToNameBinder (ScopedAST pat body) =
  Foil.withRefreshedPattern scope pat $ \(_ :: Foil.Substitution (Closure pat sig) n o -> Foil.Substitution (Closure pat sig) l o') pat' ->
    let binder = patternToNameBinder pat
        scope' = Foil.extendScopePattern pat' scope
        env' = Foil.addRename (Foil.sink env) binder (Foil.nameOf (patternToNameBinder pat'))
     in ScopedAST pat' (quote' eval scope' (eval scope' env' body))

-- quote :: (Foil.Distinct n) => Foil.Scope n -> Value' a n -> Term' a n
-- quote scope = \case
--   VarC x ->
--     Var x
--   Closure env sig ->
--     case sig of
--       LamSig annotation (ScopedAST (FoilPatternVar _ binder) body) ->
--         Foil.withRefreshed scope (Foil.nameOf binder) $ \binder' ->
--           let scope' = Foil.extendScope binder' scope
--               env' = Foil.addRename (Foil.sink env) binder (Foil.nameOf binder')
--            in Lam annotation (FoilPatternVar annotation binder') $
--                 (quote scope' (eval scope' env' body))
--       _ -> error "Unsupported signature in Closure"

instance Foil.InjectName (Closure pat sig) where
  injectName = VarC

instance Foil.Sinkable (Closure pat sig) where
  sinkabilityProof :: (Name n -> Name l) -> Closure pat sig n -> Closure pat sig l
  sinkabilityProof rename (VarC n) =
    VarC (rename n)
  sinkabilityProof rename (Closure env sig) =
    Closure (Foil.sinkabilityProof rename env) sig

eval :: (Foil.Distinct o, Foil.Distinct i) => Foil.Scope o -> Foil.Substitution (Value' a) i o -> Term' a i -> Value' a o
eval scope env = \case
  Var x -> Foil.lookupSubst env x
  App loc f x ->
    case eval scope env f of
      Closure env' (LamSig _ (ScopedAST (FoilPatternVar _ binder) body)) ->
        let arg = eval scope env x
            env'' = Foil.addSubst env' binder arg
         in eval scope env'' body
  Lam loc (FoilPatternVar _ binder) body ->
    Closure env (LamSig loc (ScopedAST (FoilPatternVar loc binder) body))

-- | Scope-safe \(\lambda\Pi\)-terms annotated with source code position.
type Term = Term' Raw.BNFC'Position

-- | Foil.Scope-safe patterns annotated with source code position.
type FoilPattern = FoilPattern' Raw.BNFC'Position

-- | Convert 'Raw.Term'' into a scope-safe term.
-- This is a special case of 'convertToAST'.
toTerm' :: (Foil.Distinct n) => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> Term' a n
toTerm' = convertToAST convertToTerm'Sig toFoilPattern' getTerm'FromScopedTerm'

-- | Convert 'Raw.Term'' into a closed scope-safe term.
-- This is a special case of 'toTerm''.
toTerm'Closed :: Raw.Term' a -> Term' a Foil.VoidS
toTerm'Closed = toTerm' Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'Raw.Term''.
-- This is a special case of 'convertFromAST'.
--
-- 'Raw.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromTerm' :: Term' a n -> Raw.Term' a
fromTerm' =
  convertFromAST
    convertFromTerm'Sig
    (Raw.Var (error "location missing"))
    (fromFoilPattern' mkVarIdent)
    (Raw.AScopedTerm (error "location missing"))
    mkVarIdent
  where
    mkVarIdent n = Raw.VarIdent ("x" ++ show n)

-- | Parse scope-safe terms via raw representation.
--
-- >>> fromString "λx.λy.λx.x" :: Term Foil.VoidS
-- λ x0 . λ x1 . λ x2 . x2
instance IsString (AST FoilPattern (Term'Sig Raw.BNFC'Position) Foil.VoidS) where
  fromString input = case Raw.pTerm (Raw.tokens input) of
    Left err -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
    Right term -> toTerm'Closed term

-- | Pretty-print scope-safe terms via raw representation.
instance Show (AST (FoilPattern' a) (Term'Sig a) Foil.VoidS) where
  show = Raw.printTree . fromTerm'

-- ** Evaluation

-- | Match a pattern against an term.
matchPattern :: FoilPattern n l -> Term n -> Foil.Substitution Term l n
matchPattern pat term = go pat term Foil.identitySubst
  where
    go :: FoilPattern i l -> Term n -> Foil.Substitution Term i n -> Foil.Substitution Term l n
    go (FoilPatternVar _loc x) e = \subst -> Foil.addSubst subst x e

whnf :: (Foil.Distinct n) => Foil.Scope n -> Term n -> Term n
whnf scope = \case
  App loc f x ->
    case whnf scope f of
      Lam _loc binder body ->
        let subst = matchPattern binder x
         in whnf scope (substitute scope subst body)
      f' -> App loc f' x
  t -> t

-- "λx. x"

-- | Normal form.
--
-- >>> Free.nf emptyScope (fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)")
-- λ x1 . λ x2 . x1
-- nf :: (Foil.Distinct n) => Foil.Scope n -> Term n -> Term n
-- nf scope term = quote scope (eval scope Foil.identitySubst term)