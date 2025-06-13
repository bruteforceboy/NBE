{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Control.DeepSeq (NFData, deepseq)
import qualified Control.Monad.Foil as Foil
import Control.Monad.Foil.Internal
  ( InjectName (injectName),
    Name,
    Sinkable (sinkabilityProof),
    Substitution (UnsafeSubstitution),
    UnifiableInPattern (unifyInPattern),
  )
import Control.Monad.Foil.TH
import Control.Monad.Free.Foil
  ( AST (..),
    ScopedAST (..),
    convertFromAST,
    convertToAST,
    substitute,
  )
import Control.Monad.Free.Foil.TH
import qualified Criterion.Main as C
import Data.Bifunctor
import Data.Bifunctor.TH
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString (..))
import Data.ZipMatchK
import qualified GHC.Generics as GHC
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

-- | Generic annotated scope-safe \(\lambda\Nbe\)-terms with patterns.
type Term' a = AST (FoilPattern' a) (Term'Sig a)

data Closure pat sig n where
  VarC ::
    Foil.Name n -> Closure pat sig n
  Closure ::
    (Foil.Distinct n) =>
    Foil.Substitution (Closure pat sig) n o -> -- Environment of captured variables.
    sig (ScopedAST pat sig n) (Closure pat sig n) ->
    Closure pat sig o

type Value' a = Closure (FoilPattern' a) (Term'Sig a)

noLocation :: Raw.BNFC'Position
noLocation = error "no location"

-- | Compose two substitutions under a given scope to produce a combined substitution.
composeSubst ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Foil.Substitution (Closure pat sig) k n ->
  Foil.Substitution (Closure pat sig) k o
composeSubst
  scope
  env@(UnsafeSubstitution outerMap)
  env'@(UnsafeSubstitution innerMap) =
    UnsafeSubstitution $
      IntMap.union
        (IntMap.map (substituteClosure scope env) innerMap)
        outerMap

-- | Perform substitution inside a closure using the given environment and scope.
substituteClosure ::
  (Foil.Distinct o, Foil.CoSinkable pat) =>
  Foil.Scope o ->
  Foil.Substitution (Closure pat sig) n o ->
  Closure pat sig n ->
  Closure pat sig o
substituteClosure scope env (VarC x) =
  Foil.lookupSubst env x
substituteClosure scope env (Closure env' sig) =
  Closure (composeSubst scope env env') sig

-- | Quote a closure back into an AST node, using the provided evaluation function.
quote' ::
  (Foil.Distinct n, Bifunctor sig, HasNameBinder pat, Foil.CoSinkable pat) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
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
      bimap
        (quoteScoped eval scope env patternToNameBinder)
        (quote' eval scope . substituteClosure scope env)
        node

-- | Convert a scoped AST under substitution back to a scoped AST in a new scope.
quoteScoped ::
  ( Foil.Distinct n,
    Foil.Distinct o,
    Bifunctor sig,
    Foil.CoSinkable pat,
    HasNameBinder pat
  ) =>
  ( forall l m.
    (Foil.Distinct m, Foil.Distinct l) =>
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
    case Foil.assertDistinct pat' of
      (Foil.Distinct) ->
        case Foil.assertDistinct pat of
          (Foil.Distinct) ->
            let binder = patternToNameBinder pat
                scope' = Foil.extendScopePattern pat' scope
                env' = Foil.addRename (Foil.sink env) binder (Foil.nameOf (patternToNameBinder pat'))
             in ScopedAST pat' (quote' eval scope' (eval scope' env' body))

class HasNameBinder pat where
  patternToNameBinder :: pat n l -> Foil.NameBinder n l

instance HasNameBinder (FoilPattern' a) where
  patternToNameBinder (FoilPatternVar _ binder) = binder
  patternToNameBinder _ = error "Unsupported pattern in patternToNameBinder"

instance Foil.InjectName (Closure pat sig) where
  injectName = VarC

instance Foil.Sinkable (Closure pat sig) where
  sinkabilityProof :: (Name n -> Name l) -> Closure pat sig n -> Closure pat sig l
  sinkabilityProof rename (VarC n) =
    VarC (rename n)
  sinkabilityProof rename (Closure env sig) =
    Closure (Foil.sinkabilityProof rename env) sig

-- | Evaluate a term into a closure value under the given scope and environment.
eval :: (Foil.Distinct o, Foil.Distinct i) => Foil.Scope o -> Foil.Substitution (Value' a) i o -> Term' a i -> Value' a o
eval scope env = \case
  Var x -> Foil.lookupSubst env x
  App _ f x ->
    case eval scope env f of
      Closure env' (LamSig _ (ScopedAST (FoilPatternVar _ binder) body)) ->
        case Foil.assertDistinct binder of
          (Foil.Distinct) ->
            let arg = eval scope env x
                env'' = Foil.addSubst env' binder arg
             in eval scope env'' body
      _ -> error "unhandled"
  Lam loc (FoilPatternVar _ binder) body ->
    Closure env (LamSig loc (ScopedAST (FoilPatternVar loc binder) body))
  Pair loc t1 t2 ->
    let v1 = eval scope env t1
        v2 = eval scope env t2
     in Closure Foil.identitySubst (PairSig loc v1 v2)
  First _ p ->
    case eval scope env p of
      Closure env' (PairSig _ v1 _) ->
        substituteClosure scope env' v1
      _ -> error "unhandled"
  Second _ p ->
    case eval scope env p of
      Closure env' (PairSig _ _ v2) ->
        substituteClosure scope env' v2
      _ -> error "unhandled"
  Let _loc boundExpr (FoilPatternVar _ binder) body ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let val = eval scope env boundExpr
            env' = Foil.addSubst env binder val
         in eval scope env' body

-- | Scope-safe \(\lambda\Nbe\)-terms annotated with source code position.
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
-- >>> fromString "λx.λy.λx.x" :: Term Foil.VoidS
-- λ x0 . λ x1 . λ x2 . x2
instance IsString (AST FoilPattern (Term'Sig Raw.BNFC'Position) Foil.VoidS) where
  fromString input = case Raw.pTerm (Raw.tokens input) of
    Left err -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
    Right term -> toTerm'Closed term

-- | Pretty-print scope-safe terms as raw syntax.
instance Show (AST (FoilPattern' a) (Term'Sig a) Foil.VoidS) where
  show = Raw.printTree . fromTerm'

-- | Match a pattern against a term, producing a substitution mapping pattern variables.
matchPattern :: FoilPattern n l -> Term n -> Foil.Substitution Term l n
matchPattern pat term = go pat term Foil.identitySubst
  where
    go :: FoilPattern i l -> Term n -> Foil.Substitution Term i n -> Foil.Substitution Term l n
    go (FoilPatternVar _loc x) e = \subst -> Foil.addSubst subst x e

-- | Compute the weak head normal form of a term under the given scope.
whnf :: (Foil.Distinct n) => Foil.Scope n -> Term n -> Term n
whnf scope = \case
  App loc f x ->
    case whnf scope f of
      Lam _loc binder body ->
        let subst = matchPattern binder x
         in whnf scope (substitute scope subst body)
      f' -> App loc f' x
  t -> t

-- | Normal form
-- >>> Free.nf emptyScope (fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)")
-- λ x0 . λ x1 . x0
-- >>> Free.nf emptyScope (fromString "let x = (λx. (x,(x,x))) in (x x)")
-- (λ x0 . (x0, (x0, x0)), (λ x0 . (x0, (x0, x0)), λ x0 . (x0, (x0, x0))))
-- >>> Free.nf emptyScope (fromString "(λx. (x,(x,x)))")
-- λ x0 . (x0, (x0, x0))
nf :: (Foil.Distinct n) => Foil.Scope n -> Term n -> Term n
nf scope term = quote' eval scope (eval scope Foil.identitySubst term)

benchTerm ::
  forall n.
  (Foil.Distinct n) =>
  Foil.Scope n ->
  String ->
  Term n ->
  C.Benchmark
benchTerm scope name term =
  C.bench name $ C.whnf (nf scope) term