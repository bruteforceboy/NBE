{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Untyped.Foil where

import Control.DeepSeq
import Data.IntMap
import Data.IntMap qualified as IntMap
import Data.IntSet
import Data.IntSet qualified as IntSet
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe qualified
import GHC.Generics (Generic)
import System.Exit (exitFailure)
import Unsafe.Coerce (unsafeCoerce)

type Id = Int

type RawName = Id

type RawScope = IntSet

data {- kind -} S
  = {- type -} VoidS

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype (NFData)

newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord)

newtype NameBinder (n :: S) (l :: S)
  = UnsafeNameBinder (Name l)
  deriving newtype (NFData, Eq, Ord)

emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName id)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert id scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope
  | IntSet.null scope = 0
  | otherwise = IntSet.findMax scope + 1

withFreshBinder ::
  Scope n ->
  (forall l. NameBinder n l -> r) ->
  r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember = IntSet.member

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: {-# UNPACK #-} !(Name n) -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: {-# UNPACK #-} !(NameBinder n l) -> Expr l -> Expr n

data Neutral n where
  NVar :: {-# UNPACK #-} !(Name n) -> Neutral n
  NApp :: Neutral n -> Value n -> Neutral n

data Value n where
  VClosure :: Substitution Value i o -> {-# UNPACK #-} !(NameBinder i l) -> Expr l -> Value o
  VNeutral :: Neutral n -> Value n

instance NFData (Expr l) where
  rnf (LamE binder body) = rnf binder `seq` rnf body
  rnf (AppE fun arg) = rnf fun `seq` rnf arg
  rnf (VarE name) = rnf name

instance NFData (Neutral n) where
  rnf (NVar name) = rnf name
  rnf (NApp neu val) = rnf neu `seq` rnf val

instance NFData (Value n) where
  rnf (VClosure env binder body) = rnf env `seq` rnf binder `seq` rnf body
  rnf (VNeutral neu) = rnf neu

-- Distinct constraints
class ExtEndo (n :: S)

class ((ExtEndo n) => ExtEndo l) => Ext (n :: S) (l :: S)

instance ((ExtEndo n) => ExtEndo l) => Ext n l

class Distinct (n :: S)

instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
data DistinctEvidence (n :: S) where
  Distinct :: (Distinct n) => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence (n :: S) (l :: S) where
  Ext :: (Ext n l) => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withFresh ::
  (Distinct n) =>
  Scope n ->
  (forall l. (DExt n l) => NameBinder n l -> r) ->
  r
withFresh scope cont =
  withFreshBinder
    scope
    ( \binder ->
        unsafeAssertFresh binder cont
    )

unsafeAssertFresh ::
  forall n l n' l' r.
  NameBinder n l ->
  ((DExt n' l') => NameBinder n' l' -> r) ->
  r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed ::
  (Distinct o) =>
  Scope o ->
  Name i ->
  (forall o'. (DExt o o') => NameBinder o o' -> r) ->
  r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName id) cont
  | IntSet.member id rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

class Sinkable (e :: S -> *) where
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder \rename' binder' ->
    LamE binder' (sinkabilityProof rename' body)

instance Sinkable Neutral where
  sinkabilityProof rename (NVar v) = NVar (rename v)
  sinkabilityProof rename (NApp neu val) =
    NApp (sinkabilityProof rename neu) (sinkabilityProof rename val)

instance Sinkable Value where
  sinkabilityProof rename (VClosure env binder body) =
    VClosure (sinkabilityProof rename env) binder body
  sinkabilityProof rename (VNeutral neu) =
    VNeutral (sinkabilityProof rename neu)

extendRenaming ::
  (Name n -> Name n') ->
  NameBinder n l ->
  (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r) ->
  r
extendRenaming _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

-- Substitution
newtype Substitution (e :: S -> *) (i :: S) (o :: S)
  = UnsafeSubstitution (IntMap (e o))
  deriving newtype (NFData)

class HasVar (e :: S -> *) where
  makeVar :: Name n -> e n

instance HasVar Expr where
  makeVar = VarE

instance HasVar Value where
  makeVar = VNeutral . NVar

lookupSubst :: (HasVar e) => Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution env) (UnsafeName id) =
  case IntMap.lookup id env of
    Just ex -> ex
    Nothing -> makeVar (UnsafeName id)

identitySubst :: Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

singletonSubst :: NameBinder i i' -> e i -> Substitution e i' i
singletonSubst (UnsafeNameBinder (UnsafeName name)) expr =
  UnsafeSubstitution (IntMap.singleton name expr)

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution (IntMap.insert id ex env)

addRename :: (HasVar e) => Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
  | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
  | otherwise = addSubst s b (makeVar n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution env) =
    UnsafeSubstitution (fmap (sinkabilityProof rename) env)

-- Substitute part
substitute :: (Distinct o) => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
  VarE name -> lookupSubst subst name
  AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
  LamE binder body ->
    withRefreshed
      scope
      (nameOf binder)
      ( \binder' ->
          let subst' = addRename (sink subst) binder (nameOf binder')
              scope' = extendScope binder' scope
              body' = substitute scope' subst' body
           in LamE binder' body'
      )

instantiate' :: (Distinct o) => Scope o -> (NameBinder o i, Expr o) -> Expr i -> Expr o
instantiate' scope (binder, expr) =
  substitute scope $
    singletonSubst binder expr

instantiate :: (Distinct o) => Scope o -> (NameBinder o i, Expr o) -> Expr i -> Expr o
instantiate scope (binder, expr) = go
  where
    -- go :: Expr i' -> Expr o
    go = \case
      e@(VarE name)
        | name == nameOf binder -> expr
        | otherwise -> unsafeCoerce e
      AppE f x -> AppE (go f) (go x)
      LamE binder body -> withRefreshed scope (nameOf binder) $ \binder' ->
        let scope' = extendScope binder' scope
         in LamE binder' $
              instantiate scope' (unsafeCoerce binder, sink expr) body

whnf :: (Distinct n) => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        whnf scope $
          instantiate' scope (binder, arg) body
      fun' -> AppE fun' arg
  t -> t

nf :: (Distinct n) => Scope n -> Expr n -> Expr n
nf scope expr = case expr of
  LamE binder body -> unsafeAssertFresh binder \binder' ->
    let scope' = extendScope binder' scope
     in LamE binder' (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        nf scope $
          instantiate' scope (binder, arg) body
      fun' -> AppE (nf scope fun') (nf scope arg)
  t -> t

nfd :: Expr VoidS -> Expr VoidS
nfd = nf emptyScope

whnfd :: Expr VoidS -> Expr VoidS
whnfd = whnf emptyScope

eval :: (Distinct o) => Scope o -> Substitution Value i o -> Expr i -> Value o
eval scope env = \case
  VarE x -> lookupSubst env x
  AppE f x ->
    case eval scope env f of
      VClosure env' binder body ->
        let arg = eval scope env x
            env'' = addSubst env' binder arg
         in eval scope env'' body
      VNeutral neu ->
        VNeutral (NApp neu (eval scope env x))
  LamE binder body ->
    VClosure env binder body

quote :: (Distinct n) => Scope n -> Value n -> Expr n
quote scope = \case
  VClosure env binder body ->
    withRefreshed scope (nameOf binder) $ \binder' ->
      let scope' = extendScope binder' scope
       in LamE binder' $
            quote
              (extendScope binder' scope)
              (eval scope' (addRename (sink env) binder (nameOf binder')) body)
  VNeutral neu -> quoteNeutral scope neu

quoteNeutral :: (Distinct n) => Scope n -> Neutral n -> Expr n
quoteNeutral _ (NVar x) = VarE x
quoteNeutral scope (NApp neu val) =
  AppE (quoteNeutral scope neu) (quote scope val)

unsafeEquals :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeEquals (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 == name2

unsafeLess :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeLess (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 < name2

-- Unsafe renaming of a raw name
unsafeRenameVar :: IntMap RawName -> RawName -> RawName
unsafeRenameVar subst name1 = case IntMap.lookup name1 subst of
  Just name2 -> name2
  Nothing -> name1

unsafeAeq ::
  IntMap RawName ->
  IntMap RawName ->
  IntSet ->
  IntSet ->
  Expr n ->
  Expr l ->
  Bool
unsafeAeq subst1 subst2 target1 target2 (VarE (UnsafeName x)) (VarE (UnsafeName y))
  | IntSet.member x target1 = False
  | IntSet.member y target2 = False
  | otherwise = (unsafeRenameVar subst1 x) == (unsafeRenameVar subst2 y)
unsafeAeq subst1 subst2 target1 target2 (AppE fun1 arg1) (AppE fun2 arg2) =
  and
    [ unsafeAeq subst1 subst2 target1 target2 fun1 fun2,
      unsafeAeq subst1 subst2 target1 target2 arg1 arg2
    ]
unsafeAeq
  subst1
  subst2
  target1
  target2
  (LamE binder1@(UnsafeNameBinder (UnsafeName name1)) body1)
  (LamE binder2@(UnsafeNameBinder (UnsafeName name2)) body2)
    | unsafeEquals binder1 binder2 = unsafeAeq subst1 subst2 target1 target2 body1 body2
    | unsafeLess binder1 binder2 =
        let subst2' = IntMap.insert name2 name1 subst2
            target2' = IntSet.insert name1 target2
         in unsafeAeq subst1 subst2' target1 target2' body1 body2
    | otherwise =
        let (UnsafeName name1) = nameOf binder1
            subst1' = IntMap.insert name1 name2 subst1
            target1' = IntSet.insert name2 target1
         in unsafeAeq subst1' subst2 target1' target2 body1 body2
unsafeAeq _ _ _ _ _ _ = False