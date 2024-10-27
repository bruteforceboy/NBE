{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}

module Untyped.Foil where

import Control.Monad (when)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.IntSet as Set
import Control.DeepSeq (NFData)

data {- kind -} S
  = {- type -} VoidS

newtype RawName = RawName Int
  deriving (Eq, Ord)

newtype RawScope = RawScope Set.IntSet
  deriving (Eq)

newtype Name (n :: S) = UnsafeName RawName
  deriving (Eq, Ord)

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving (Eq)

newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord)

rawEmptyScope :: RawScope
rawEmptyScope = RawScope Set.empty

rawFreshName :: RawScope -> RawName
rawFreshName (RawScope s)
  | Set.null s = RawName 0
  | otherwise = RawName (Set.findMax s + 1)

rawExtendScope :: RawName -> RawScope -> RawScope
rawExtendScope (RawName i) (RawScope s) = RawScope (Set.insert i s)

rawMember :: RawName -> RawScope -> Bool
rawMember (RawName i) (RawScope s) = Set.member i s

newtype RawSubst a = RawSubst (IntMap a)

rawIdSubst :: RawSubst a
rawIdSubst = RawSubst IM.empty

rawLookup :: RawSubst a -> RawName -> Maybe a
rawLookup (RawSubst env) (RawName i) = IM.lookup i env

rawExtendSubst :: RawName -> a -> RawSubst a -> RawSubst a
rawExtendSubst (RawName i) val (RawSubst env) = RawSubst (IM.insert i val env)

emptyScope :: Scope VoidS
emptyScope = UnsafeScope rawEmptyScope

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName rn)) (UnsafeScope s) =
  UnsafeScope (rawExtendScope rn s)

withFreshBinder :: Scope n -> (forall l. NameBinder n l -> r) -> r
withFreshBinder (UnsafeScope rs) cont =
  let binder = UnsafeNameBinder (UnsafeName (rawFreshName rs))
   in cont binder

data Expr n where
  VarE :: {-# UNPACK #-} !(Name n) -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: {-# UNPACK #-} !(NameBinder n l) -> Expr l -> Expr n
  ClosureE :: Substitution Expr n o -> {-# UNPACK #-} !(NameBinder n l) -> Expr l -> Expr o

newtype Substitution (e :: S -> *) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (e o))
  deriving newtype (NFData)

class HasVar (e :: S -> *) where
  makeVar :: Name n -> e n

instance HasVar Expr where
  makeVar = VarE

lookupSubst :: HasVar e => Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution env) (UnsafeName id) =
    case IntMap.lookup id env of
        Just ex -> ex
        Nothing -> makeVar (UnsafeName id)

identitySubst :: Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

singletonSubst :: NameBinder i i' -> e i -> Substitution e i' i
singletonSubst (UnsafeNameBinder (UnsafeName name)) expr
  = UnsafeSubstitution (IntMap.singleton name expr)

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution (IntMap.insert id ex env)

addRename :: HasVar e => Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
    | otherwise = addSubst s b (makeVar n)

class Distinct (n :: S)
instance Distinct VoidS

substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) (\binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body in LamE binder' body'
        )
    ClosureE{} -> error "not implemented"

newtype Env val n = Env [(Name n, val n)]

lookupVar :: Env val n -> Name n -> val n
lookupVar (Env ((name, val) : env')) x
  | name == x = val
  | otherwise = lookupVar (Env env') x
lookupVar (Env []) x = x

eval :: Substitution Expr i o -> Expr i -> Expr o
eval env = \case
  VarE x -> lookupSubst env x
  AppE f x ->
    case eval env f of
      ClosureE env' binder body -> do
        eval (addSubst env' binder (eval env x)) body
      f' -> AppE f' (eval env x)
  LamE binder body -> ClosureE env binder body
  ClosureE env binder body -> error "impossible"

quote :: Distinct n => Scope n -> Expr n -> Expr n
quote scope = \case
  e@VarE{} -> e
  AppE f x -> AppE (quote scope f) (quote scope x)
  LamE binder body -> unsafeAssertFresh binder $ \binder' ->
    LamE binder (quote (extendScope binder' scope) (unsafeCoerce body))
  ClosureE env binder body -> withRefreshed scope (nameOf binder) $ \binder' ->
    quote scope (LamE binder' (eval (addRename (sink env) binder (nameOf binder')) body) )

runProgram :: [(Name VoidS, Expr VoidS)] -> Expr VoidS -> Value VoidS
runProgram defs expr =
  let env = addDefs (Env []) defs
   in eval env expr

toChurch :: Integer -> Expr VoidS
toChurch 0 = VarE (UnsafeName (RawName 0))
toChurch n = AppE (VarE (UnsafeName (RawName 1))) (toChurch (n - 1))

churchDefs :: [(Name VoidS, Expr VoidS)]
churchDefs =
  [ (UnsafeName (RawName 0), LamE (UnsafeNameBinder (UnsafeName (RawName 2))) (LamE (UnsafeNameBinder (UnsafeName (RawName 3))) (VarE (UnsafeName (RawName 3))))),
    (UnsafeName (RawName 1), LamE (UnsafeNameBinder (UnsafeName (RawName 4))) (LamE (UnsafeNameBinder (UnsafeName (RawName 5))) (LamE (UnsafeNameBinder (UnsafeName (RawName 6))) (AppE (VarE (UnsafeName (RawName 5))) (AppE (AppE (VarE (UnsafeName (RawName 4))) (VarE (UnsafeName (RawName 5)))) (VarE (UnsafeName (RawName 6)))))))),
    (UnsafeName (RawName 7), LamE (UnsafeNameBinder (UnsafeName (RawName 8))) (LamE (UnsafeNameBinder (UnsafeName (RawName 9))) (LamE (UnsafeNameBinder (UnsafeName (RawName 10))) (AppE (AppE (VarE (UnsafeName (RawName 8))) (VarE (UnsafeName (RawName 10)))) (AppE (AppE (VarE (UnsafeName (RawName 9))) (VarE (UnsafeName (RawName 10)))) (VarE (UnsafeName (RawName 10))))))))
  ]

testSubstitution :: Value VoidS
testSubstitution =
  let subst = addSubst (identitySubst VarE) (UnsafeNameBinder (UnsafeName (RawName 0))) (VarE (UnsafeName (RawName 1)))
      expr = LamE (UnsafeNameBinder (UnsafeName (RawName 0))) (VarE (UnsafeName (RawName 0)))
      resultExpr = substitute emptyScope subst expr
   in eval (Env []) resultExpr

testFoil :: Value VoidS
testFoil = runProgram churchDefs (AppE (AppE (VarE (UnsafeName (RawName 7))) (toChurch 2)) (toChurch 3))