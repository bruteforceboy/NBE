-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Parser.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pCommand
  , pListCommand
  , pTerm2
  , pTerm
  , pTerm1
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Parser.Syntax.Abs
import Parser.Syntax.Lex

}

%name pProgram_internal Program
%name pCommand_internal Command
%name pListCommand_internal ListCommand
%name pTerm2_internal Term2
%name pTerm_internal Term
%name pTerm1_internal Term1
%name pScopedTerm_internal ScopedTerm
%name pPattern_internal Pattern
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '('        { PT _ (TS _ 1)       }
  ')'        { PT _ (TS _ 2)       }
  ','        { PT _ (TS _ 3)       }
  '.'        { PT _ (TS _ 4)       }
  ':'        { PT _ (TS _ 5)       }
  ';'        { PT _ (TS _ 6)       }
  '_'        { PT _ (TS _ 7)       }
  'check'    { PT _ (TS _ 8)       }
  'compute'  { PT _ (TS _ 9)       }
  'λ'        { PT _ (TS _ 10)      }
  L_VarIdent { PT _ (T_VarIdent _) }

%%

VarIdent :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.VarIdent) }
VarIdent  : L_VarIdent { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.VarIdent (tokenText $1)) }

Program :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Program) }
Program
  : ListCommand { (fst $1, Parser.Syntax.Abs.AProgram (fst $1) (snd $1)) }

Command :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Command) }
Command
  : 'check' Term ':' Term { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.CommandCheck (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }
  | 'compute' Term ':' Term { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.CommandCompute (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }

ListCommand :: { (Parser.Syntax.Abs.BNFC'Position, [Parser.Syntax.Abs.Command]) }
ListCommand
  : {- empty -} { (Parser.Syntax.Abs.BNFC'NoPosition, []) }
  | Command ';' ListCommand { (fst $1, (:) (snd $1) (snd $3)) }

Term2 :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Term) }
Term2
  : VarIdent { (fst $1, Parser.Syntax.Abs.Var (fst $1) (snd $1)) }
  | '(' Term ')' { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), (snd $2)) }

Term :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Term) }
Term
  : 'λ' Pattern '.' ScopedTerm { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.Lam (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }
  | Term1 { (fst $1, (snd $1)) }

Term1 :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Term) }
Term1
  : Term1 Term2 { (fst $1, Parser.Syntax.Abs.App (fst $1) (snd $1) (snd $2)) }
  | Term2 { (fst $1, (snd $1)) }

ScopedTerm :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.ScopedTerm) }
ScopedTerm
  : Term { (fst $1, Parser.Syntax.Abs.AScopedTerm (fst $1) (snd $1)) }

Pattern :: { (Parser.Syntax.Abs.BNFC'Position, Parser.Syntax.Abs.Pattern) }
Pattern
  : '_' { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.PatternWildcard (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1))) }
  | VarIdent { (fst $1, Parser.Syntax.Abs.PatternVar (fst $1) (snd $1)) }
  | '(' Pattern ',' Pattern ')' { (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1), Parser.Syntax.Abs.PatternPair (uncurry Parser.Syntax.Abs.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $4)) }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Parser.Syntax.Abs.Program
pProgram = fmap snd . pProgram_internal

pCommand :: [Token] -> Err Parser.Syntax.Abs.Command
pCommand = fmap snd . pCommand_internal

pListCommand :: [Token] -> Err [Parser.Syntax.Abs.Command]
pListCommand = fmap snd . pListCommand_internal

pTerm2 :: [Token] -> Err Parser.Syntax.Abs.Term
pTerm2 = fmap snd . pTerm2_internal

pTerm :: [Token] -> Err Parser.Syntax.Abs.Term
pTerm = fmap snd . pTerm_internal

pTerm1 :: [Token] -> Err Parser.Syntax.Abs.Term
pTerm1 = fmap snd . pTerm1_internal

pScopedTerm :: [Token] -> Err Parser.Syntax.Abs.ScopedTerm
pScopedTerm = fmap snd . pScopedTerm_internal

pPattern :: [Token] -> Err Parser.Syntax.Abs.Pattern
pPattern = fmap snd . pPattern_internal
}

