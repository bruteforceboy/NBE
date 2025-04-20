{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Lambda.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pTerm2
  , pTerm
  , pTerm1
  , pListTerm
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.Lambda.Syntax.Abs
import Language.Lambda.Syntax.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn10 ((Language.Lambda.Syntax.Abs.BNFC'Position, Language.Lambda.Syntax.Abs.VarIdent))
	| HappyAbsSyn11 ((Language.Lambda.Syntax.Abs.BNFC'Position, Language.Lambda.Syntax.Abs.Program))
	| HappyAbsSyn12 ((Language.Lambda.Syntax.Abs.BNFC'Position, Language.Lambda.Syntax.Abs.Term))
	| HappyAbsSyn15 ((Language.Lambda.Syntax.Abs.BNFC'Position, [Language.Lambda.Syntax.Abs.Term]))
	| HappyAbsSyn16 ((Language.Lambda.Syntax.Abs.BNFC'Position, Language.Lambda.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn17 ((Language.Lambda.Syntax.Abs.BNFC'Position, Language.Lambda.Syntax.Abs.Pattern))

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,114) ([0,7938,32768,1024,8192,496,2048,64,512,31,49280,7,0,1,16384,0,0,0,0,0,0,0,0,0,0,0,0,32,1,0,0,7938,0,1024,0,256,2048,0,512,0,2048,0,0,0,16392,0,7938,0,0,0,0,0,0,0,0,256,0,0,0,31752,0,7938,32768,1984,0,1,0,1,3072,0,0,0,61472,1,31752,0,7938,0,1,16384,0,0,0,0,0,0,0,0,0,512,0,4,0,0,8192,496,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pTerm2_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pListTerm_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","Term2","Term","Term1","ListTerm","ScopedTerm","Pattern","'('","')'","','","'.'","';'","'='","'in'","'let'","'\955'","'\960\8321'","'\960\8322'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 30
        bit_end = (st Prelude.+ 1) Prelude.* 30
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..29]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (18) = happyShift action_16
action_0 (25) = happyShift action_17
action_0 (26) = happyShift action_18
action_0 (27) = happyShift action_19
action_0 (28) = happyShift action_20
action_0 (29) = happyShift action_8
action_0 (10) = happyGoto action_11
action_0 (11) = happyGoto action_27
action_0 (12) = happyGoto action_12
action_0 (13) = happyGoto action_21
action_0 (14) = happyGoto action_14
action_0 (15) = happyGoto action_28
action_0 _ = happyReduce_19

action_1 (18) = happyShift action_24
action_1 (29) = happyShift action_8
action_1 (10) = happyGoto action_11
action_1 (12) = happyGoto action_26
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (18) = happyShift action_16
action_2 (25) = happyShift action_17
action_2 (26) = happyShift action_18
action_2 (27) = happyShift action_19
action_2 (28) = happyShift action_20
action_2 (29) = happyShift action_8
action_2 (10) = happyGoto action_11
action_2 (12) = happyGoto action_12
action_2 (13) = happyGoto action_25
action_2 (14) = happyGoto action_14
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (18) = happyShift action_24
action_3 (29) = happyShift action_8
action_3 (10) = happyGoto action_11
action_3 (12) = happyGoto action_12
action_3 (14) = happyGoto action_23
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (18) = happyShift action_16
action_4 (25) = happyShift action_17
action_4 (26) = happyShift action_18
action_4 (27) = happyShift action_19
action_4 (28) = happyShift action_20
action_4 (29) = happyShift action_8
action_4 (10) = happyGoto action_11
action_4 (12) = happyGoto action_12
action_4 (13) = happyGoto action_21
action_4 (14) = happyGoto action_14
action_4 (15) = happyGoto action_22
action_4 _ = happyReduce_19

action_5 (18) = happyShift action_16
action_5 (25) = happyShift action_17
action_5 (26) = happyShift action_18
action_5 (27) = happyShift action_19
action_5 (28) = happyShift action_20
action_5 (29) = happyShift action_8
action_5 (10) = happyGoto action_11
action_5 (12) = happyGoto action_12
action_5 (13) = happyGoto action_13
action_5 (14) = happyGoto action_14
action_5 (16) = happyGoto action_15
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (29) = happyShift action_8
action_6 (10) = happyGoto action_9
action_6 (17) = happyGoto action_10
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (29) = happyShift action_8
action_7 _ = happyFail (happyExpListPerState 7)

action_8 _ = happyReduce_7

action_9 _ = happyReduce_22

action_10 (30) = happyAccept
action_10 _ = happyFail (happyExpListPerState 10)

action_11 _ = happyReduce_9

action_12 _ = happyReduce_18

action_13 _ = happyReduce_21

action_14 (18) = happyShift action_24
action_14 (29) = happyShift action_8
action_14 (10) = happyGoto action_11
action_14 (12) = happyGoto action_30
action_14 _ = happyReduce_16

action_15 (30) = happyAccept
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (18) = happyShift action_16
action_16 (25) = happyShift action_17
action_16 (26) = happyShift action_18
action_16 (27) = happyShift action_19
action_16 (28) = happyShift action_20
action_16 (29) = happyShift action_8
action_16 (10) = happyGoto action_11
action_16 (12) = happyGoto action_12
action_16 (13) = happyGoto action_36
action_16 (14) = happyGoto action_14
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (29) = happyShift action_8
action_17 (10) = happyGoto action_9
action_17 (17) = happyGoto action_35
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (29) = happyShift action_8
action_18 (10) = happyGoto action_9
action_18 (17) = happyGoto action_34
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (18) = happyShift action_33
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (18) = happyShift action_32
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (22) = happyShift action_31
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (30) = happyAccept
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (18) = happyShift action_24
action_23 (29) = happyShift action_8
action_23 (30) = happyAccept
action_23 (10) = happyGoto action_11
action_23 (12) = happyGoto action_30
action_23 _ = happyFail (happyExpListPerState 23)

action_24 (18) = happyShift action_16
action_24 (25) = happyShift action_17
action_24 (26) = happyShift action_18
action_24 (27) = happyShift action_19
action_24 (28) = happyShift action_20
action_24 (29) = happyShift action_8
action_24 (10) = happyGoto action_11
action_24 (12) = happyGoto action_12
action_24 (13) = happyGoto action_29
action_24 (14) = happyGoto action_14
action_24 _ = happyFail (happyExpListPerState 24)

action_25 (30) = happyAccept
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (30) = happyAccept
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (30) = happyAccept
action_27 _ = happyFail (happyExpListPerState 27)

action_28 _ = happyReduce_8

action_29 (19) = happyShift action_37
action_29 _ = happyFail (happyExpListPerState 29)

action_30 _ = happyReduce_17

action_31 (18) = happyShift action_16
action_31 (25) = happyShift action_17
action_31 (26) = happyShift action_18
action_31 (27) = happyShift action_19
action_31 (28) = happyShift action_20
action_31 (29) = happyShift action_8
action_31 (10) = happyGoto action_11
action_31 (12) = happyGoto action_12
action_31 (13) = happyGoto action_21
action_31 (14) = happyGoto action_14
action_31 (15) = happyGoto action_43
action_31 _ = happyReduce_19

action_32 (18) = happyShift action_16
action_32 (25) = happyShift action_17
action_32 (26) = happyShift action_18
action_32 (27) = happyShift action_19
action_32 (28) = happyShift action_20
action_32 (29) = happyShift action_8
action_32 (10) = happyGoto action_11
action_32 (12) = happyGoto action_12
action_32 (13) = happyGoto action_42
action_32 (14) = happyGoto action_14
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (18) = happyShift action_16
action_33 (25) = happyShift action_17
action_33 (26) = happyShift action_18
action_33 (27) = happyShift action_19
action_33 (28) = happyShift action_20
action_33 (29) = happyShift action_8
action_33 (10) = happyGoto action_11
action_33 (12) = happyGoto action_12
action_33 (13) = happyGoto action_41
action_33 (14) = happyGoto action_14
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (21) = happyShift action_40
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (23) = happyShift action_39
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (19) = happyShift action_37
action_36 (20) = happyShift action_38
action_36 _ = happyFail (happyExpListPerState 36)

action_37 _ = happyReduce_10

action_38 (18) = happyShift action_16
action_38 (25) = happyShift action_17
action_38 (26) = happyShift action_18
action_38 (27) = happyShift action_19
action_38 (28) = happyShift action_20
action_38 (29) = happyShift action_8
action_38 (10) = happyGoto action_11
action_38 (12) = happyGoto action_12
action_38 (13) = happyGoto action_48
action_38 (14) = happyGoto action_14
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (18) = happyShift action_16
action_39 (25) = happyShift action_17
action_39 (26) = happyShift action_18
action_39 (27) = happyShift action_19
action_39 (28) = happyShift action_20
action_39 (29) = happyShift action_8
action_39 (10) = happyGoto action_11
action_39 (12) = happyGoto action_12
action_39 (13) = happyGoto action_47
action_39 (14) = happyGoto action_14
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (18) = happyShift action_16
action_40 (25) = happyShift action_17
action_40 (26) = happyShift action_18
action_40 (27) = happyShift action_19
action_40 (28) = happyShift action_20
action_40 (29) = happyShift action_8
action_40 (10) = happyGoto action_11
action_40 (12) = happyGoto action_12
action_40 (13) = happyGoto action_13
action_40 (14) = happyGoto action_14
action_40 (16) = happyGoto action_46
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (19) = happyShift action_45
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (19) = happyShift action_44
action_42 _ = happyFail (happyExpListPerState 42)

action_43 _ = happyReduce_20

action_44 _ = happyReduce_14

action_45 _ = happyReduce_13

action_46 _ = happyReduce_11

action_47 (24) = happyShift action_50
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (19) = happyShift action_49
action_48 _ = happyFail (happyExpListPerState 48)

action_49 _ = happyReduce_12

action_50 (18) = happyShift action_16
action_50 (25) = happyShift action_17
action_50 (26) = happyShift action_18
action_50 (27) = happyShift action_19
action_50 (28) = happyShift action_20
action_50 (29) = happyShift action_8
action_50 (10) = happyGoto action_11
action_50 (12) = happyGoto action_12
action_50 (13) = happyGoto action_13
action_50 (14) = happyGoto action_14
action_50 (16) = happyGoto action_51
action_50 _ = happyFail (happyExpListPerState 50)

action_51 _ = happyReduce_15

happyReduce_7 = happySpecReduce_1  10 happyReduction_7
happyReduction_7 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn10
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_1  11 happyReduction_8
happyReduction_8 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn11
		 ((fst happy_var_1, Language.Lambda.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  12 happyReduction_9
happyReduction_9 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn12
		 ((fst happy_var_1, Language.Lambda.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  12 happyReduction_10
happyReduction_10 _
	(HappyAbsSyn12  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happyReduce 4 13 happyReduction_11
happyReduction_11 ((HappyAbsSyn16  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.Lam (uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_12 = happyReduce 5 13 happyReduction_12
happyReduction_12 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.Pair (uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_13 = happyReduce 4 13 happyReduction_13
happyReduction_13 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.First (uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_14 = happyReduce 4 13 happyReduction_14
happyReduction_14 (_ `HappyStk`
	(HappyAbsSyn12  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.Second (uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_15 = happyReduce 6 13 happyReduction_15
happyReduction_15 ((HappyAbsSyn16  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 ((uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.Lambda.Syntax.Abs.Let (uncurry Language.Lambda.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_16 = happySpecReduce_1  13 happyReduction_16
happyReduction_16 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_2  14 happyReduction_17
happyReduction_17 (HappyAbsSyn12  happy_var_2)
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 ((fst happy_var_1, Language.Lambda.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  14 happyReduction_18
happyReduction_18 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_0  15 happyReduction_19
happyReduction_19  =  HappyAbsSyn15
		 ((Language.Lambda.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_20 = happySpecReduce_3  15 happyReduction_20
happyReduction_20 (HappyAbsSyn15  happy_var_3)
	_
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_20 _ _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  16 happyReduction_21
happyReduction_21 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn16
		 ((fst happy_var_1, Language.Lambda.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  17 happyReduction_22
happyReduction_22 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn17
		 ((fst happy_var_1, Language.Lambda.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_22 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 30 30 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 18;
	PT _ (TS _ 2) -> cont 19;
	PT _ (TS _ 3) -> cont 20;
	PT _ (TS _ 4) -> cont 21;
	PT _ (TS _ 5) -> cont 22;
	PT _ (TS _ 6) -> cont 23;
	PT _ (TS _ 7) -> cont 24;
	PT _ (TS _ 8) -> cont 25;
	PT _ (TS _ 9) -> cont 26;
	PT _ (TS _ 10) -> cont 27;
	PT _ (TS _ 11) -> cont 28;
	PT _ (T_VarIdent _) -> cont 29;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 30 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn11 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

pListTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn16 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn17 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


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

pProgram :: [Token] -> Err Language.Lambda.Syntax.Abs.Program
pProgram = fmap snd . pProgram_internal

pTerm2 :: [Token] -> Err Language.Lambda.Syntax.Abs.Term
pTerm2 = fmap snd . pTerm2_internal

pTerm :: [Token] -> Err Language.Lambda.Syntax.Abs.Term
pTerm = fmap snd . pTerm_internal

pTerm1 :: [Token] -> Err Language.Lambda.Syntax.Abs.Term
pTerm1 = fmap snd . pTerm1_internal

pListTerm :: [Token] -> Err [Language.Lambda.Syntax.Abs.Term]
pListTerm = fmap snd . pListTerm_internal

pScopedTerm :: [Token] -> Err Language.Lambda.Syntax.Abs.ScopedTerm
pScopedTerm = fmap snd . pScopedTerm_internal

pPattern :: [Token] -> Err Language.Lambda.Syntax.Abs.Pattern
pPattern = fmap snd . pPattern_internal
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
