Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import int_array_lib.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.

(*----- Function foo -----*)

Definition foo_safety_wit_1 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_3 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_4 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| ((m_pre * m_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m_pre * m_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| ((s_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s_pre + 6 )) |]
.

Definition foo_safety_wit_7 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_8 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| ((m_pre * m_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m_pre * m_pre )) |]
.

Definition foo_safety_wit_9 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| ((s_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s_pre + 6 )) |]
.

Definition foo_safety_wit_10 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_11 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((m_pre * m_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m_pre * m_pre )) |]
.

Definition foo_safety_wit_12 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((s_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s_pre + 6 )) |]
.

Definition foo_safety_wit_13 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_14 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| ((2 <> (INT_MIN)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition foo_safety_wit_15 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_16 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| ((1 <> (INT_MIN)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition foo_safety_wit_17 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_18 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre <> (INT_MIN)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition foo_safety_wit_19 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_20 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 2)
|--
  [| ((2 + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 + 2 )) |]
.

Definition foo_safety_wit_21 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> 1)
|--
  [| ((1 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 + 1 )) |]
.

Definition foo_safety_wit_22 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre + g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + g_pre )) |]
.

Definition foo_safety_wit_23 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 4 ) ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_24 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 4 ) ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_25 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 4 ) ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_26 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 % ( 4 ) ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_27 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 % ( 4 ) ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_28 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 % ( 4 ) ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_29 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 % ( 4 ) ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_30 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 % ( 4 ) ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_31 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 % ( 4 ) ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_32 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre + g_pre ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_33 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre + g_pre ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_34 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre + g_pre ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_35 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 + 1 ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_36 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 + 1 ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_37 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 + 1 ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_38 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 + 2 ))
|--
  [| ((x_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 6 )) |]
.

Definition foo_safety_wit_39 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 + 2 ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_40 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 + 2 ))
|--
  [| ((b_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + s_pre )) |]
.

Definition foo_safety_wit_41 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 4 ) ))
|--
  [| (((g_pre % ( 4 ) ) * (g_pre % ( 4 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((g_pre % ( 4 ) ) * (g_pre % ( 4 ) ) )) |]
.

Definition foo_safety_wit_42 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 % ( 4 ) ))
|--
  [| (((1 % ( 4 ) ) * (1 % ( 4 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((1 % ( 4 ) ) * (1 % ( 4 ) ) )) |]
.

Definition foo_safety_wit_43 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 % ( 4 ) ))
|--
  [| (((2 % ( 4 ) ) * (2 % ( 4 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 % ( 4 ) ) * (2 % ( 4 ) ) )) |]
.

Definition foo_safety_wit_44 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre + g_pre ))
|--
  [| (((g_pre + g_pre ) * (g_pre + g_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((g_pre + g_pre ) * (g_pre + g_pre ) )) |]
.

Definition foo_safety_wit_45 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (1 + 1 ))
|--
  [| (((1 + 1 ) * (1 + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((1 + 1 ) * (1 + 1 ) )) |]
.

Definition foo_safety_wit_46 := 
forall (b_pre: Z) (m_pre: Z) (p_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "g" ) )) # Int  |-> (2 + 2 ))
|--
  [| (((2 + 2 ) * (2 + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 + 2 ) * (2 + 2 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (s_pre: Z) (x_pre: Z) ,
  [| (x_pre <= s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_6 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_7 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) > (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_8 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_9 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_10 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) <= (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_11 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre <> 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_12 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 2) |] 
  &&  [| (g_pre <> 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_13 := 
forall (b_pre: Z) (m_pre: Z) (s_pre: Z) (x_pre: Z) (g_pre: Z) ,
  [| ((x_pre + 6 ) <= (b_pre + s_pre )) |] 
  &&  [| ((m_pre * m_pre ) > (s_pre + 6 )) |] 
  &&  [| (g_pre = 1) |] 
  &&  [| (x_pre > s_pre) |]
  &&  emp
|--
  TT && emp 
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_foo_safety_wit_1 : foo_safety_wit_1.
Axiom proof_of_foo_safety_wit_2 : foo_safety_wit_2.
Axiom proof_of_foo_safety_wit_3 : foo_safety_wit_3.
Axiom proof_of_foo_safety_wit_4 : foo_safety_wit_4.
Axiom proof_of_foo_safety_wit_5 : foo_safety_wit_5.
Axiom proof_of_foo_safety_wit_6 : foo_safety_wit_6.
Axiom proof_of_foo_safety_wit_7 : foo_safety_wit_7.
Axiom proof_of_foo_safety_wit_8 : foo_safety_wit_8.
Axiom proof_of_foo_safety_wit_9 : foo_safety_wit_9.
Axiom proof_of_foo_safety_wit_10 : foo_safety_wit_10.
Axiom proof_of_foo_safety_wit_11 : foo_safety_wit_11.
Axiom proof_of_foo_safety_wit_12 : foo_safety_wit_12.
Axiom proof_of_foo_safety_wit_13 : foo_safety_wit_13.
Axiom proof_of_foo_safety_wit_14 : foo_safety_wit_14.
Axiom proof_of_foo_safety_wit_15 : foo_safety_wit_15.
Axiom proof_of_foo_safety_wit_16 : foo_safety_wit_16.
Axiom proof_of_foo_safety_wit_17 : foo_safety_wit_17.
Axiom proof_of_foo_safety_wit_18 : foo_safety_wit_18.
Axiom proof_of_foo_safety_wit_19 : foo_safety_wit_19.
Axiom proof_of_foo_safety_wit_20 : foo_safety_wit_20.
Axiom proof_of_foo_safety_wit_21 : foo_safety_wit_21.
Axiom proof_of_foo_safety_wit_22 : foo_safety_wit_22.
Axiom proof_of_foo_safety_wit_23 : foo_safety_wit_23.
Axiom proof_of_foo_safety_wit_24 : foo_safety_wit_24.
Axiom proof_of_foo_safety_wit_25 : foo_safety_wit_25.
Axiom proof_of_foo_safety_wit_26 : foo_safety_wit_26.
Axiom proof_of_foo_safety_wit_27 : foo_safety_wit_27.
Axiom proof_of_foo_safety_wit_28 : foo_safety_wit_28.
Axiom proof_of_foo_safety_wit_29 : foo_safety_wit_29.
Axiom proof_of_foo_safety_wit_30 : foo_safety_wit_30.
Axiom proof_of_foo_safety_wit_31 : foo_safety_wit_31.
Axiom proof_of_foo_safety_wit_32 : foo_safety_wit_32.
Axiom proof_of_foo_safety_wit_33 : foo_safety_wit_33.
Axiom proof_of_foo_safety_wit_34 : foo_safety_wit_34.
Axiom proof_of_foo_safety_wit_35 : foo_safety_wit_35.
Axiom proof_of_foo_safety_wit_36 : foo_safety_wit_36.
Axiom proof_of_foo_safety_wit_37 : foo_safety_wit_37.
Axiom proof_of_foo_safety_wit_38 : foo_safety_wit_38.
Axiom proof_of_foo_safety_wit_39 : foo_safety_wit_39.
Axiom proof_of_foo_safety_wit_40 : foo_safety_wit_40.
Axiom proof_of_foo_safety_wit_41 : foo_safety_wit_41.
Axiom proof_of_foo_safety_wit_42 : foo_safety_wit_42.
Axiom proof_of_foo_safety_wit_43 : foo_safety_wit_43.
Axiom proof_of_foo_safety_wit_44 : foo_safety_wit_44.
Axiom proof_of_foo_safety_wit_45 : foo_safety_wit_45.
Axiom proof_of_foo_safety_wit_46 : foo_safety_wit_46.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.
Axiom proof_of_foo_return_wit_1_6 : foo_return_wit_1_6.
Axiom proof_of_foo_return_wit_1_7 : foo_return_wit_1_7.
Axiom proof_of_foo_return_wit_1_8 : foo_return_wit_1_8.
Axiom proof_of_foo_return_wit_1_9 : foo_return_wit_1_9.
Axiom proof_of_foo_return_wit_1_10 : foo_return_wit_1_10.
Axiom proof_of_foo_return_wit_1_11 : foo_return_wit_1_11.
Axiom proof_of_foo_return_wit_1_12 : foo_return_wit_1_12.
Axiom proof_of_foo_return_wit_1_13 : foo_return_wit_1_13.

End VC_Correct.
