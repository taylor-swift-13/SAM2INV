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
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> k6lf_pre)
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> k6lf_pre)
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((c_pre + (h_pre * p_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c_pre + (h_pre * p_pre ) )) |]
.

Definition foo_safety_wit_3 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> k6lf_pre)
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((h_pre * p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * p_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> k6lf_pre)
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((k6lf_pre + (h_pre * h_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k6lf_pre + (h_pre * h_pre ) )) |]
.

Definition foo_safety_wit_5 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> k6lf_pre)
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((h_pre * h_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * h_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((w1_pre + (p_pre * p_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w1_pre + (p_pre * p_pre ) )) |]
.

Definition foo_safety_wit_7 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((p_pre * p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * p_pre )) |]
.

Definition foo_safety_wit_8 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((f7r_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (f7r_pre - 1 )) |]
.

Definition foo_safety_wit_9 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> f7r_pre)
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_10 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((f7r_pre - 1 ) * (f7r_pre - 1 ) )) |]
.

Definition foo_safety_wit_11 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((h8_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h8_pre + 3 )) |]
.

Definition foo_safety_wit_12 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_13 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((p_pre * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * 2 )) |]
.

Definition foo_safety_wit_14 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_15 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((i_pre <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_16 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_17 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_18 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((i_pre <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_19 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_20 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_21 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_22 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_23 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_24 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_25 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((q3_pre + (g_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q3_pre + (g_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_26 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((q3_pre + (g_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q3_pre + (g_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_27 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((q3_pre + g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q3_pre + g_pre )) |]
.

Definition foo_safety_wit_28 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> q3_pre)
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((q3_pre + g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q3_pre + g_pre )) |]
.

Definition foo_safety_wit_29 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_30 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_31 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((h_pre * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * 4 )) |]
.

Definition foo_safety_wit_32 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_33 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (((f7r_pre - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_34 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_35 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_36 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_37 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_38 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((h_pre * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * 4 )) |]
.

Definition foo_safety_wit_39 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_40 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (((f7r_pre - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_41 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_42 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_43 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_44 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_45 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((h_pre * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * 4 )) |]
.

Definition foo_safety_wit_46 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_47 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((f7r_pre - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_48 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_49 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_50 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_51 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_52 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| ((h_pre * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (h_pre * 4 )) |]
.

Definition foo_safety_wit_53 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_54 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((f7r_pre - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_55 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_56 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_57 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) )) |]
.

Definition foo_safety_wit_58 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre % ( 5 ) ))
|--
  [| (((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) )) |]
.

Definition foo_safety_wit_59 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) )) |]
.

Definition foo_safety_wit_60 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> g_pre)
|--
  [| ((g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) )) |]
.

Definition foo_safety_wit_61 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| ((p_pre <> (INT_MIN)) \/ (9 <> (-1))) |] 
  &&  [| (9 <> 0) |]
.

Definition foo_safety_wit_62 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition foo_safety_wit_63 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((p_pre * 2 ) <> (INT_MIN)) \/ (9 <> (-1))) |] 
  &&  [| (9 <> 0) |]
.

Definition foo_safety_wit_64 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition foo_safety_wit_65 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((p_pre * 2 ) <> (INT_MIN)) \/ (9 <> (-1))) |] 
  &&  [| (9 <> 0) |]
.

Definition foo_safety_wit_66 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre * 2 ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition foo_safety_wit_67 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| ((p_pre <> (INT_MIN)) \/ (9 <> (-1))) |] 
  &&  [| (9 <> 0) |]
.

Definition foo_safety_wit_68 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition foo_safety_wit_69 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 )) |]
.

Definition foo_safety_wit_70 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_71 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> ((p_pre * 2 ) % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 )) |]
.

Definition foo_safety_wit_72 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> ((p_pre * 2 ) % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + (g_pre % ( 5 ) ) ))
  **  ((( &( "g" ) )) # Int  |-> ((g_pre % ( 5 ) ) + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_73 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> ((p_pre * 2 ) % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 )) |]
.

Definition foo_safety_wit_74 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> ((p_pre * 2 ) % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_75 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) + 4 )) |]
.

Definition foo_safety_wit_76 := 
forall (h_pre: Z) (p_pre: Z) (h8_pre: Z) (i_pre: Z) (k6lf_pre: Z) (w1_pre: Z) (c_pre: Z) (f7r_pre: Z) (q3_pre: Z) (g_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  ((( &( "h" ) )) # Int  |-> (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ))
  **  ((( &( "p" ) )) # Int  |-> (p_pre % ( 9 ) ))
  **  ((( &( "h8" ) )) # Int  |-> h8_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "k6lf" ) )) # Int  |-> (k6lf_pre + (h_pre * h_pre ) ))
  **  ((( &( "w1" ) )) # Int  |-> (w1_pre + (p_pre * p_pre ) ))
  **  ((( &( "c" ) )) # Int  |-> (c_pre + (h_pre * p_pre ) ))
  **  ((( &( "f7r" ) )) # Int  |-> (f7r_pre - 1 ))
  **  ((( &( "q3" ) )) # Int  |-> (q3_pre + g_pre ))
  **  ((( &( "g" ) )) # Int  |-> (g_pre + (((h_pre * 4 ) + ((f7r_pre - 1 ) % ( 2 ) ) ) + 0 ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_return_wit_1_1 := 
forall (f7r_pre: Z) ,
  [| (f7r_pre < 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (h8_pre: Z) (i_pre: Z) (f7r_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (h8_pre: Z) (i_pre: Z) (f7r_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (h8_pre: Z) (i_pre: Z) (f7r_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) <= (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (h8_pre: Z) (i_pre: Z) (f7r_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (((f7r_pre - 1 ) * (f7r_pre - 1 ) ) > (h8_pre + 3 )) |] 
  &&  [| (f7r_pre >= 1) |]
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
Axiom proof_of_foo_safety_wit_47 : foo_safety_wit_47.
Axiom proof_of_foo_safety_wit_48 : foo_safety_wit_48.
Axiom proof_of_foo_safety_wit_49 : foo_safety_wit_49.
Axiom proof_of_foo_safety_wit_50 : foo_safety_wit_50.
Axiom proof_of_foo_safety_wit_51 : foo_safety_wit_51.
Axiom proof_of_foo_safety_wit_52 : foo_safety_wit_52.
Axiom proof_of_foo_safety_wit_53 : foo_safety_wit_53.
Axiom proof_of_foo_safety_wit_54 : foo_safety_wit_54.
Axiom proof_of_foo_safety_wit_55 : foo_safety_wit_55.
Axiom proof_of_foo_safety_wit_56 : foo_safety_wit_56.
Axiom proof_of_foo_safety_wit_57 : foo_safety_wit_57.
Axiom proof_of_foo_safety_wit_58 : foo_safety_wit_58.
Axiom proof_of_foo_safety_wit_59 : foo_safety_wit_59.
Axiom proof_of_foo_safety_wit_60 : foo_safety_wit_60.
Axiom proof_of_foo_safety_wit_61 : foo_safety_wit_61.
Axiom proof_of_foo_safety_wit_62 : foo_safety_wit_62.
Axiom proof_of_foo_safety_wit_63 : foo_safety_wit_63.
Axiom proof_of_foo_safety_wit_64 : foo_safety_wit_64.
Axiom proof_of_foo_safety_wit_65 : foo_safety_wit_65.
Axiom proof_of_foo_safety_wit_66 : foo_safety_wit_66.
Axiom proof_of_foo_safety_wit_67 : foo_safety_wit_67.
Axiom proof_of_foo_safety_wit_68 : foo_safety_wit_68.
Axiom proof_of_foo_safety_wit_69 : foo_safety_wit_69.
Axiom proof_of_foo_safety_wit_70 : foo_safety_wit_70.
Axiom proof_of_foo_safety_wit_71 : foo_safety_wit_71.
Axiom proof_of_foo_safety_wit_72 : foo_safety_wit_72.
Axiom proof_of_foo_safety_wit_73 : foo_safety_wit_73.
Axiom proof_of_foo_safety_wit_74 : foo_safety_wit_74.
Axiom proof_of_foo_safety_wit_75 : foo_safety_wit_75.
Axiom proof_of_foo_safety_wit_76 : foo_safety_wit_76.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.

End VC_Correct.
