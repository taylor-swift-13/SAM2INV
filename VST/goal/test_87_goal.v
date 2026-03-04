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
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((t_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 2 )) |]
.

Definition foo_safety_wit_2 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_3 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_4 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_5 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_6 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_7 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 2)
|--
  [| ((t_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 2 )) |]
.

Definition foo_safety_wit_8 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 2)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_9 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 2)
|--
  [| ((2 + r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 + r_pre )) |]
.

Definition foo_safety_wit_10 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) > (2 + r_pre )) |] 
  &&  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 2)
|--
  [| False |]
.

Definition foo_safety_wit_11 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 1)
|--
  [| ((t_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 2 )) |]
.

Definition foo_safety_wit_12 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 1)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_13 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 1)
|--
  [| ((1 + r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 + r_pre )) |]
.

Definition foo_safety_wit_14 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) > (1 + r_pre )) |] 
  &&  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 1)
|--
  [| False |]
.

Definition foo_safety_wit_15 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((t_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 2 )) |]
.

Definition foo_safety_wit_16 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_17 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre + r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre + r_pre )) |]
.

Definition foo_safety_wit_18 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (2 + r_pre )) |] 
  &&  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 2)
|--
  [| ((2 * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * 2 )) |]
.

Definition foo_safety_wit_19 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (1 + r_pre )) |] 
  &&  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> 1)
|--
  [| ((1 * 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * 1 )) |]
.

Definition foo_safety_wit_20 := 
forall (b_pre: Z) (k_pre: Z) (p_pre: Z) (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (a_pre + r_pre )) |] 
  &&  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre * a_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre * a_pre )) |]
.

Definition foo_return_wit_1_1 := 
forall (r_pre: Z) (t_pre: Z) ,
  [| ((t_pre + 2 ) > r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) > (a_pre + r_pre )) |] 
  &&  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (2 + r_pre )) |] 
  &&  [| (a_pre = 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (1 + r_pre )) |] 
  &&  [| (a_pre = 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (r_pre: Z) (t_pre: Z) (a_pre: Z) ,
  [| ((t_pre + 2 ) <= (a_pre + r_pre )) |] 
  &&  [| (a_pre <> 2) |] 
  &&  [| (a_pre <> 1) |] 
  &&  [| ((t_pre + 2 ) <= r_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.

End VC_Correct.
