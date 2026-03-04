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
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((v_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre + 5 )) |]
.

Definition foo_safety_wit_2 := 
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_3 := 
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  [| ((v_pre + 5 ) <= r_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((j_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  [| ((v_pre + 5 ) <= r_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  [| ((j_pre + 1 ) <= r_pre) |] 
  &&  [| ((v_pre + 5 ) <= r_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((j_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j_pre + 1 )) |]
.

Definition foo_safety_wit_6 := 
forall (k_pre: Z) (p_pre: Z) (q_pre: Z) (r_pre: Z) (v_pre: Z) (j_pre: Z) (z_pre: Z) ,
  [| ((j_pre + 1 ) <= r_pre) |] 
  &&  [| ((v_pre + 5 ) <= r_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (r_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 5 ) > r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (r_pre: Z) (v_pre: Z) (j_pre: Z) ,
  [| ((j_pre + 1 ) > r_pre) |] 
  &&  [| ((v_pre + 5 ) <= r_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (r_pre: Z) (v_pre: Z) (j_pre: Z) ,
  [| ((j_pre + 1 ) <= r_pre) |] 
  &&  [| ((v_pre + 5 ) <= r_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
