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
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((2 * k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * k_pre )) |]
.

Definition foo_safety_wit_2 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_3 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_6 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre = 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_7 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre = 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> 0)
|--
  [| ((i_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i_pre + 1 )) |]
.

Definition foo_safety_wit_8 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre = 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_9 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre <> 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_10 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre <> 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> 1)
|--
  [| ((j_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j_pre + 1 )) |]
.

Definition foo_safety_wit_11 := 
forall (i_pre: Z) (j_pre: Z) (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre <> 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "b" ) )) # Int  |-> 1)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (k_pre: Z) (n_pre: Z) ,
  [| (n_pre >= (2 * k_pre )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre <> 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (k_pre: Z) (n_pre: Z) (b_pre: Z) ,
  [| (b_pre = 1) |] 
  &&  [| (n_pre < (2 * k_pre )) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
