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
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre < 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((v_pre + (2 * Y_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre + (2 * Y_pre ) )) |]
.

Definition foo_safety_wit_3 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre < 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((2 * Y_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * Y_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre < 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_5 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((v_pre + (2 * (Y_pre - X_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre + (2 * (Y_pre - X_pre ) ) )) |]
.

Definition foo_safety_wit_6 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((2 * (Y_pre - X_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * (Y_pre - X_pre ) )) |]
.

Definition foo_safety_wit_7 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_8 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((Y_pre - X_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (Y_pre - X_pre )) |]
.

Definition foo_safety_wit_9 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre + (2 * (Y_pre - X_pre ) ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((y_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 1 )) |]
.

Definition foo_safety_wit_10 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre < 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre + (2 * Y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_11 := 
forall (X_pre: Z) (Y_pre: Z) (v_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  ((( &( "X" ) )) # Int  |-> X_pre)
  **  ((( &( "Y" ) )) # Int  |-> Y_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre + (2 * (Y_pre - X_pre ) ) ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_return_wit_1_1 := 
forall (X_pre: Z) (x_pre: Z) ,
  [| (x_pre > X_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (X_pre: Z) (v_pre: Z) (x_pre: Z) ,
  [| (v_pre < 0) |] 
  &&  [| (x_pre <= X_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (X_pre: Z) (v_pre: Z) (x_pre: Z) ,
  [| (v_pre >= 0) |] 
  &&  [| (x_pre <= X_pre) |]
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
