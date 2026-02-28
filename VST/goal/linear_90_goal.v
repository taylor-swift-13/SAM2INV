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
forall (x_pre: Z) (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (lock_pre: Z) (y_pre: Z) ,
  [| (x_pre <> y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "lock" ) )) # Int  |-> lock_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (x_pre: Z) (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (lock_pre: Z) (y_pre: Z) ,
  [| (x_pre <> y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "lock" ) )) # Int  |-> lock_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (x_pre: Z) (y_pre: Z) ,
  [| (x_pre = y_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (x_pre: Z) (y_pre: Z) ,
  [| (x_pre <> y_pre) |]
  &&  emp
|--
  TT && emp 
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_foo_safety_wit_1 : foo_safety_wit_1.
Axiom proof_of_foo_safety_wit_2 : foo_safety_wit_2.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.

End VC_Correct.
