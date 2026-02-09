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

(*----- Function foo_3 -----*)

Definition foo_3_safety_wit_1 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_3_safety_wit_2 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| False |]
.

Definition foo_3_safety_wit_3 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| ((y_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 1 )) |]
.

Definition foo_3_safety_wit_4 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_3_safety_wit_5 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 1 ))
|--
  [| ((a_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre - 1 )) |]
.

Definition foo_3_safety_wit_6 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 1 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_3_return_wit_1 := 
forall (x_pre: Z) (a_pre: Z) (y_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (a_pre = 64) |] 
  &&  [| (x_pre = 64) |]
  &&  emp
|--
  TT && emp 
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_foo_3_safety_wit_1 : foo_3_safety_wit_1.
Axiom proof_of_foo_3_safety_wit_2 : foo_3_safety_wit_2.
Axiom proof_of_foo_3_safety_wit_3 : foo_3_safety_wit_3.
Axiom proof_of_foo_3_safety_wit_4 : foo_3_safety_wit_4.
Axiom proof_of_foo_3_safety_wit_5 : foo_3_safety_wit_5.
Axiom proof_of_foo_3_safety_wit_6 : foo_3_safety_wit_6.
Axiom proof_of_foo_3_return_wit_1 : foo_3_return_wit_1.

End VC_Correct.
