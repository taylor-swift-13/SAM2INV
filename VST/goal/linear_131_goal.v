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
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  [| (x1_pre > 0) |]
  &&  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_3 := 
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_4 := 
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  [| (x3_pre > 0) |] 
  &&  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
|--
  [| ((x1_pre - d1_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x1_pre - d1_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  [| (x3_pre > 0) |] 
  &&  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre - d1_pre ))
|--
  [| ((x2_pre - d2_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x2_pre - d2_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (x2_pre: Z) (x3_pre: Z) (d1_pre: Z) (d2_pre: Z) (d3_pre: Z) (x1_pre: Z) ,
  [| (x3_pre > 0) |] 
  &&  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  ((( &( "x2" ) )) # Int  |-> (x2_pre - d2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "d1" ) )) # Int  |-> d1_pre)
  **  ((( &( "d2" ) )) # Int  |-> d2_pre)
  **  ((( &( "d3" ) )) # Int  |-> d3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre - d1_pre ))
|--
  [| ((x3_pre - d3_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x3_pre - d3_pre )) |]
.

Definition foo_return_wit_1_1 := 
forall (x1_pre: Z) ,
  [| (x1_pre <= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (x2_pre: Z) (x1_pre: Z) ,
  [| (x2_pre <= 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (x2_pre: Z) (x3_pre: Z) (x1_pre: Z) ,
  [| (x3_pre <= 0) |] 
  &&  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (x2_pre: Z) (x3_pre: Z) (x1_pre: Z) ,
  [| (x3_pre > 0) |] 
  &&  [| (x2_pre > 0) |] 
  &&  [| (x1_pre > 0) |]
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
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.

End VC_Correct.
