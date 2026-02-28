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
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_3 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_4 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((y_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 2 )) |]
.

Definition foo_safety_wit_5 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_6 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((z_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + 3 )) |]
.

Definition foo_safety_wit_7 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_return_wit_1 := 
  TT && emp 
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
Axiom proof_of_foo_return_wit_1 : foo_return_wit_1.

End VC_Correct.
