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
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((y_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_3 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_4 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((z_pre + x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + x_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| ((y_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre - 1 )) |]
.

Definition foo_safety_wit_7 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_8 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (y_pre - 1 ))
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| ((2 * x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * x_pre )) |]
.

Definition foo_safety_wit_9 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (y_pre - 1 ))
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_10 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((2 * x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * x_pre )) |]
.

Definition foo_safety_wit_11 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_12 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> (2 * x_pre ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| ((y_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_13 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> (2 * x_pre ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_14 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> (2 * x_pre ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre - 1 ))
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| (((y_pre - 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_15 := 
forall (a_pre: Z) (b_pre: Z) (x_pre: Z) (y_pre: Z) (z_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> (2 * x_pre ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre - 1 ))
  **  ((( &( "z" ) )) # Int  |-> (z_pre + x_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_return_wit_1_1 := 
forall (y_pre: Z) ,
  [| (y_pre = 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (y_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (y_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
