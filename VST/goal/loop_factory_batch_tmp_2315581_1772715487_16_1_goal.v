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
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) (zp_pre: Z) ,
  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> zp_pre)
|--
  [| ((uad_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_2 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) (zp_pre: Z) ,
  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> zp_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_3 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (((uad_pre - vb_pre ) <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_4 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((uad_pre - vb_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (uad_pre - vb_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_6 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((uad_pre - vb_pre ) % ( 5 ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) )) |]
.

Definition foo_safety_wit_7 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((uad_pre - vb_pre ) % ( 5 ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_8 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> vb_pre)
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((vb_pre + (uad_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (vb_pre + (uad_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_9 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ) + 1 )) |]
.

Definition foo_safety_wit_10 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_11 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> (vb_pre + (uad_pre % ( 5 ) ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (((vb_pre + (uad_pre % ( 5 ) ) ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((vb_pre + (uad_pre % ( 5 ) ) ) + 1 )) |]
.

Definition foo_safety_wit_12 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> (vb_pre + (uad_pre % ( 5 ) ) ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_13 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((vb_pre + (uad_pre % ( 5 ) ) ) + 1 ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((uad_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (uad_pre + 1 )) |]
.

Definition foo_safety_wit_14 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> ((vb_pre + (uad_pre % ( 5 ) ) ) + 1 ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_15 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> (((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ) + 1 ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| ((uad_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (uad_pre + 1 )) |]
.

Definition foo_safety_wit_16 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  ((( &( "j7x" ) )) # Int  |-> j7x_pre)
  **  ((( &( "uad" ) )) # Int  |-> uad_pre)
  **  ((( &( "vb" ) )) # Int  |-> (((((uad_pre - vb_pre ) % ( 5 ) ) + (uad_pre % ( 5 ) ) ) - ((uad_pre - vb_pre ) % ( 5 ) ) ) + 1 ))
  **  ((( &( "zp" ) )) # Int  |-> (uad_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (j7x_pre: Z) (uad_pre: Z) ,
  [| (uad_pre >= j7x_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre < vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (j7x_pre: Z) (uad_pre: Z) (vb_pre: Z) ,
  [| (uad_pre >= vb_pre) |] 
  &&  [| (uad_pre < j7x_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
