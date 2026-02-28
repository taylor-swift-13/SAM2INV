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
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (((i_pre + x_pre ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i_pre + x_pre ) + 1 )) |]
.

Definition foo_safety_wit_3 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| ((i_pre + x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i_pre + x_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_6 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (((j_pre + y_pre ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((j_pre + y_pre ) + 1 )) |]
.

Definition foo_safety_wit_7 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| ((j_pre + y_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j_pre + y_pre )) |]
.

Definition foo_safety_wit_8 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_9 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((j_pre + y_pre ) + 1 ))
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_10 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((j_pre + y_pre ) + 1 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_11 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((j_pre + y_pre ) + 1 ))
|--
  [| ((y_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 1 )) |]
.

Definition foo_safety_wit_12 := 
forall (x_pre: Z) (y_pre: Z) (i_pre: Z) (j_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i_pre + x_pre ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((j_pre + y_pre ) + 1 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
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
Axiom proof_of_foo_safety_wit_8 : foo_safety_wit_8.
Axiom proof_of_foo_safety_wit_9 : foo_safety_wit_9.
Axiom proof_of_foo_safety_wit_10 : foo_safety_wit_10.
Axiom proof_of_foo_safety_wit_11 : foo_safety_wit_11.
Axiom proof_of_foo_safety_wit_12 : foo_safety_wit_12.
Axiom proof_of_foo_return_wit_1 : foo_return_wit_1.

End VC_Correct.
