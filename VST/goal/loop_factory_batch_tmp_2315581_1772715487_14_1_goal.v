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
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) (wg9_pre: Z) ,
  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> wg9_pre)
|--
  [| ((r_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (r_pre - 1 )) |]
.

Definition foo_safety_wit_2 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) (wg9_pre: Z) ,
  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> wg9_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) (wg9_pre: Z) ,
  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> wg9_pre)
|--
  [| ((la_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_4 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) (wg9_pre: Z) ,
  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> wg9_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_5 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> (la_pre % ( 5 ) ))
|--
  [| (((la_pre - (la_pre % ( 5 ) ) ) <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_6 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> (la_pre % ( 5 ) ))
|--
  [| ((la_pre - (la_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (la_pre - (la_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_7 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> (la_pre % ( 5 ) ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_8 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ))
|--
  [| (((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) )) |]
.

Definition foo_safety_wit_9 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ))
|--
  [| ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) )) |]
.

Definition foo_safety_wit_10 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> (la_pre % ( 5 ) ))
|--
  [| (((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_11 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ))
|--
  [| ((la_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (la_pre + 1 )) |]
.

Definition foo_safety_wit_12 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> la_pre)
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) ))
|--
  [| ((la_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (la_pre + 1 )) |]
.

Definition foo_safety_wit_13 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) ))
|--
  [| ((z_pre + ((la_pre + 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + ((la_pre + 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_14 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) ))
|--
  [| (((la_pre + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_15 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((la_pre % ( 5 ) ) + (la_pre % ( 5 ) ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_16 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ))
|--
  [| ((z_pre + ((la_pre + 1 ) % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + ((la_pre + 1 ) % ( 2 ) ) )) |]
.

Definition foo_safety_wit_17 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ))
|--
  [| (((la_pre + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_18 := 
forall (z_pre: Z) (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "la" ) )) # Int  |-> (la_pre + 1 ))
  **  ((( &( "wg9" ) )) # Int  |-> ((((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) + ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ) - ((la_pre - (la_pre % ( 5 ) ) ) % ( 5 ) ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_return_wit_1_1 := 
forall (r_pre: Z) (la_pre: Z) ,
  [| (la_pre > (r_pre - 1 )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (r_pre: Z) (la_pre: Z) ,
  [| (la_pre < (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (r_pre: Z) (la_pre: Z) ,
  [| (la_pre >= (la_pre % ( 5 ) )) |] 
  &&  [| (la_pre <= (r_pre - 1 )) |]
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
Axiom proof_of_foo_safety_wit_17 : foo_safety_wit_17.
Axiom proof_of_foo_safety_wit_18 : foo_safety_wit_18.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
