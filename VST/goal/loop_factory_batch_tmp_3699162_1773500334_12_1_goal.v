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
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (o9_pre: Z) (c0y_pre: Z) ,
  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> o9_pre)
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| ((pe_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pe_pre - 1 )) |]
.

Definition foo_safety_wit_2 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (o9_pre: Z) (c0y_pre: Z) ,
  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> o9_pre)
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (o9_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
  &&  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> o9_pre)
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| ((c0y_pre + 6 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c0y_pre + 6 )) |]
.

Definition foo_safety_wit_4 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (o9_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
  &&  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> o9_pre)
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_5 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
  &&  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> (c0y_pre + 6 ))
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| ((c0y_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c0y_pre + 2 )) |]
.

Definition foo_safety_wit_6 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
  &&  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> (c0y_pre + 6 ))
  **  ((( &( "c0y" ) )) # Int  |-> c0y_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_7 := 
forall (pe_pre: Z) (rr_pre: Z) (c_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
  &&  ((( &( "pe" ) )) # Int  |-> pe_pre)
  **  ((( &( "rr" ) )) # Int  |-> rr_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "o9" ) )) # Int  |-> (c0y_pre + 6 ))
  **  ((( &( "c0y" ) )) # Int  |-> (c0y_pre + 2 ))
|--
  [| ((rr_pre + (c0y_pre + 6 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (rr_pre + (c0y_pre + 6 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (pe_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre > (pe_pre - 1 )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (pe_pre: Z) (c0y_pre: Z) ,
  [| (c0y_pre <= (pe_pre - 1 )) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.

End VC_Correct.
