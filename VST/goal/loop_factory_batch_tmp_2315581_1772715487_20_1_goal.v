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
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) (eb_pre: Z) ,
  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> eb_pre)
|--
  [| ((s5_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_2 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) (eb_pre: Z) ,
  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> eb_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_3 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| (((s5_pre - qxzq_pre ) <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_4 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((s5_pre - qxzq_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s5_pre - qxzq_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_6 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> ((s5_pre - qxzq_pre ) % ( 5 ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| (((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) - ((s5_pre - qxzq_pre ) % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) - ((s5_pre - qxzq_pre ) % ( 5 ) ) )) |]
.

Definition foo_safety_wit_7 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> ((s5_pre - qxzq_pre ) % ( 5 ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_8 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre < qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> qxzq_pre)
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((qxzq_pre + (s5_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (qxzq_pre + (s5_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_9 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> ((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) - ((s5_pre - qxzq_pre ) % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((s5_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s5_pre + 1 )) |]
.

Definition foo_safety_wit_10 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> ((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) - ((s5_pre - qxzq_pre ) % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_11 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre < qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> (qxzq_pre + (s5_pre % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((s5_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s5_pre + 1 )) |]
.

Definition foo_safety_wit_12 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre < qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> s5_pre)
  **  ((( &( "qxzq" ) )) # Int  |-> (qxzq_pre + (s5_pre % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_13 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre < qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> (s5_pre + 1 ))
  **  ((( &( "qxzq" ) )) # Int  |-> (qxzq_pre + (s5_pre % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((f_pre + (s5_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (f_pre + (s5_pre % ( 5 ) ) )) |]
.

Definition foo_safety_wit_14 := 
forall (f_pre: Z) (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  ((( &( "f" ) )) # Int  |-> f_pre)
  **  ((( &( "rz" ) )) # Int  |-> rz_pre)
  **  ((( &( "s5" ) )) # Int  |-> (s5_pre + 1 ))
  **  ((( &( "qxzq" ) )) # Int  |-> ((((s5_pre - qxzq_pre ) % ( 5 ) ) + (s5_pre % ( 5 ) ) ) - ((s5_pre - qxzq_pre ) % ( 5 ) ) ))
  **  ((( &( "eb" ) )) # Int  |-> (s5_pre % ( 5 ) ))
|--
  [| ((f_pre + (s5_pre % ( 5 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (f_pre + (s5_pre % ( 5 ) ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (rz_pre: Z) (s5_pre: Z) ,
  [| (s5_pre >= rz_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre < qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (rz_pre: Z) (s5_pre: Z) (qxzq_pre: Z) ,
  [| (s5_pre >= qxzq_pre) |] 
  &&  [| (s5_pre < rz_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
