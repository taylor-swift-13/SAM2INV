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
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_3 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((last_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (last_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((a_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre + 3 )) |]
.

Definition foo_safety_wit_6 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_7 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 3 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((b_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + 3 )) |]
.

Definition foo_safety_wit_8 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 3 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_9 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((a_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre + 2 )) |]
.

Definition foo_safety_wit_10 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_11 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((a_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a_pre + 2 )) |]
.

Definition foo_safety_wit_12 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_13 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((b_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + 2 )) |]
.

Definition foo_safety_wit_14 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_15 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| ((b_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre + 2 )) |]
.

Definition foo_safety_wit_16 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_17 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = last_pre) |] 
  &&  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 3 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 3 ))
|--
  [| False |]
.

Definition foo_safety_wit_18 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_19 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre <> 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| False |]
.

Definition foo_safety_wit_20 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (c_pre = last_pre) |] 
  &&  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_21 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (st_pre <> 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| False |]
.

Definition foo_safety_wit_22 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| (((a_pre + 2 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre + 2 ) + 1 )) |]
.

Definition foo_safety_wit_23 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> (a_pre + 2 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_24 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> ((a_pre + 2 ) + 1 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| ((c_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c_pre + 1 )) |]
.

Definition foo_safety_wit_25 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) (a_pre: Z) (b_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "last" ) )) # Int  |-> last_pre)
  **  ((( &( "st" ) )) # Int  |-> st_pre)
  **  ((( &( "a" ) )) # Int  |-> ((a_pre + 2 ) + 1 ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre + 2 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) ,
  [| (c_pre <> last_pre) |] 
  &&  [| (st_pre <> 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) ,
  [| (st_pre <> 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (st_pre <> 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) ,
  [| (c_pre <> last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) ,
  [| (c_pre <> last_pre) |] 
  &&  [| (c_pre = (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (c_pre: Z) (last_pre: Z) (st_pre: Z) ,
  [| (st_pre = 0) |] 
  &&  [| (c_pre = last_pre) |] 
  &&  [| (c_pre <> (last_pre + 1 )) |] 
  &&  [| (st_pre = 0) |]
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
Axiom proof_of_foo_safety_wit_19 : foo_safety_wit_19.
Axiom proof_of_foo_safety_wit_20 : foo_safety_wit_20.
Axiom proof_of_foo_safety_wit_21 : foo_safety_wit_21.
Axiom proof_of_foo_safety_wit_22 : foo_safety_wit_22.
Axiom proof_of_foo_safety_wit_23 : foo_safety_wit_23.
Axiom proof_of_foo_safety_wit_24 : foo_safety_wit_24.
Axiom proof_of_foo_safety_wit_25 : foo_safety_wit_25.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.

End VC_Correct.
