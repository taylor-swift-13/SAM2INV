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
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((v_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre + 3 )) |]
.

Definition foo_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) < l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((v_pre * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre * 2 )) |]
.

Definition foo_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) < l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) >= l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((v_pre * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre * 2 )) |]
.

Definition foo_safety_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) >= l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_8 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) < l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 2 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_9 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) < l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 2 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_10 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) >= l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 2 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_11 := 
forall (b_pre: Z) (n_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) >= l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 2 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_return_wit_1_1 := 
forall (i_pre: Z) ,
  [| (i_pre <= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) < l_pre) |] 
  &&  [| (i_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (l_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((v_pre + 3 ) >= l_pre) |] 
  &&  [| (i_pre > 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
