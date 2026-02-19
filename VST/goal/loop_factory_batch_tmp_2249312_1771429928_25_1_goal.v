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
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((v_pre * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre * 4 )) |]
.

Definition foo_safety_wit_2 := 
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_3 := 
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 4 ))
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition foo_safety_wit_4 := 
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 4 ))
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_5 := 
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 4 ))
  **  ((( &( "a" ) )) # Int  |-> (a_pre ÷ 4 ))
|--
  [| ((((v_pre * 4 ) + (a_pre ÷ 4 ) ) + (a_pre ÷ 4 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((v_pre * 4 ) + (a_pre ÷ 4 ) ) + (a_pre ÷ 4 ) )) |]
.

Definition foo_safety_wit_6 := 
forall (n_pre: Z) (p_pre: Z) (l_pre: Z) (i_pre: Z) (v_pre: Z) (a_pre: Z) ,
  [| (i_pre < l_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * 4 ))
  **  ((( &( "a" ) )) # Int  |-> (a_pre ÷ 4 ))
|--
  [| (((v_pre * 4 ) + (a_pre ÷ 4 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((v_pre * 4 ) + (a_pre ÷ 4 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (l_pre: Z) (i_pre: Z) ,
  [| (i_pre >= l_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (l_pre: Z) (i_pre: Z) ,
  [| (i_pre < l_pre) |]
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

End VC_Correct.
