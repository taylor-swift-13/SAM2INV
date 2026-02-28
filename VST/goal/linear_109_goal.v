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
forall (m_pre: Z) (j_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre < a_pre) |] 
  &&  [| (k_pre < c_pre) |]
  &&  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| ((k_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k_pre + 1 )) |]
.

Definition foo_safety_wit_2 := 
forall (m_pre: Z) (j_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre < a_pre) |] 
  &&  [| (k_pre < c_pre) |]
  &&  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (m_pre: Z) (j_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre >= a_pre) |] 
  &&  [| (k_pre < c_pre) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| ((k_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (m_pre: Z) (j_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre >= a_pre) |] 
  &&  [| (k_pre < c_pre) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (c_pre: Z) (k_pre: Z) ,
  [| (k_pre >= c_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (m_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre < a_pre) |] 
  &&  [| (k_pre < c_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (m_pre: Z) (a_pre: Z) (c_pre: Z) (k_pre: Z) ,
  [| (m_pre >= a_pre) |] 
  &&  [| (k_pre < c_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
