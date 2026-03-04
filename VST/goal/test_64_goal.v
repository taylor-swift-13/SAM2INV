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
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| (6 <> (INT_MIN)) |]
.

Definition foo_safety_wit_2 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_3 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| (((o_pre + s_pre ) + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((o_pre + s_pre ) + 3 )) |]
.

Definition foo_safety_wit_4 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| ((o_pre + s_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (o_pre + s_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_6 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> ((o_pre + s_pre ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| ((s_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s_pre + 3 )) |]
.

Definition foo_safety_wit_7 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> ((o_pre + s_pre ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> s_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_8 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> ((o_pre + s_pre ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> (s_pre + 3 ))
|--
  [| ((((o_pre + s_pre ) + 3 ) + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((o_pre + s_pre ) + 3 ) + 3 )) |]
.

Definition foo_safety_wit_9 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> ((o_pre + s_pre ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> (s_pre + 3 ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_10 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> (((o_pre + s_pre ) + 3 ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> (s_pre + 3 ))
|--
  [| (((s_pre + 3 ) + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((s_pre + 3 ) + 3 )) |]
.

Definition foo_safety_wit_11 := 
forall (b_pre: Z) (p_pre: Z) (q_pre: Z) (e_pre: Z) (m_pre: Z) (o_pre: Z) (s_pre: Z) ,
  [| (o_pre <= (-6)) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "o" ) )) # Int  |-> (((o_pre + s_pre ) + 3 ) + 3 ))
  **  ((( &( "s" ) )) # Int  |-> (s_pre + 3 ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_return_wit_1_1 := 
forall (o_pre: Z) ,
  [| (o_pre > (-6)) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (o_pre: Z) ,
  [| (o_pre <= (-6)) |]
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

End VC_Correct.
