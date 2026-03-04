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
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((i_pre - 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i_pre - 3 )) |]
.

Definition foo_safety_wit_2 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_3 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_4 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_6 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_7 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_8 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 2)
|--
  [| ((2 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 + 1 )) |]
.

Definition foo_safety_wit_9 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 2)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_10 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 1)
|--
  [| ((1 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 + 1 )) |]
.

Definition foo_safety_wit_11 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 1)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_12 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre <> 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((q_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_pre + 1 )) |]
.

Definition foo_safety_wit_13 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| (q_pre <> 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_14 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((2 + 1 ) < y_pre) |] 
  &&  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 2)
|--
  [| ((2 + i_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 + i_pre )) |]
.

Definition foo_safety_wit_15 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((1 + 1 ) < y_pre) |] 
  &&  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> 1)
|--
  [| ((1 + i_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 + i_pre )) |]
.

Definition foo_safety_wit_16 := 
forall (a_pre: Z) (b_pre: Z) (m_pre: Z) (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((q_pre + 1 ) < y_pre) |] 
  &&  [| (q_pre <> 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((q_pre + i_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_pre + i_pre )) |]
.

Definition foo_return_wit_1_1 := 
forall (i_pre: Z) ,
  [| ((i_pre - 3 ) < 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((q_pre + 1 ) >= y_pre) |] 
  &&  [| (q_pre <> 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((1 + 1 ) >= y_pre) |] 
  &&  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((2 + 1 ) >= y_pre) |] 
  &&  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((2 + 1 ) < y_pre) |] 
  &&  [| (q_pre = 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_6 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((1 + 1 ) < y_pre) |] 
  &&  [| (q_pre = 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_7 := 
forall (y_pre: Z) (i_pre: Z) (q_pre: Z) ,
  [| ((q_pre + 1 ) < y_pre) |] 
  &&  [| (q_pre <> 2) |] 
  &&  [| (q_pre <> 1) |] 
  &&  [| ((i_pre - 3 ) >= 0) |]
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
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.
Axiom proof_of_foo_return_wit_1_6 : foo_return_wit_1_6.
Axiom proof_of_foo_return_wit_1_7 : foo_return_wit_1_7.

End VC_Correct.
