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
forall (v_pre: Z) (t1b_pre: Z) (go1m_pre: Z) (wb_pre: Z) (u5c_pre: Z) (j29_pre: Z) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "t1b" ) )) # Int  |-> t1b_pre)
  **  ((( &( "go1m" ) )) # Int  |-> go1m_pre)
  **  ((( &( "wb" ) )) # Int  |-> wb_pre)
  **  ((( &( "u5c" ) )) # Int  |-> u5c_pre)
  **  ((( &( "j29" ) )) # Int  |-> j29_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (v_pre: Z) (t1b_pre: Z) (go1m_pre: Z) (wb_pre: Z) (u5c_pre: Z) (j29_pre: Z) ,
  [| (j29_pre > 0) |]
  &&  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "t1b" ) )) # Int  |-> t1b_pre)
  **  ((( &( "go1m" ) )) # Int  |-> go1m_pre)
  **  ((( &( "wb" ) )) # Int  |-> wb_pre)
  **  ((( &( "u5c" ) )) # Int  |-> u5c_pre)
  **  ((( &( "j29" ) )) # Int  |-> j29_pre)
|--
  [| ((wb_pre + j29_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (wb_pre + j29_pre )) |]
.

Definition foo_safety_wit_3 := 
forall (v_pre: Z) (t1b_pre: Z) (go1m_pre: Z) (wb_pre: Z) (u5c_pre: Z) (j29_pre: Z) ,
  [| (j29_pre > 0) |]
  &&  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "t1b" ) )) # Int  |-> t1b_pre)
  **  ((( &( "go1m" ) )) # Int  |-> go1m_pre)
  **  ((( &( "wb" ) )) # Int  |-> (wb_pre + j29_pre ))
  **  ((( &( "u5c" ) )) # Int  |-> u5c_pre)
  **  ((( &( "j29" ) )) # Int  |-> j29_pre)
|--
  [| ((go1m_pre + (u5c_pre * j29_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go1m_pre + (u5c_pre * j29_pre ) )) |]
.

Definition foo_safety_wit_4 := 
forall (v_pre: Z) (t1b_pre: Z) (go1m_pre: Z) (wb_pre: Z) (u5c_pre: Z) (j29_pre: Z) ,
  [| (j29_pre > 0) |]
  &&  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "t1b" ) )) # Int  |-> t1b_pre)
  **  ((( &( "go1m" ) )) # Int  |-> go1m_pre)
  **  ((( &( "wb" ) )) # Int  |-> (wb_pre + j29_pre ))
  **  ((( &( "u5c" ) )) # Int  |-> u5c_pre)
  **  ((( &( "j29" ) )) # Int  |-> j29_pre)
|--
  [| ((u5c_pre * j29_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (u5c_pre * j29_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (v_pre: Z) (t1b_pre: Z) (go1m_pre: Z) (wb_pre: Z) (u5c_pre: Z) (j29_pre: Z) ,
  [| (j29_pre > 0) |]
  &&  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "t1b" ) )) # Int  |-> t1b_pre)
  **  ((( &( "go1m" ) )) # Int  |-> (go1m_pre + (u5c_pre * j29_pre ) ))
  **  ((( &( "wb" ) )) # Int  |-> (wb_pre + j29_pre ))
  **  ((( &( "u5c" ) )) # Int  |-> u5c_pre)
  **  ((( &( "j29" ) )) # Int  |-> j29_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_return_wit_1_1 := 
forall (j29_pre: Z) ,
  [| (j29_pre <= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (j29_pre: Z) ,
  [| (j29_pre > 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.

End VC_Correct.
