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
forall (sy_pre: Z) (bv_pre: Z) (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre < w_pre) |]
  &&  ((( &( "sy" ) )) # Int  |-> sy_pre)
  **  ((( &( "bv" ) )) # Int  |-> bv_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "s7k" ) )) # Int  |-> s7k_pre)
|--
  [| ((s7k_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s7k_pre + 1 )) |]
.

Definition foo_safety_wit_2 := 
forall (sy_pre: Z) (bv_pre: Z) (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre < w_pre) |]
  &&  ((( &( "sy" ) )) # Int  |-> sy_pre)
  **  ((( &( "bv" ) )) # Int  |-> bv_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "s7k" ) )) # Int  |-> (s7k_pre + 1 ))
|--
  [| ((bv_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bv_pre + 1 )) |]
.

Definition foo_safety_wit_3 := 
forall (sy_pre: Z) (bv_pre: Z) (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre < w_pre) |]
  &&  ((( &( "sy" ) )) # Int  |-> sy_pre)
  **  ((( &( "bv" ) )) # Int  |-> bv_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "s7k" ) )) # Int  |-> (s7k_pre + 1 ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_4 := 
forall (sy_pre: Z) (bv_pre: Z) (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre < w_pre) |]
  &&  ((( &( "sy" ) )) # Int  |-> sy_pre)
  **  ((( &( "bv" ) )) # Int  |-> (bv_pre + 1 ))
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "s7k" ) )) # Int  |-> (s7k_pre + 1 ))
|--
  [| ((sy_pre + (s7k_pre + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sy_pre + (s7k_pre + 1 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre >= w_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (w_pre: Z) (s7k_pre: Z) ,
  [| (s7k_pre < w_pre) |]
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

End VC_Correct.
