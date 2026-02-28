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
forall (j_pre: Z) (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (j_pre: Z) (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition foo_safety_wit_3 := 
forall (j_pre: Z) (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  [| (c_pre > 48) |]
  &&  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| (57 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 57) |]
.

Definition foo_safety_wit_4 := 
forall (j_pre: Z) (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  [| (c_pre < 57) |] 
  &&  [| (c_pre > 48) |]
  &&  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| ((i_pre + i_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i_pre + i_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  [| (c_pre < 57) |] 
  &&  [| (c_pre > 48) |]
  &&  ((( &( "j" ) )) # Int  |-> (i_pre + i_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| ((c_pre - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c_pre - 48 )) |]
.

Definition foo_safety_wit_6 := 
forall (c_pre: Z) (t_pre: Z) (i_pre: Z) ,
  [| (c_pre < 57) |] 
  &&  [| (c_pre > 48) |]
  &&  ((( &( "j" ) )) # Int  |-> (i_pre + i_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition foo_safety_wit_7 := 
forall (c_pre: Z) (i_pre: Z) ,
  [| (c_pre < 57) |] 
  &&  [| (c_pre > 48) |]
  &&  ((( &( "j" ) )) # Int  |-> (i_pre + i_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> (c_pre - 48 ))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
|--
  [| (((i_pre + i_pre ) + (c_pre - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i_pre + i_pre ) + (c_pre - 48 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (c_pre: Z) ,
  [| (c_pre <= 48) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (c_pre: Z) ,
  [| (c_pre >= 57) |] 
  &&  [| (c_pre > 48) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (c_pre: Z) ,
  [| (c_pre < 57) |] 
  &&  [| (c_pre > 48) |]
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
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.

End VC_Correct.
