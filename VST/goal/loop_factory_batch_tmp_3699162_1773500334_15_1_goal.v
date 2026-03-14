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
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> svq_pre)
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> b3_pre)
|--
  [| ((io_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (io_pre - 1 )) |]
.

Definition foo_safety_wit_2 := 
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> svq_pre)
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> b3_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  [| (b3_pre <= (io_pre - 1 )) |]
  &&  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> svq_pre)
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> b3_pre)
|--
  [| ((b3_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b3_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  [| (b3_pre <= (io_pre - 1 )) |]
  &&  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> svq_pre)
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> b3_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  [| (b3_pre <= (io_pre - 1 )) |]
  &&  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> svq_pre)
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> (b3_pre + 1 ))
|--
  [| ((svq_pre + r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (svq_pre + r_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (r_pre: Z) (io_pre: Z) (svq_pre: Z) (av_pre: Z) (k_pre: Z) (ls_pre: Z) (b3_pre: Z) ,
  [| (b3_pre <= (io_pre - 1 )) |]
  &&  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "io" ) )) # Int  |-> io_pre)
  **  ((( &( "svq" ) )) # Int  |-> (svq_pre + r_pre ))
  **  ((( &( "av" ) )) # Int  |-> av_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "ls" ) )) # Int  |-> ls_pre)
  **  ((( &( "b3" ) )) # Int  |-> (b3_pre + 1 ))
|--
  [| ((k_pre + (b3_pre + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k_pre + (b3_pre + 1 ) )) |]
.

Definition foo_return_wit_1_1 := 
forall (io_pre: Z) (b3_pre: Z) ,
  [| (b3_pre > (io_pre - 1 )) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (io_pre: Z) (b3_pre: Z) ,
  [| (b3_pre <= (io_pre - 1 )) |]
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
