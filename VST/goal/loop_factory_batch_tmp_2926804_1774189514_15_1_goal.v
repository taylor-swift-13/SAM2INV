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
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> k7x_pre)
  **  ((( &( "tc" ) )) # Int  |-> tc_pre)
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> k7x_pre)
  **  ((( &( "tc" ) )) # Int  |-> tc_pre)
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((tc_pre + (c_pre * c_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (tc_pre + (c_pre * c_pre ) )) |]
.

Definition foo_safety_wit_3 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> k7x_pre)
  **  ((( &( "tc" ) )) # Int  |-> tc_pre)
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((c_pre * c_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c_pre * c_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> k7x_pre)
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((k7x_pre + (p_pre * p_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k7x_pre + (p_pre * p_pre ) )) |]
.

Definition foo_safety_wit_5 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> k7x_pre)
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((p_pre * p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * p_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((b_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b_pre - 1 )) |]
.

Definition foo_safety_wit_7 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_8 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((b7_pre + (p_pre * c_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b7_pre + (p_pre * c_pre ) )) |]
.

Definition foo_safety_wit_9 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> b7_pre)
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((p_pre * c_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * c_pre )) |]
.

Definition foo_safety_wit_10 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((p_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre + 1 )) |]
.

Definition foo_safety_wit_11 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_12 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((p_pre * ebh_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * ebh_pre )) |]
.

Definition foo_safety_wit_13 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((c7_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c7_pre + 5 )) |]
.

Definition foo_safety_wit_14 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_15 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre + tcn2_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre + tcn2_pre )) |]
.

Definition foo_safety_wit_16 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((c7_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c7_pre + 5 )) |]
.

Definition foo_safety_wit_17 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_18 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre + tcn2_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre + tcn2_pre )) |]
.

Definition foo_safety_wit_19 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) )) |]
.

Definition foo_safety_wit_20 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre * ebh_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre * ebh_pre )) |]
.

Definition foo_safety_wit_21 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((ebh_pre * ebh_pre ) + p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((ebh_pre * ebh_pre ) + p_pre )) |]
.

Definition foo_safety_wit_22 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre * ebh_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre * ebh_pre )) |]
.

Definition foo_safety_wit_23 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_24 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) )) |]
.

Definition foo_safety_wit_25 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| ((gpb_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (gpb_pre * 3 )) |]
.

Definition foo_safety_wit_26 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_27 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (((tc_pre + (c_pre * c_pre ) ) <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_28 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_29 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_30 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_31 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) )) |]
.

Definition foo_safety_wit_32 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| ((gpb_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (gpb_pre * 3 )) |]
.

Definition foo_safety_wit_33 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_34 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (((tc_pre + (c_pre * c_pre ) ) <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_35 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_36 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_37 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_38 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) )) |]
.

Definition foo_safety_wit_39 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((gpb_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (gpb_pre * 3 )) |]
.

Definition foo_safety_wit_40 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_41 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((tc_pre + (c_pre * c_pre ) ) <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_42 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_43 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_44 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 )) |]
.

Definition foo_safety_wit_45 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) )) |]
.

Definition foo_safety_wit_46 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((gpb_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (gpb_pre * 3 )) |]
.

Definition foo_safety_wit_47 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_48 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((tc_pre + (c_pre * c_pre ) ) <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_49 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_50 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> gpb_pre)
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_51 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 )) |]
.

Definition foo_safety_wit_52 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 )) |]
.

Definition foo_safety_wit_53 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_54 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_55 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 )) |]
.

Definition foo_safety_wit_56 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 )) |]
.

Definition foo_safety_wit_57 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_58 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_59 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| ((((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 )) |]
.

Definition foo_safety_wit_60 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 )) |]
.

Definition foo_safety_wit_61 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_62 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_63 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| ((((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 )) |]
.

Definition foo_safety_wit_64 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 )) |]
.

Definition foo_safety_wit_65 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_66 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_67 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (((((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 )) |]
.

Definition foo_safety_wit_68 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| ((((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_69 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + p_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_70 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (((((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 )) |]
.

Definition foo_safety_wit_71 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| ((((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_72 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_73 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 )) |]
.

Definition foo_safety_wit_74 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_75 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_76 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 )) |]
.

Definition foo_safety_wit_77 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_78 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ebh_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_79 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| (((p_pre * p_pre ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p_pre * p_pre ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_80 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| ((p_pre * p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * p_pre )) |]
.

Definition foo_safety_wit_81 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| ((((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_82 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((ebh_pre * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| (((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p_pre * ebh_pre ) * (p_pre * ebh_pre ) )) |]
.

Definition foo_safety_wit_83 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| ((((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_84 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> (p_pre * ebh_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((((ebh_pre * ebh_pre ) + (p_pre * ebh_pre ) ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| (((p_pre * ebh_pre ) * (p_pre * ebh_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p_pre * ebh_pre ) * (p_pre * ebh_pre ) )) |]
.

Definition foo_safety_wit_85 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| (((p_pre * p_pre ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((p_pre * p_pre ) + (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) )) |]
.

Definition foo_safety_wit_86 := 
forall (p_pre: Z) (c_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (k7x_pre: Z) (tc_pre: Z) (b7_pre: Z) (b_pre: Z) (gpb_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "tcn2" ) )) # Int  |-> tcn2_pre)
  **  ((( &( "c7" ) )) # Int  |-> c7_pre)
  **  ((( &( "k7x" ) )) # Int  |-> (k7x_pre + (p_pre * p_pre ) ))
  **  ((( &( "tc" ) )) # Int  |-> (tc_pre + (c_pre * c_pre ) ))
  **  ((( &( "b7" ) )) # Int  |-> (b7_pre + (p_pre * c_pre ) ))
  **  ((( &( "b" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "gpb" ) )) # Int  |-> (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ))
  **  ((( &( "ebh" ) )) # Int  |-> ((((ebh_pre * ebh_pre ) + p_pre ) * (((((gpb_pre * 3 ) + ((tc_pre + (c_pre * c_pre ) ) % ( 6 ) ) ) + 0 ) * 4 ) + 2 ) ) + 2 ))
|--
  [| ((p_pre * p_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p_pre * p_pre )) |]
.

Definition foo_return_wit_1_1 := 
forall (b_pre: Z) ,
  [| (b_pre < 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (p_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (b_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (p_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (b_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) > (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (p_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (b_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) < tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (p_pre: Z) (tcn2_pre: Z) (c7_pre: Z) (b_pre: Z) (ebh_pre: Z) ,
  [| ((c7_pre + 5 ) <= (ebh_pre + tcn2_pre )) |] 
  &&  [| ((p_pre + 1 ) >= tcn2_pre) |] 
  &&  [| (b_pre >= 1) |]
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
Axiom proof_of_foo_safety_wit_26 : foo_safety_wit_26.
Axiom proof_of_foo_safety_wit_27 : foo_safety_wit_27.
Axiom proof_of_foo_safety_wit_28 : foo_safety_wit_28.
Axiom proof_of_foo_safety_wit_29 : foo_safety_wit_29.
Axiom proof_of_foo_safety_wit_30 : foo_safety_wit_30.
Axiom proof_of_foo_safety_wit_31 : foo_safety_wit_31.
Axiom proof_of_foo_safety_wit_32 : foo_safety_wit_32.
Axiom proof_of_foo_safety_wit_33 : foo_safety_wit_33.
Axiom proof_of_foo_safety_wit_34 : foo_safety_wit_34.
Axiom proof_of_foo_safety_wit_35 : foo_safety_wit_35.
Axiom proof_of_foo_safety_wit_36 : foo_safety_wit_36.
Axiom proof_of_foo_safety_wit_37 : foo_safety_wit_37.
Axiom proof_of_foo_safety_wit_38 : foo_safety_wit_38.
Axiom proof_of_foo_safety_wit_39 : foo_safety_wit_39.
Axiom proof_of_foo_safety_wit_40 : foo_safety_wit_40.
Axiom proof_of_foo_safety_wit_41 : foo_safety_wit_41.
Axiom proof_of_foo_safety_wit_42 : foo_safety_wit_42.
Axiom proof_of_foo_safety_wit_43 : foo_safety_wit_43.
Axiom proof_of_foo_safety_wit_44 : foo_safety_wit_44.
Axiom proof_of_foo_safety_wit_45 : foo_safety_wit_45.
Axiom proof_of_foo_safety_wit_46 : foo_safety_wit_46.
Axiom proof_of_foo_safety_wit_47 : foo_safety_wit_47.
Axiom proof_of_foo_safety_wit_48 : foo_safety_wit_48.
Axiom proof_of_foo_safety_wit_49 : foo_safety_wit_49.
Axiom proof_of_foo_safety_wit_50 : foo_safety_wit_50.
Axiom proof_of_foo_safety_wit_51 : foo_safety_wit_51.
Axiom proof_of_foo_safety_wit_52 : foo_safety_wit_52.
Axiom proof_of_foo_safety_wit_53 : foo_safety_wit_53.
Axiom proof_of_foo_safety_wit_54 : foo_safety_wit_54.
Axiom proof_of_foo_safety_wit_55 : foo_safety_wit_55.
Axiom proof_of_foo_safety_wit_56 : foo_safety_wit_56.
Axiom proof_of_foo_safety_wit_57 : foo_safety_wit_57.
Axiom proof_of_foo_safety_wit_58 : foo_safety_wit_58.
Axiom proof_of_foo_safety_wit_59 : foo_safety_wit_59.
Axiom proof_of_foo_safety_wit_60 : foo_safety_wit_60.
Axiom proof_of_foo_safety_wit_61 : foo_safety_wit_61.
Axiom proof_of_foo_safety_wit_62 : foo_safety_wit_62.
Axiom proof_of_foo_safety_wit_63 : foo_safety_wit_63.
Axiom proof_of_foo_safety_wit_64 : foo_safety_wit_64.
Axiom proof_of_foo_safety_wit_65 : foo_safety_wit_65.
Axiom proof_of_foo_safety_wit_66 : foo_safety_wit_66.
Axiom proof_of_foo_safety_wit_67 : foo_safety_wit_67.
Axiom proof_of_foo_safety_wit_68 : foo_safety_wit_68.
Axiom proof_of_foo_safety_wit_69 : foo_safety_wit_69.
Axiom proof_of_foo_safety_wit_70 : foo_safety_wit_70.
Axiom proof_of_foo_safety_wit_71 : foo_safety_wit_71.
Axiom proof_of_foo_safety_wit_72 : foo_safety_wit_72.
Axiom proof_of_foo_safety_wit_73 : foo_safety_wit_73.
Axiom proof_of_foo_safety_wit_74 : foo_safety_wit_74.
Axiom proof_of_foo_safety_wit_75 : foo_safety_wit_75.
Axiom proof_of_foo_safety_wit_76 : foo_safety_wit_76.
Axiom proof_of_foo_safety_wit_77 : foo_safety_wit_77.
Axiom proof_of_foo_safety_wit_78 : foo_safety_wit_78.
Axiom proof_of_foo_safety_wit_79 : foo_safety_wit_79.
Axiom proof_of_foo_safety_wit_80 : foo_safety_wit_80.
Axiom proof_of_foo_safety_wit_81 : foo_safety_wit_81.
Axiom proof_of_foo_safety_wit_82 : foo_safety_wit_82.
Axiom proof_of_foo_safety_wit_83 : foo_safety_wit_83.
Axiom proof_of_foo_safety_wit_84 : foo_safety_wit_84.
Axiom proof_of_foo_safety_wit_85 : foo_safety_wit_85.
Axiom proof_of_foo_safety_wit_86 : foo_safety_wit_86.
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.

End VC_Correct.
