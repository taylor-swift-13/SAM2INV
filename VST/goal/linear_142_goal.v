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
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((v2_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v2_pre + 5 )) |]
.

Definition foo_safety_wit_2 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_3 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_4 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_5 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((x1_pre + v1_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x1_pre + v1_pre )) |]
.

Definition foo_safety_wit_6 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> x3_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((x3_pre + v3_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x3_pre + v3_pre )) |]
.

Definition foo_safety_wit_7 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((x2_pre + v2_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x2_pre + v2_pre )) |]
.

Definition foo_safety_wit_8 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) )) |]
.

Definition foo_safety_wit_9 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) )) |]
.

Definition foo_safety_wit_10 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (((x2_pre + v2_pre ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((x2_pre + v2_pre ) * 2 )) |]
.

Definition foo_safety_wit_11 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_12 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_13 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) >= 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((v2_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v2_pre - 1 )) |]
.

Definition foo_safety_wit_14 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) >= 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_15 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) )) |]
.

Definition foo_safety_wit_16 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) )) |]
.

Definition foo_safety_wit_17 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (((x2_pre + v2_pre ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((x2_pre + v2_pre ) * 2 )) |]
.

Definition foo_safety_wit_18 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_19 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_20 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) > 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| False |]
.

Definition foo_safety_wit_21 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((v2_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v2_pre + 1 )) |]
.

Definition foo_safety_wit_22 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> v2_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_23 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) >= 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> (v2_pre - 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((t_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 1 )) |]
.

Definition foo_safety_wit_24 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) >= 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> (v2_pre - 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_25 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> (v2_pre + 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| ((t_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (t_pre + 1 )) |]
.

Definition foo_safety_wit_26 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) (t_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  ((( &( "v1" ) )) # Int  |-> v1_pre)
  **  ((( &( "v2" ) )) # Int  |-> (v2_pre + 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "x1" ) )) # Int  |-> (x1_pre + v1_pre ))
  **  ((( &( "x2" ) )) # Int  |-> (x2_pre + v2_pre ))
  **  ((( &( "x3" ) )) # Int  |-> (x3_pre + v3_pre ))
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (v2_pre: Z) ,
  [| ((v2_pre + 5 ) < 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (v2_pre: Z) ,
  [| (v2_pre > 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) >= 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (v1_pre: Z) (v2_pre: Z) (v3_pre: Z) (x1_pre: Z) (x2_pre: Z) (x3_pre: Z) ,
  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) <= 0) |] 
  &&  [| (((((x2_pre + v2_pre ) * 2 ) - (x1_pre + v1_pre ) ) - (x3_pre + v3_pre ) ) < 0) |] 
  &&  [| (v2_pre <= 5) |] 
  &&  [| ((v2_pre + 5 ) >= 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.

End VC_Correct.
