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
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_3 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_4 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_5 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((y_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 2 )) |]
.

Definition foo_safety_wit_6 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_7 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((10 * w_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (10 * w_pre )) |]
.

Definition foo_safety_wit_8 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition foo_safety_wit_9 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((100 * x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (100 * x_pre )) |]
.

Definition foo_safety_wit_10 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition foo_safety_wit_11 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((0 - y_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 - y_pre )) |]
.

Definition foo_safety_wit_12 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_13 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_14 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_15 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition foo_safety_wit_16 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_17 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((y_pre + 100 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 100 )) |]
.

Definition foo_safety_wit_18 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition foo_safety_wit_19 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((y_pre + 100 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre + 100 )) |]
.

Definition foo_safety_wit_20 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition foo_safety_wit_21 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((w_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w_pre + 1 )) |]
.

Definition foo_safety_wit_22 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_23 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (0 - y_pre ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((w_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w_pre + 1 )) |]
.

Definition foo_safety_wit_24 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (0 - y_pre ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_25 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((w_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w_pre + 1 )) |]
.

Definition foo_safety_wit_26 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_27 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| ((w_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w_pre + 1 )) |]
.

Definition foo_safety_wit_28 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_29 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| ((z_pre + 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + 10 )) |]
.

Definition foo_safety_wit_30 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition foo_safety_wit_31 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| ((z_pre + 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + 10 )) |]
.

Definition foo_safety_wit_32 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 100 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition foo_safety_wit_33 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (0 - y_pre ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| ((z_pre + 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + 10 )) |]
.

Definition foo_safety_wit_34 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> (0 - y_pre ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition foo_safety_wit_35 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| ((z_pre + 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z_pre + 10 )) |]
.

Definition foo_safety_wit_36 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (x_pre >= 4) |]
  &&  ((( &( "x" ) )) # Int  |-> (x_pre + 1 ))
  **  ((( &( "y" ) )) # Int  |-> (y_pre + 2 ))
  **  ((( &( "z" ) )) # Int  |-> z_pre)
  **  ((( &( "w" ) )) # Int  |-> (w_pre + 1 ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition foo_return_wit_1_1 := 
forall (x_pre: Z) (y_pre: Z) (w_pre: Z) ,
  [| (y_pre <= (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre < (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (x_pre: Z) (y_pre: Z) (z_pre: Z) (w_pre: Z) ,
  [| (z_pre >= (100 * x_pre )) |] 
  &&  [| (y_pre > (10 * w_pre )) |] 
  &&  [| (x_pre < 4) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (x_pre: Z) ,
  [| (x_pre >= 4) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.

End VC_Correct.
