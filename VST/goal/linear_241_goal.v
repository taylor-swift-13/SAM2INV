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
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> term_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> term_pre)
|--
  [| ((term_pre * (x_pre ÷ count_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (term_pre * (x_pre ÷ count_pre ) )) |]
.

Definition foo_safety_wit_3 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> term_pre)
|--
  [| ((x_pre <> (INT_MIN)) \/ (count_pre <> (-1))) |] 
  &&  [| (count_pre <> 0) |]
.

Definition foo_safety_wit_4 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (((count_pre ÷ 2 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_5 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((count_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_6 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_7 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_8 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_9 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_10 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (1 <> (INT_MIN)) |]
.

Definition foo_safety_wit_11 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (multFactor_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> multFactor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_12 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) )) |]
.

Definition foo_safety_wit_13 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((1 * (term_pre * (x_pre ÷ count_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * (term_pre * (x_pre ÷ count_pre ) ) )) |]
.

Definition foo_safety_wit_14 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) )) |]
.

Definition foo_safety_wit_15 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> evenExp_pre)
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((-1) * (term_pre * (x_pre ÷ count_pre ) ) )) |]
.

Definition foo_safety_wit_16 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((count_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count_pre + 1 )) |]
.

Definition foo_safety_wit_17 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_18 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((count_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count_pre + 1 )) |]
.

Definition foo_safety_wit_19 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_20 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) )) |]
.

Definition foo_safety_wit_21 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((x_pre <> (INT_MIN)) \/ ((count_pre + 1 ) <> (-1))) |] 
  &&  [| ((count_pre + 1 ) <> 0) |]
.

Definition foo_safety_wit_22 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| (((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) )) |]
.

Definition foo_safety_wit_23 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> (term_pre * (x_pre ÷ count_pre ) ))
|--
  [| ((x_pre <> (INT_MIN)) \/ ((count_pre + 1 ) <> (-1))) |] 
  &&  [| ((count_pre + 1 ) <> 0) |]
.

Definition foo_safety_wit_24 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| ((oddExp_pre + ((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (oddExp_pre + ((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) )) |]
.

Definition foo_safety_wit_25 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| (((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) )) |]
.

Definition foo_safety_wit_26 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| ((oddExp_pre + (1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (oddExp_pre + (1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) )) |]
.

Definition foo_safety_wit_27 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> oddExp_pre)
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| ((1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) )) |]
.

Definition foo_safety_wit_28 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> (oddExp_pre + (1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ))
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| (((count_pre + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((count_pre + 1 ) + 1 )) |]
.

Definition foo_safety_wit_29 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> (oddExp_pre + (1 * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ))
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + (1 * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_30 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> (oddExp_pre + ((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ))
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| (((count_pre + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((count_pre + 1 ) + 1 )) |]
.

Definition foo_safety_wit_31 := 
forall (oddExp_pre: Z) (evenExp_pre: Z) (count_pre: Z) (x_pre: Z) (term_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
  &&  ((( &( "oddExp" ) )) # Int  |-> (oddExp_pre + ((-1) * ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ) ) ))
  **  ((( &( "evenExp" ) )) # Int  |-> (evenExp_pre + ((-1) * (term_pre * (x_pre ÷ count_pre ) ) ) ))
  **  ((( &( "multFactor" ) )) # Int  |-> (-1))
  **  ((( &( "count" ) )) # Int  |-> (count_pre + 1 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "term" ) )) # Int  |-> ((term_pre * (x_pre ÷ count_pre ) ) * (x_pre ÷ (count_pre + 1 ) ) ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (count_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) = 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (count_pre: Z) ,
  [| (((count_pre ÷ 2 ) % ( 2 ) ) <> 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.

End VC_Correct.
