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
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre <> (INT_MIN)) \/ (5 <> (-1))) |] 
  &&  [| (5 <> 0) |]
.

Definition foo_safety_wit_2 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_3 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_4 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) = 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((v3_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v3_pre + 1 )) |]
.

Definition foo_safety_wit_5 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) = 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_6 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre <> (INT_MIN)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition foo_safety_wit_7 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_8 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_9 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) = 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((v4_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v4_pre + 1 )) |]
.

Definition foo_safety_wit_10 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) = 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_11 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre <> (INT_MIN)) \/ (3 <> (-1))) |] 
  &&  [| (3 <> 0) |]
.

Definition foo_safety_wit_12 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_13 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_14 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) = 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((i_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i_pre + 1 )) |]
.

Definition foo_safety_wit_15 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) = 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_16 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition foo_safety_wit_17 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_18 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_19 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) = 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((j_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j_pre + 1 )) |]
.

Definition foo_safety_wit_20 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) = 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_21 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((k_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k_pre + 1 )) |]
.

Definition foo_safety_wit_22 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_23 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) = 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> (v3_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_pre + 1 )) |]
.

Definition foo_safety_wit_24 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) = 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> (v3_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_25 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) = 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> (v4_pre + 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_pre + 1 )) |]
.

Definition foo_safety_wit_26 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) = 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> (v4_pre + 1 ))
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_27 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) = 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_pre + 1 ))
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_pre + 1 )) |]
.

Definition foo_safety_wit_28 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) = 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_pre + 1 ))
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_29 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) = 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> (j_pre + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_pre + 1 )) |]
.

Definition foo_safety_wit_30 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) = 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "j" ) )) # Int  |-> (j_pre + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_31 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| ((l_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (l_pre + 1 )) |]
.

Definition foo_safety_wit_32 := 
forall (k_pre: Z) (j_pre: Z) (i_pre: Z) (v4_pre: Z) (v3_pre: Z) (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  ((( &( "k" ) )) # Int  |-> (k_pre + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v4" ) )) # Int  |-> v4_pre)
  **  ((( &( "v3" ) )) # Int  |-> v3_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| (l_pre >= n_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 5 ) ) = 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 4 ) ) = 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 3 ) ) = 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) = 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_6 := 
forall (n_pre: Z) (l_pre: Z) ,
  [| ((l_pre % ( 2 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 3 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 4 ) ) <> 0) |] 
  &&  [| ((l_pre % ( 5 ) ) <> 0) |] 
  &&  [| (l_pre < n_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.
Axiom proof_of_foo_return_wit_1_6 : foo_return_wit_1_6.

End VC_Correct.
