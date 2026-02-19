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
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_3 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_5 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 )) |]
.

Definition foo_safety_wit_6 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre )) |]
.

Definition foo_safety_wit_7 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((2 * r_pre ) - k_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * r_pre ) - k_pre ) + q_pre )) |]
.

Definition foo_safety_wit_8 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) - k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) - k_pre )) |]
.

Definition foo_safety_wit_9 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_10 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_11 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_12 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((q_pre + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_pre + 4 )) |]
.

Definition foo_safety_wit_13 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_14 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre + 4 ))
|--
  [| ((d_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + 2 )) |]
.

Definition foo_safety_wit_15 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) + d_pre ) + 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre + 4 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_16 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_17 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_18 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_19 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| False |]
.

Definition foo_safety_wit_20 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_21 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_22 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_23 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((d_pre + k_pre ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((d_pre + k_pre ) + 2 )) |]
.

Definition foo_safety_wit_24 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((d_pre + k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + k_pre )) |]
.

Definition foo_safety_wit_25 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_26 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((2 * r_pre ) - k_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * r_pre ) - k_pre ) + q_pre )) |]
.

Definition foo_safety_wit_27 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) - k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) - k_pre )) |]
.

Definition foo_safety_wit_28 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_29 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_30 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((2 * r_pre ) - k_pre ) + q_pre ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((d_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + 2 )) |]
.

Definition foo_safety_wit_31 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((2 * r_pre ) - k_pre ) + q_pre ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_32 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_33 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_34 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_35 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| False |]
.

Definition foo_safety_wit_36 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_37 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_38 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_39 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((d_pre + k_pre ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((d_pre + k_pre ) + 2 )) |]
.

Definition foo_safety_wit_40 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((d_pre + k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + k_pre )) |]
.

Definition foo_safety_wit_41 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_42 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| False |]
.

Definition foo_safety_wit_43 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) + q_pre )) |]
.

Definition foo_safety_wit_44 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_45 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_46 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((2 * d_pre ) + k_pre ) + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * d_pre ) + k_pre ) + 4 )) |]
.

Definition foo_safety_wit_47 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * d_pre ) + k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * d_pre ) + k_pre )) |]
.

Definition foo_safety_wit_48 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * d_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * d_pre )) |]
.

Definition foo_safety_wit_49 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_50 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (t_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_51 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 )) |]
.

Definition foo_safety_wit_52 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre )) |]
.

Definition foo_safety_wit_53 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((2 * r_pre ) - k_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * r_pre ) - k_pre ) + q_pre )) |]
.

Definition foo_safety_wit_54 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) - k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) - k_pre )) |]
.

Definition foo_safety_wit_55 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_56 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_57 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_58 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((q_pre - 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_pre - 4 )) |]
.

Definition foo_safety_wit_59 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_60 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre - 4 ))
|--
  [| ((d_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + 2 )) |]
.

Definition foo_safety_wit_61 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - d_pre ) - 2 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre - 4 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_62 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 )) |]
.

Definition foo_safety_wit_63 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) )) |]
.

Definition foo_safety_wit_64 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((((2 * r_pre ) - k_pre ) + q_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * r_pre ) - k_pre ) + q_pre )) |]
.

Definition foo_safety_wit_65 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (((2 * r_pre ) - k_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * r_pre ) - k_pre )) |]
.

Definition foo_safety_wit_66 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * r_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * r_pre )) |]
.

Definition foo_safety_wit_67 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_68 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((2 * d_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * d_pre )) |]
.

Definition foo_safety_wit_69 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_70 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_71 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| ((q_pre - 8 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_pre - 8 )) |]
.

Definition foo_safety_wit_72 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_73 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre - 8 ))
|--
  [| ((d_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d_pre + 2 )) |]
.

Definition foo_safety_wit_74 := 
forall (a_pre: Z) (s_pre: Z) (n_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "r" ) )) # Int  |-> (((((2 * r_pre ) - k_pre ) + q_pre ) - (2 * d_pre ) ) - 4 ))
  **  ((( &( "t" ) )) # Int  |-> r_pre)
  **  ((( &( "k" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> (q_pre - 8 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_return_wit_1_1 := 
forall (s_pre: Z) (d_pre: Z) ,
  [| (s_pre < d_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (s_pre: Z) (d_pre: Z) (r_pre: Z) ,
  [| (r_pre = 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (s_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) >= (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (s_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < (((2 * d_pre ) + k_pre ) + 4 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (s_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < ((d_pre + k_pre ) + 2 )) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (((2 * r_pre ) + q_pre ) >= k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_6 := 
forall (s_pre: Z) (d_pre: Z) (r_pre: Z) (k_pre: Z) (q_pre: Z) ,
  [| (((2 * r_pre ) + q_pre ) < k_pre) |] 
  &&  [| (r_pre <> 0) |] 
  &&  [| (s_pre >= d_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.
Axiom proof_of_foo_return_wit_1_6 : foo_return_wit_1_6.

End VC_Correct.
