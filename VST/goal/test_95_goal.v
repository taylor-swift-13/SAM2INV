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
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| ((i_pre <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| ((i_pre <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((i_pre <> (INT_MIN)) \/ (6 <> (-1))) |] 
  &&  [| (6 <> 0) |]
.

Definition foo_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition foo_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| (((2 * 2 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * 2 ) + 2 )) |]
.

Definition foo_safety_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| ((2 * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * 2 )) |]
.

Definition foo_safety_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| (((1 * 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((1 * 1 ) + 1 )) |]
.

Definition foo_safety_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| ((1 * 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * 1 )) |]
.

Definition foo_safety_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| (((v_pre * v_pre ) + v_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((v_pre * v_pre ) + v_pre )) |]
.

Definition foo_safety_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((v_pre * v_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre * v_pre )) |]
.

Definition foo_safety_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 2)
|--
  [| ((2 * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * 2 )) |]
.

Definition foo_safety_wit_22 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> 1)
|--
  [| ((1 * 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * 1 )) |]
.

Definition foo_safety_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
|--
  [| ((v_pre * v_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v_pre * v_pre )) |]
.

Definition foo_safety_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((v_pre * v_pre ) + v_pre ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((v_pre * v_pre ) + v_pre ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((v_pre * v_pre ) + v_pre ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((1 * 1 ) + 1 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((1 * 1 ) + 1 ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((1 * 1 ) + 1 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((2 * 2 ) + 2 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((2 * 2 ) + 2 ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((2 * 2 ) + 2 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_33 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * v_pre ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_34 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * v_pre ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_35 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * v_pre ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_36 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (1 * 1 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_37 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (1 * 1 ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_38 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (1 * 1 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_39 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (2 * 2 ))
|--
  [| ((i_pre <> (INT_MIN)) \/ (8 <> (-1))) |] 
  &&  [| (8 <> 0) |]
.

Definition foo_safety_wit_40 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (2 * 2 ))
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition foo_safety_wit_41 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (2 * 2 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_42 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((v_pre * v_pre ) + v_pre ))
|--
  [| ((((v_pre * v_pre ) + v_pre ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((v_pre * v_pre ) + v_pre ) * 2 )) |]
.

Definition foo_safety_wit_43 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((v_pre * v_pre ) + v_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_44 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((1 * 1 ) + 1 ))
|--
  [| ((((1 * 1 ) + 1 ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((1 * 1 ) + 1 ) * 2 )) |]
.

Definition foo_safety_wit_45 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((1 * 1 ) + 1 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_46 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((2 * 2 ) + 2 ))
|--
  [| ((((2 * 2 ) + 2 ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((2 * 2 ) + 2 ) * 2 )) |]
.

Definition foo_safety_wit_47 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> ((2 * 2 ) + 2 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_48 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * v_pre ))
|--
  [| (((v_pre * v_pre ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((v_pre * v_pre ) * 2 )) |]
.

Definition foo_safety_wit_49 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (v_pre * v_pre ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_50 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (1 * 1 ))
|--
  [| (((1 * 1 ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((1 * 1 ) * 2 )) |]
.

Definition foo_safety_wit_51 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (1 * 1 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_safety_wit_52 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (2 * 2 ))
|--
  [| (((2 * 2 ) * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((2 * 2 ) * 2 )) |]
.

Definition foo_safety_wit_53 := 
forall (m_pre: Z) (n_pre: Z) (p_pre: Z) (k_pre: Z) (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "v" ) )) # Int  |-> (2 * 2 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition foo_return_wit_1_1 := 
forall (i_pre: Z) ,
  [| (i_pre < 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_6 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_7 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) <> 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_8 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_9 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_10 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) = 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_11 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre <> 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_12 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 2) |] 
  &&  [| (v_pre <> 1) |] 
  &&  [| (i_pre >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_13 := 
forall (i_pre: Z) (v_pre: Z) ,
  [| ((i_pre % ( 8 ) ) = 0) |] 
  &&  [| ((i_pre % ( 6 ) ) <> 0) |] 
  &&  [| (v_pre = 1) |] 
  &&  [| (i_pre >= 1) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.
Axiom proof_of_foo_return_wit_1_6 : foo_return_wit_1_6.
Axiom proof_of_foo_return_wit_1_7 : foo_return_wit_1_7.
Axiom proof_of_foo_return_wit_1_8 : foo_return_wit_1_8.
Axiom proof_of_foo_return_wit_1_9 : foo_return_wit_1_9.
Axiom proof_of_foo_return_wit_1_10 : foo_return_wit_1_10.
Axiom proof_of_foo_return_wit_1_11 : foo_return_wit_1_11.
Axiom proof_of_foo_return_wit_1_12 : foo_return_wit_1_12.
Axiom proof_of_foo_return_wit_1_13 : foo_return_wit_1_13.

End VC_Correct.
