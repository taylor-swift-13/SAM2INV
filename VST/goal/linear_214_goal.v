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
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((nonexclusive_pre + unowned_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (nonexclusive_pre + unowned_pre )) |]
.

Definition foo_safety_wit_2 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_3 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_4 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (1 = 0) |] 
  &&  [| (invalid_pre >= 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_5 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (0 <> 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_6 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (0 <> 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_7 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_8 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_9 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_10 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_11 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((nonexclusive_pre + exclusive_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (nonexclusive_pre + exclusive_pre )) |]
.

Definition foo_safety_wit_12 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> (nonexclusive_pre + exclusive_pre ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_13 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> 0)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> (nonexclusive_pre + exclusive_pre ))
|--
  [| ((invalid_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (invalid_pre - 1 )) |]
.

Definition foo_safety_wit_14 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> 0)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> (nonexclusive_pre + exclusive_pre ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_15 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> 0)
  **  ((( &( "invalid" ) )) # Int  |-> (invalid_pre - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> (nonexclusive_pre + exclusive_pre ))
|--
  [| ((unowned_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (unowned_pre + 1 )) |]
.

Definition foo_safety_wit_16 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> 0)
  **  ((( &( "invalid" ) )) # Int  |-> (invalid_pre - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> (nonexclusive_pre + exclusive_pre ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_17 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((nonexclusive_pre + unowned_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (nonexclusive_pre + unowned_pre )) |]
.

Definition foo_safety_wit_18 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_19 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_20 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((nonexclusive_pre + unowned_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (nonexclusive_pre + unowned_pre )) |]
.

Definition foo_safety_wit_21 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_22 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) < 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| False |]
.

Definition foo_safety_wit_23 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 )) |]
.

Definition foo_safety_wit_24 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (((invalid_pre + unowned_pre ) + nonexclusive_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((invalid_pre + unowned_pre ) + nonexclusive_pre )) |]
.

Definition foo_safety_wit_25 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| ((invalid_pre + unowned_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (invalid_pre + unowned_pre )) |]
.

Definition foo_safety_wit_26 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> invalid_pre)
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_27 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> (((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> nonexclusive_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_28 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> (((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> 0)
|--
  [| ((exclusive_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (exclusive_pre + 1 )) |]
.

Definition foo_safety_wit_29 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> exclusive_pre)
  **  ((( &( "invalid" ) )) # Int  |-> (((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_30 := 
forall (exclusive_pre: Z) (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  ((( &( "exclusive" ) )) # Int  |-> (exclusive_pre + 1 ))
  **  ((( &( "invalid" ) )) # Int  |-> (((invalid_pre + unowned_pre ) + nonexclusive_pre ) - 1 ))
  **  ((( &( "unowned" ) )) # Int  |-> unowned_pre)
  **  ((( &( "nonexclusive" ) )) # Int  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_return_wit_1_1 := 
forall (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (1 <> 0) |] 
  &&  [| (invalid_pre >= 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) < 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| ((nonexclusive_pre + unowned_pre ) >= 1) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| (invalid_pre < 1) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) >= 1) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (invalid_pre: Z) (unowned_pre: Z) (nonexclusive_pre: Z) ,
  [| (invalid_pre >= 1) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((nonexclusive_pre + unowned_pre ) < 1) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.

End VC_Correct.
