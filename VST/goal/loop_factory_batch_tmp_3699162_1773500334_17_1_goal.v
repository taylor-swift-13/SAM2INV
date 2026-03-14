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
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  ((( &( "pl" ) )) # Int  |-> pl_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| ((pa_pre + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pa_pre + 4 )) |]
.

Definition foo_safety_wit_2 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  ((( &( "pl" ) )) # Int  |-> pl_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_3 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> pl_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| ((ty_pre + pl_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ty_pre + pl_pre )) |]
.

Definition foo_safety_wit_4 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> pl_pre)
  **  ((( &( "ty" ) )) # Int  |-> (ty_pre + pl_pre ))
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| ((pl_pre + (ty_pre + pl_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pl_pre + (ty_pre + pl_pre ) )) |]
.

Definition foo_safety_wit_5 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> (pl_pre + (ty_pre + pl_pre ) ))
  **  ((( &( "ty" ) )) # Int  |-> (ty_pre + pl_pre ))
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| (((pa_pre + 4 ) - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((pa_pre + 4 ) - 1 )) |]
.

Definition foo_safety_wit_6 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> (pl_pre + (ty_pre + pl_pre ) ))
  **  ((( &( "ty" ) )) # Int  |-> (ty_pre + pl_pre ))
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| ((pa_pre + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pa_pre + 4 )) |]
.

Definition foo_safety_wit_7 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> (pl_pre + (ty_pre + pl_pre ) ))
  **  ((( &( "ty" ) )) # Int  |-> (ty_pre + pl_pre ))
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition foo_safety_wit_8 := 
forall (pl_pre: Z) (ty_pre: Z) (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
  &&  ((( &( "pl" ) )) # Int  |-> (pl_pre + (ty_pre + pl_pre ) ))
  **  ((( &( "ty" ) )) # Int  |-> (ty_pre + pl_pre ))
  **  ((( &( "ja" ) )) # Int  |-> ja_pre)
  **  ((( &( "pa" ) )) # Int  |-> pa_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_return_wit_1_1 := 
forall (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) > ja_pre) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (ja_pre: Z) (pa_pre: Z) ,
  [| ((pa_pre + 4 ) <= ja_pre) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.

End VC_Correct.
