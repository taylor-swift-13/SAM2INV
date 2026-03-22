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
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> z1_pre)
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_2 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> z1_pre)
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> o_pre)
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((o_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (o_pre - 1 )) |]
.

Definition foo_safety_wit_3 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> z1_pre)
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((z1_pre + (g_pre * g_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (z1_pre + (g_pre * g_pre ) )) |]
.

Definition foo_safety_wit_4 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> z1_pre)
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g_pre * g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre * g_pre )) |]
.

Definition foo_safety_wit_5 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((nx27_pre + (g_pre * g_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (nx27_pre + (g_pre * g_pre ) )) |]
.

Definition foo_safety_wit_6 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> nx27_pre)
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g_pre * g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre * g_pre )) |]
.

Definition foo_safety_wit_7 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g0_pre + (g_pre * g_pre ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g0_pre + (g_pre * g_pre ) )) |]
.

Definition foo_safety_wit_8 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> g0_pre)
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g_pre * g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre * g_pre )) |]
.

Definition foo_safety_wit_9 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((e3g_pre <> (INT_MIN)) \/ (7 <> (-1))) |] 
  &&  [| (7 <> 0) |]
.

Definition foo_safety_wit_10 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition foo_safety_wit_11 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition foo_safety_wit_12 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((m9it_pre * hs0_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m9it_pre * hs0_pre )) |]
.

Definition foo_safety_wit_13 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((go_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre + 5 )) |]
.

Definition foo_safety_wit_14 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_15 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((go_pre + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre + 5 )) |]
.

Definition foo_safety_wit_16 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_17 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((go_pre * g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre * g_pre )) |]
.

Definition foo_safety_wit_18 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((go_pre * g_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre * g_pre )) |]
.

Definition foo_safety_wit_19 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((((go_pre * g_pre ) * 3 ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((go_pre * g_pre ) * 3 ) + 5 )) |]
.

Definition foo_safety_wit_20 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (((go_pre * g_pre ) * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((go_pre * g_pre ) * 3 )) |]
.

Definition foo_safety_wit_21 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_22 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_23 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((((go_pre * g_pre ) * 3 ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((go_pre * g_pre ) * 3 ) + 5 )) |]
.

Definition foo_safety_wit_24 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (((go_pre * g_pre ) * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((go_pre * g_pre ) * 3 )) |]
.

Definition foo_safety_wit_25 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_26 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (go_pre * g_pre ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_27 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (((go_pre * 3 ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((go_pre * 3 ) + 5 )) |]
.

Definition foo_safety_wit_28 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((go_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre * 3 )) |]
.

Definition foo_safety_wit_29 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_30 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_31 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (((go_pre * 3 ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((go_pre * 3 ) + 5 )) |]
.

Definition foo_safety_wit_32 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((go_pre * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (go_pre * 3 )) |]
.

Definition foo_safety_wit_33 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition foo_safety_wit_34 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> go_pre)
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_35 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g_pre + (z1_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (z1_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_36 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((g_pre + (z1_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (z1_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_37 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((g_pre + (z1_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (z1_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_38 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> g_pre)
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((g_pre + (z1_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (g_pre + (z1_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_39 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_40 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_41 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_42 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> hs0_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) )) |]
.

Definition foo_safety_wit_43 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((r_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (r_pre + 1 )) |]
.

Definition foo_safety_wit_44 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_45 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((r_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (r_pre + 1 )) |]
.

Definition foo_safety_wit_46 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_47 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((r_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (r_pre + 1 )) |]
.

Definition foo_safety_wit_48 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_49 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((r_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (r_pre + 1 )) |]
.

Definition foo_safety_wit_50 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition foo_safety_wit_51 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) + 5 )) |]
.

Definition foo_safety_wit_52 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) )) |]
.

Definition foo_safety_wit_53 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_54 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) + 5 )) |]
.

Definition foo_safety_wit_55 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * (((go_pre * g_pre ) * 3 ) + 5 ) )) |]
.

Definition foo_safety_wit_56 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> (((go_pre * g_pre ) * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_57 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| ((((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) + 5 )) |]
.

Definition foo_safety_wit_58 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) )) |]
.

Definition foo_safety_wit_59 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> (m9it_pre * hs0_pre ))
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_safety_wit_60 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| ((((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) + 5 )) |]
.

Definition foo_safety_wit_61 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ) * ((go_pre * 3 ) + 5 ) )) |]
.

Definition foo_safety_wit_62 := 
forall (g_pre: Z) (nyw_pre: Z) (e3g_pre: Z) (g0_pre: Z) (z1_pre: Z) (nx27_pre: Z) (o_pre: Z) (go_pre: Z) (hs0_pre: Z) (r_pre: Z) (m9it_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  ((( &( "g" ) )) # Int  |-> (g_pre + (z1_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "nyw" ) )) # Int  |-> nyw_pre)
  **  ((( &( "e3g" ) )) # Int  |-> e3g_pre)
  **  ((( &( "g0" ) )) # Int  |-> (g0_pre + (g_pre * g_pre ) ))
  **  ((( &( "z1" ) )) # Int  |-> (z1_pre + (g_pre * g_pre ) ))
  **  ((( &( "nx27" ) )) # Int  |-> (nx27_pre + (g_pre * g_pre ) ))
  **  ((( &( "o" ) )) # Int  |-> (o_pre - 1 ))
  **  ((( &( "go" ) )) # Int  |-> ((go_pre * 3 ) + 5 ))
  **  ((( &( "hs0" ) )) # Int  |-> (hs0_pre + (nx27_pre + (g_pre * g_pre ) ) ))
  **  ((( &( "r" ) )) # Int  |-> (r_pre + 1 ))
  **  ((( &( "m9it" ) )) # Int  |-> m9it_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition foo_return_wit_1_1 := 
forall (o_pre: Z) ,
  [| (o_pre <= 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_2 := 
forall (nyw_pre: Z) (e3g_pre: Z) (o_pre: Z) (go_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_3 := 
forall (nyw_pre: Z) (e3g_pre: Z) (o_pre: Z) (go_pre: Z) ,
  [| ((go_pre + 5 ) < nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_4 := 
forall (nyw_pre: Z) (e3g_pre: Z) (o_pre: Z) (go_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) = 0) |] 
  &&  [| (o_pre > 0) |]
  &&  emp
|--
  TT && emp 
.

Definition foo_return_wit_1_5 := 
forall (nyw_pre: Z) (e3g_pre: Z) (o_pre: Z) (go_pre: Z) ,
  [| ((go_pre + 5 ) >= nyw_pre) |] 
  &&  [| ((e3g_pre % ( 7 ) ) <> 0) |] 
  &&  [| (o_pre > 0) |]
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
Axiom proof_of_foo_return_wit_1_1 : foo_return_wit_1_1.
Axiom proof_of_foo_return_wit_1_2 : foo_return_wit_1_2.
Axiom proof_of_foo_return_wit_1_3 : foo_return_wit_1_3.
Axiom proof_of_foo_return_wit_1_4 : foo_return_wit_1_4.
Axiom proof_of_foo_return_wit_1_5 : foo_return_wit_1_5.

End VC_Correct.
