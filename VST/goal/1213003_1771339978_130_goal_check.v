From  Require Import 1213003_1771339978_130_goal 1213003_1771339978_130_proof_auto 1213003_1771339978_130_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 1213003_1771339978_130_proof_auto.
  Include 1213003_1771339978_130_proof_manual.
End VC_Correctness.
