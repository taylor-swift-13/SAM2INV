From  Require Import linear_142_goal linear_142_proof_auto linear_142_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_142_proof_auto.
  Include linear_142_proof_manual.
End VC_Correctness.
