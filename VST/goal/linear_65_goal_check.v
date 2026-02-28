From  Require Import linear_65_goal linear_65_proof_auto linear_65_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_65_proof_auto.
  Include linear_65_proof_manual.
End VC_Correctness.
