From  Require Import linear_109_goal linear_109_proof_auto linear_109_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_109_proof_auto.
  Include linear_109_proof_manual.
End VC_Correctness.
