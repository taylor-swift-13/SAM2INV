From  Require Import linear_131_goal linear_131_proof_auto linear_131_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_131_proof_auto.
  Include linear_131_proof_manual.
End VC_Correctness.
