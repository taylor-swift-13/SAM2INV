From  Require Import linear_287_goal linear_287_proof_auto linear_287_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_287_proof_auto.
  Include linear_287_proof_manual.
End VC_Correctness.
