From  Require Import linear_250_goal linear_250_proof_auto linear_250_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_250_proof_auto.
  Include linear_250_proof_manual.
End VC_Correctness.
