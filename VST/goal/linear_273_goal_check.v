From  Require Import linear_273_goal linear_273_proof_auto linear_273_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_273_proof_auto.
  Include linear_273_proof_manual.
End VC_Correctness.
