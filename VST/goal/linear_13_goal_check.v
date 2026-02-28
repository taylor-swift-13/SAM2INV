From  Require Import linear_13_goal linear_13_proof_auto linear_13_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_13_proof_auto.
  Include linear_13_proof_manual.
End VC_Correctness.
