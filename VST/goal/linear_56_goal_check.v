From  Require Import linear_56_goal linear_56_proof_auto linear_56_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_56_proof_auto.
  Include linear_56_proof_manual.
End VC_Correctness.
