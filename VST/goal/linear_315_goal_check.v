From  Require Import linear_315_goal linear_315_proof_auto linear_315_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_315_proof_auto.
  Include linear_315_proof_manual.
End VC_Correctness.
