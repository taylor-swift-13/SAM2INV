From  Require Import linear_159_goal linear_159_proof_auto linear_159_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_159_proof_auto.
  Include linear_159_proof_manual.
End VC_Correctness.
