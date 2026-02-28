From  Require Import linear_28_goal linear_28_proof_auto linear_28_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_28_proof_auto.
  Include linear_28_proof_manual.
End VC_Correctness.
