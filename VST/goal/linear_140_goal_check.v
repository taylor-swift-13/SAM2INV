From  Require Import linear_140_goal linear_140_proof_auto linear_140_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_140_proof_auto.
  Include linear_140_proof_manual.
End VC_Correctness.
