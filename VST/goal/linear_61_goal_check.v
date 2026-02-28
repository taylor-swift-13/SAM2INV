From  Require Import linear_61_goal linear_61_proof_auto linear_61_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_61_proof_auto.
  Include linear_61_proof_manual.
End VC_Correctness.
