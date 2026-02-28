From  Require Import linear_99_goal linear_99_proof_auto linear_99_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_99_proof_auto.
  Include linear_99_proof_manual.
End VC_Correctness.
