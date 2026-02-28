From  Require Import linear_91_goal linear_91_proof_auto linear_91_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_91_proof_auto.
  Include linear_91_proof_manual.
End VC_Correctness.
