From  Require Import linear_278_goal linear_278_proof_auto linear_278_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_278_proof_auto.
  Include linear_278_proof_manual.
End VC_Correctness.
