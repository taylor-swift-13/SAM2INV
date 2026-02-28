From  Require Import linear_44_goal linear_44_proof_auto linear_44_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_44_proof_auto.
  Include linear_44_proof_manual.
End VC_Correctness.
