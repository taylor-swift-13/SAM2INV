From  Require Import linear_103_goal linear_103_proof_auto linear_103_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_103_proof_auto.
  Include linear_103_proof_manual.
End VC_Correctness.
