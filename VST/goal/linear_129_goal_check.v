From  Require Import linear_129_goal linear_129_proof_auto linear_129_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_129_proof_auto.
  Include linear_129_proof_manual.
End VC_Correctness.
