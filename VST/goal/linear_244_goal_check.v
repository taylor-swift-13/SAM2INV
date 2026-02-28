From  Require Import linear_244_goal linear_244_proof_auto linear_244_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_244_proof_auto.
  Include linear_244_proof_manual.
End VC_Correctness.
