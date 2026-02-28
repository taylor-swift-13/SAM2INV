From  Require Import linear_83_goal linear_83_proof_auto linear_83_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_83_proof_auto.
  Include linear_83_proof_manual.
End VC_Correctness.
