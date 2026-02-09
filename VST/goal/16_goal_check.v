From  Require Import 16_goal 16_proof_auto 16_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 16_proof_auto.
  Include 16_proof_manual.
End VC_Correctness.
