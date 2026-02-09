From  Require Import 8_goal 8_proof_auto 8_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 8_proof_auto.
  Include 8_proof_manual.
End VC_Correctness.
