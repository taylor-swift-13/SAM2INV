From  Require Import 24_goal 24_proof_auto 24_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 24_proof_auto.
  Include 24_proof_manual.
End VC_Correctness.
