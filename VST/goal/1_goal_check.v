From  Require Import 1_goal 1_proof_auto 1_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 1_proof_auto.
  Include 1_proof_manual.
End VC_Correctness.
