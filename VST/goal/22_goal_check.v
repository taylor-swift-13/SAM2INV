From  Require Import 22_goal 22_proof_auto 22_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 22_proof_auto.
  Include 22_proof_manual.
End VC_Correctness.
