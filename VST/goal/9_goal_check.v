From  Require Import 9_goal 9_proof_auto 9_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 9_proof_auto.
  Include 9_proof_manual.
End VC_Correctness.
