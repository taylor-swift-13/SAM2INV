From  Require Import 26_goal 26_proof_auto 26_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 26_proof_auto.
  Include 26_proof_manual.
End VC_Correctness.
