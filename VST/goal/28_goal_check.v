From  Require Import 28_goal 28_proof_auto 28_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 28_proof_auto.
  Include 28_proof_manual.
End VC_Correctness.
