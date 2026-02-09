From  Require Import 18_goal 18_proof_auto 18_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 18_proof_auto.
  Include 18_proof_manual.
End VC_Correctness.
