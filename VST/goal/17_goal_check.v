From  Require Import 17_goal 17_proof_auto 17_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 17_proof_auto.
  Include 17_proof_manual.
End VC_Correctness.
