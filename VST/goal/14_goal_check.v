From  Require Import 14_goal 14_proof_auto 14_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 14_proof_auto.
  Include 14_proof_manual.
End VC_Correctness.
