From  Require Import 29_goal 29_proof_auto 29_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 29_proof_auto.
  Include 29_proof_manual.
End VC_Correctness.
