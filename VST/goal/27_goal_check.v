From  Require Import 27_goal 27_proof_auto 27_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 27_proof_auto.
  Include 27_proof_manual.
End VC_Correctness.
