From  Require Import 0_goal 0_proof_auto 0_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 0_proof_auto.
  Include 0_proof_manual.
End VC_Correctness.
