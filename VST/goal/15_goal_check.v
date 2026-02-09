From  Require Import 15_goal 15_proof_auto 15_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 15_proof_auto.
  Include 15_proof_manual.
End VC_Correctness.
