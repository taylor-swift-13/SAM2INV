From  Require Import 21_goal 21_proof_auto 21_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 21_proof_auto.
  Include 21_proof_manual.
End VC_Correctness.
