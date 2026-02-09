From  Require Import 25_goal 25_proof_auto 25_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 25_proof_auto.
  Include 25_proof_manual.
End VC_Correctness.
