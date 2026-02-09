From  Require Import 30_goal 30_proof_auto 30_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 30_proof_auto.
  Include 30_proof_manual.
End VC_Correctness.
