From  Require Import 7_goal 7_proof_auto 7_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 7_proof_auto.
  Include 7_proof_manual.
End VC_Correctness.
