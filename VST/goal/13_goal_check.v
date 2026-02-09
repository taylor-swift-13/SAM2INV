From  Require Import 13_goal 13_proof_auto 13_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 13_proof_auto.
  Include 13_proof_manual.
End VC_Correctness.
