From  Require Import 23_goal 23_proof_auto 23_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 23_proof_auto.
  Include 23_proof_manual.
End VC_Correctness.
