From  Require Import 10_goal 10_proof_auto 10_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 10_proof_auto.
  Include 10_proof_manual.
End VC_Correctness.
