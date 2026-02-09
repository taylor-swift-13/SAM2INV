From  Require Import 6_goal 6_proof_auto 6_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 6_proof_auto.
  Include 6_proof_manual.
End VC_Correctness.
