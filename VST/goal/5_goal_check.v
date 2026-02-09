From  Require Import 5_goal 5_proof_auto 5_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 5_proof_auto.
  Include 5_proof_manual.
End VC_Correctness.
