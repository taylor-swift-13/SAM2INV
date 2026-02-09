From  Require Import 3_goal 3_proof_auto 3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 3_proof_auto.
  Include 3_proof_manual.
End VC_Correctness.
