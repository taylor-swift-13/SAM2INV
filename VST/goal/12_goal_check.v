From  Require Import 12_goal 12_proof_auto 12_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 12_proof_auto.
  Include 12_proof_manual.
End VC_Correctness.
