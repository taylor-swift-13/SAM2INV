From  Require Import 11_goal 11_proof_auto 11_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 11_proof_auto.
  Include 11_proof_manual.
End VC_Correctness.
