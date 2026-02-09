From  Require Import 19_goal 19_proof_auto 19_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 19_proof_auto.
  Include 19_proof_manual.
End VC_Correctness.
