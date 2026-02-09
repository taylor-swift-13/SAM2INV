From  Require Import 4.c_goal 4.c_proof_auto 4.c_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 4.c_proof_auto.
  Include 4.c_proof_manual.
End VC_Correctness.
