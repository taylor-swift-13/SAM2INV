From  Require Import 2.c_goal 2.c_proof_auto 2.c_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 2.c_proof_auto.
  Include 2.c_proof_manual.
End VC_Correctness.
