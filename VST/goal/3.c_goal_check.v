From  Require Import 3.c_goal 3.c_proof_auto 3.c_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include 3.c_proof_auto.
  Include 3.c_proof_manual.
End VC_Correctness.
