From  Require Import test_50_goal test_50_proof_auto test_50_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_50_proof_auto.
  Include test_50_proof_manual.
End VC_Correctness.
