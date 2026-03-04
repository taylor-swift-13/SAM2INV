From  Require Import test_1_goal test_1_proof_auto test_1_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_1_proof_auto.
  Include test_1_proof_manual.
End VC_Correctness.
