From  Require Import test_16_goal test_16_proof_auto test_16_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_16_proof_auto.
  Include test_16_proof_manual.
End VC_Correctness.
