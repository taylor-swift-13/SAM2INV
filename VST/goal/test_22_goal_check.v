From  Require Import test_22_goal test_22_proof_auto test_22_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_22_proof_auto.
  Include test_22_proof_manual.
End VC_Correctness.
