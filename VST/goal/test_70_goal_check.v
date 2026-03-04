From  Require Import test_70_goal test_70_proof_auto test_70_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_70_proof_auto.
  Include test_70_proof_manual.
End VC_Correctness.
