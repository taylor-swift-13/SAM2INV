From  Require Import test_46_goal test_46_proof_auto test_46_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_46_proof_auto.
  Include test_46_proof_manual.
End VC_Correctness.
