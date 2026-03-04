From  Require Import test_28_goal test_28_proof_auto test_28_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_28_proof_auto.
  Include test_28_proof_manual.
End VC_Correctness.
