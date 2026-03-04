From  Require Import test_5_goal test_5_proof_auto test_5_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_5_proof_auto.
  Include test_5_proof_manual.
End VC_Correctness.
