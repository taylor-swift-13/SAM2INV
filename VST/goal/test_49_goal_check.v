From  Require Import test_49_goal test_49_proof_auto test_49_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_49_proof_auto.
  Include test_49_proof_manual.
End VC_Correctness.
