From  Require Import test_39_goal test_39_proof_auto test_39_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_39_proof_auto.
  Include test_39_proof_manual.
End VC_Correctness.
