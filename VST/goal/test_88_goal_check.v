From  Require Import test_88_goal test_88_proof_auto test_88_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_88_proof_auto.
  Include test_88_proof_manual.
End VC_Correctness.
