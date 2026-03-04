From  Require Import test_91_goal test_91_proof_auto test_91_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_91_proof_auto.
  Include test_91_proof_manual.
End VC_Correctness.
