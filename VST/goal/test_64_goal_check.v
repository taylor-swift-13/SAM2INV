From  Require Import test_64_goal test_64_proof_auto test_64_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_64_proof_auto.
  Include test_64_proof_manual.
End VC_Correctness.
