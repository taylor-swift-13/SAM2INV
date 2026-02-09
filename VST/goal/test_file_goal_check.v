From  Require Import test_file_goal test_file_proof_auto test_file_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_file_proof_auto.
  Include test_file_proof_manual.
End VC_Correctness.
