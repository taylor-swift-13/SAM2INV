From  Require Import test_78_goal test_78_proof_auto test_78_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_78_proof_auto.
  Include test_78_proof_manual.
End VC_Correctness.
