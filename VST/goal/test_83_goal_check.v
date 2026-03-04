From  Require Import test_83_goal test_83_proof_auto test_83_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_83_proof_auto.
  Include test_83_proof_manual.
End VC_Correctness.
