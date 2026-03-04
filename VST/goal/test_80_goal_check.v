From  Require Import test_80_goal test_80_proof_auto test_80_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include test_80_proof_auto.
  Include test_80_proof_manual.
End VC_Correctness.
