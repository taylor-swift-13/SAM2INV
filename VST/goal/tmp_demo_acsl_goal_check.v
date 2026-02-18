From  Require Import tmp_demo_acsl_goal tmp_demo_acsl_proof_auto tmp_demo_acsl_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include tmp_demo_acsl_proof_auto.
  Include tmp_demo_acsl_proof_manual.
End VC_Correctness.
