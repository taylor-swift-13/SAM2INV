From  Require Import tmp_precheck_9_goal tmp_precheck_9_proof_auto tmp_precheck_9_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include tmp_precheck_9_proof_auto.
  Include tmp_precheck_9_proof_manual.
End VC_Correctness.
