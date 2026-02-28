From  Require Import linear_215_goal linear_215_proof_auto linear_215_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_215_proof_auto.
  Include linear_215_proof_manual.
End VC_Correctness.
