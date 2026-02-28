From  Require Import linear_128_goal linear_128_proof_auto linear_128_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_128_proof_auto.
  Include linear_128_proof_manual.
End VC_Correctness.
