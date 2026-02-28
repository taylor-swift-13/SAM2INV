From  Require Import linear_310_goal linear_310_proof_auto linear_310_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include linear_310_proof_auto.
  Include linear_310_proof_manual.
End VC_Correctness.
