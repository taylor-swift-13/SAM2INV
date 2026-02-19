From  Require Import NLA_lipus_38_goal NLA_lipus_38_proof_auto NLA_lipus_38_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include NLA_lipus_38_proof_auto.
  Include NLA_lipus_38_proof_manual.
End VC_Correctness.
