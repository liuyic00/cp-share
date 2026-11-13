From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedMulBridge MulDivCheckedMulTrace.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked.
Open Scope Z_scope.
Module MulDivCheckedMulOutput.
Theorem data_assertion_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n
  (operation : word 4 (r11_ncontractFn (run (step initial resetInput) pins n))<4) :
  nth 3 (assertionChecks (run (step initial resetInput) pins n) (pins n)) false=true.
Proof.
  set (s := run (step initial resetInput) pins n) in *.
  destruct (Z.eq_dec (word 1 (r9_ncontractPending s)) 1) as [pending|inactive].
  2: { apply MulDivCheckedData.MulDivCheckedData.inactive; intuition. }
  destruct (Z.eq_dec (v38 s (pins n)) 1) as [valid|inactive].
  2: { apply MulDivCheckedData.MulDivCheckedData.inactive; intuition. }
  destruct (MulDivCheckedMetadata.MulDivCheckedMetadata.legal_run initial resetInput reset pins n pending) as [range width].
  change (word 1 (r12_ncontractDw s)=1 \/ word 4 (r11_ncontractFn s)=0 \/ 4<=word 4 (r11_ncontractFn s)) in width.
  destruct (MulDivCheckedMulTrace.MulDivCheckedMulTrace.run_invariant initial resetInput reset pins n pending operation) as [[state rest]|[state result]].
  - change (word 3 (r0_nstate s)=2) in state; unfold v38,v37,v36,v35,v4 in valid; rewrite state in valid; discriminate.
  - apply MulDivCheckedData.MulDivCheckedData.of_correct.
    rewrite MulDivCheckedMulBridge.MulDivCheckedMulBridge.expected_eq_specification.
    + apply result.
    + change (word 4 (r11_ncontractFn s)<4 /\ (word 4 (r11_ncontractFn s)=0 \/ word 1 (r12_ncontractDw s)=1)); intuition lia.
Qed.
End MulDivCheckedMulOutput.
Print Assumptions MulDivCheckedMulOutput.data_assertion_after_reset.
