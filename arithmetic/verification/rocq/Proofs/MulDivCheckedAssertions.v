From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedTiming MulDivCheckedMetadata MulDivCheckedStall
  MulDivCheckedDivisionAssertions MulDivCheckedDivisionOutputTrace MulDivCheckedMulOutput.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked.
Open Scope Z_scope.
Module MulDivCheckedAssertions.
Theorem data_assertion_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  nth 3 (assertionChecks (run (step initial resetInput) pins n) (pins n)) false=true.
Proof.
  set (s := run (step initial resetInput) pins n).
  destruct (Z.eq_dec (word 1 (r9_ncontractPending s)) 1) as [pending|inactive].
  - destruct (MulDivCheckedMetadata.MulDivCheckedMetadata.legal_run initial resetInput reset pins n pending) as [range width].
    change (word 4 (r11_ncontractFn s)<8) in range.
    destruct (Z_lt_dec (word 4 (r11_ncontractFn s)) 4) as [mul|div].
    + apply MulDivCheckedMulOutput.MulDivCheckedMulOutput.data_assertion_after_reset; assumption.
    + apply MulDivCheckedDivisionOutputTrace.MulDivCheckedDivisionOutputTrace.data_assertion_after_reset; [exact reset|].
      change (word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/ word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7); lia.
  - apply MulDivCheckedData.MulDivCheckedData.inactive; intuition.
Qed.
(* Exactly all eleven generated checks, on arbitrary traces after one reset edge. *)
Theorem all_assertions_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  asserts (run (step initial resetInput) pins n) (pins n).
Proof.
  pose proof (MulDivCheckedTiming.MulDivCheckedTiming.timing_assertions_after_reset initial resetInput reset pins n) as timing.
  pose proof (MulDivCheckedMetadata.MulDivCheckedMetadata.tag_assertion_after_reset initial resetInput reset pins n) as tag.
  pose proof (data_assertion_after_reset initial resetInput reset pins n) as data.
  pose proof (MulDivCheckedDivisionAssertions.MulDivCheckedDivisionAssertions.assertions_after_reset initial resetInput reset pins n) as arithmetic.
  pose proof (MulDivCheckedStall.MulDivCheckedStall.stall_assertions_trace initial resetInput pins n) as stall.
  unfold asserts,MulDivCheckedDivisionChecks.MulDivCheckedDivisionChecks.checks,assertionChecks in *.
  cbn [firstn skipn nth forallb] in *.
  repeat rewrite Bool.andb_true_iff in *; intuition.
Qed.
End MulDivCheckedAssertions.
Print Assumptions MulDivCheckedAssertions.all_assertions_after_reset.
