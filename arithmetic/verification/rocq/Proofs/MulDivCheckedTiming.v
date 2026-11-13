From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedMetadata MulDivCheckedMulTiming MulDivCheckedUnsignedTiming MulDivCheckedSignedTimingTrace.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked.
Open Scope Z_scope.
Module MulDivCheckedTiming.
(* Both generated timing assertions, all thirteen legal operation/width modes,
   arbitrary inputs and observations after a reset edge. *)
Theorem timing_assertions_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  forallb (fun b=>b) (firstn 2 (assertionChecks (run (step initial resetInput) pins n) (pins n)))=true.
Proof.
  set (s := run (step initial resetInput) pins n).
  destruct (Z.eq_dec (word 1 (r9_ncontractPending s)) 1) as [pending|inactive].
  - destruct (MulDivCheckedMetadata.MulDivCheckedMetadata.legal_run initial resetInput reset pins n pending) as [range width].
    change (word 4 (r11_ncontractFn s)<8) in range.
    assert (cases : word 4 (r11_ncontractFn s)<4 \/
      (word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=6) \/
      (word 4 (r11_ncontractFn s)=5 \/ word 4 (r11_ncontractFn s)=7)) by lia.
    destruct cases as [mul|[signed|unsigned]].
    + apply MulDivCheckedMulTiming.MulDivCheckedMulTiming.timing_assertions_after_reset; assumption.
    + apply MulDivCheckedSignedTimingTrace.MulDivCheckedSignedTimingTrace.timing_assertions_after_reset; assumption.
    + apply MulDivCheckedUnsignedTiming.MulDivCheckedUnsignedTiming.timing_assertions_after_reset; assumption.
  - apply MulDivCheckedTimingChecks.MulDivCheckedTimingChecks.inactive; exact inactive.
Qed.
End MulDivCheckedTiming.
Print Assumptions MulDivCheckedTiming.timing_assertions_after_reset.
