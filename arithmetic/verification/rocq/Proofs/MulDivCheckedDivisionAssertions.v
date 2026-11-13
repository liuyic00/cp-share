From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedDivisionTrace MulDivCheckedMetadata MulDivCheckedWitnessCorrect.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedDivisionAssertions.
Module D := MulDivCheckedDivisionTrace.MulDivCheckedDivisionTrace.
Module C := MulDivCheckedDivisionChecks.MulDivCheckedDivisionChecks.
Module W := MulDivCheckedWitnessCorrect.MulDivCheckedWitnessCorrect.
Lemma base_active s i (base : v267 s i<>0) :
  word 1 (r9_ncontractPending s)=1 /\ v191 s i=1 /\ v38 s i=1.
Proof.
  assert (fn : v191 s i=0 \/ v191 s i=1) by (unfold v191; apply bit_cases).
  assert (valid : v38 s i=0 \/ v38 s i=1) by (unfold v38; apply bit_cases).
  destruct (bit_cases (r9_ncontractPending s)) as [p|p].
  - exfalso; apply base; unfold v267,v233,v227; rewrite p; reflexivity.
  - split; [exact p|]; destruct fn as [fn|fn].
    + exfalso; apply base; unfold v267; rewrite fn,Z.land_0_r; reflexivity.
    + split; [exact fn|]; destruct valid as [valid|valid]; [|exact valid].
      exfalso; apply base; unfold v267,v233; rewrite valid,Z.land_0_r; reflexivity.
Qed.
Lemma division_operation s i (range : word 4 (r11_ncontractFn s)<8) (bit : v191 s i=1) : D.Operation s.
Proof.
  pose proof (bounds 4 (r11_ncontractFn s) ltac:(lia)) as bound.
  assert (cases : word 4 (r11_ncontractFn s)=0 \/ word 4 (r11_ncontractFn s)=1 \/
    word 4 (r11_ncontractFn s)=2 \/ word 4 (r11_ncontractFn s)=3 \/
    word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/
    word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7) by lia.
  unfold v191 in bit; unfold D.Operation;
    destruct cases as [fn|[fn|[fn|[fn|[fn|[fn|[fn|fn]]]]]]]; rewrite fn in bit; try discriminate; intuition.
Qed.
Lemma valid_witness s i (phases : D.Phases s) (valid : v38 s i=1) : W.Invariant s.
Proof.
  destruct phases as [[op [neg flag]]|[[state rest]|[[state correct]|[state correct]]]].
  - destruct neg as [state rest]; unfold v38,v37,v36,v35,v4 in valid; rewrite state in valid; discriminate.
  - unfold v38,v37,v36,v35,v4 in valid; rewrite state in valid; discriminate.
  - unfold v38,v37,v36,v35,v4 in valid; rewrite state in valid; discriminate.
  - exact correct.
Qed.
Theorem assertions_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  C.checks (run (step initial resetInput) pins n) (pins n).
Proof.
  set (s := run (step initial resetInput) pins n).
  destruct (Z.eq_dec (v267 s (pins n)) 0) as [inactive|active].
  - apply C.inactive_base; exact inactive.
  - destruct (base_active s (pins n) active) as [pending [bit valid]].
    destruct (MulDivCheckedMetadata.MulDivCheckedMetadata.legal_run initial resetInput reset pins n pending) as [range width].
    pose proof (division_operation s (pins n) range bit) as operation.
    apply W.arithmetic_checks; apply (valid_witness s (pins n)); [|exact valid].
    exact (D.run_invariant initial resetInput reset pins n pending operation).
Qed.
End MulDivCheckedDivisionAssertions.
Print Assumptions MulDivCheckedDivisionAssertions.assertions_after_reset.
