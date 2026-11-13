From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixFinishInvariant RadixComputeInvariant RadixSetupInvariant.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixFinishInvariant.RadixFinishInvariant
  RadixComputeInvariant.RadixComputeInvariant RadixSetupInvariant.RadixSetupInvariant.
Open Scope Z_scope.
Module RadixTrace.
Definition ShiftCorrect s := forall i, word 1 (nreset i)=0 -> ComputeCorrect (step s i).
Definition TraceInvariant s :=
  word 3 (r0_nstate s)=0 \/
  (word 3 (r0_nstate s)=1 /\ CaptureCorrect s) \/
  (word 3 (r0_nstate s)=2 /\ ShiftCorrect s) \/
  (word 3 (r0_nstate s)=3 /\ ComputeCorrect s) \/
  (word 3 (r0_nstate s)=4 /\ MagnitudeCorrect s).
Lemma idle_stays s i (hs : word 3 (r0_nstate s)=0)
  (hr : word 1 (nreset i)=0) (hv : word 1 (nio_5Fin_5Fvalid i)=0) : r0_nstate (step s i)=0.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hv; reflexivity. Qed.
Lemma finish_control s i (hs : word 3 (r0_nstate s)=4)
  (hr : word 1 (nreset i)=0) : word 3 (r0_nstate (step s i))=0 \/ word 3 (r0_nstate (step s i))=4.
Proof.
  cbn [step r0_nstate]; rewrite hr; control; rewrite hs.
  destruct (Words.bit_cases (nio_5Fout_5Fready i)) as [h|h];
    change (Words.word 1 (nio_5Fout_5Fready i)) with (word 1 (nio_5Fout_5Fready i)) in h;
    rewrite h; [right | left]; reflexivity.
Qed.
Local Opaque step run.
Theorem trace_invariant_step s i (invariant : TraceInvariant s) : TraceInvariant (step s i).
Proof.
  destruct (Words.bit_cases (nreset i)) as [hr|hr]; change (Words.word 1 (nreset i)) with (word 1 (nreset i)) in hr.
  2: { left; rewrite (reset_idle s i hr); reflexivity. }
  destruct invariant as [idle|[[logState captured]|[[shiftState shifted]|[[computeState computing]|[finishState finished]]]]].
  - destruct (Words.bit_cases (nio_5Fin_5Fvalid i)) as [hv|hv]; change (Words.word 1 (nio_5Fin_5Fvalid i)) with (word 1 (nio_5Fin_5Fvalid i)) in hv.
    + left; rewrite (idle_stays s i idle hr hv); reflexivity.
    + right; left; split; [rewrite (accept_state s i hr idle hv); reflexivity | apply capture_invariant; assumption].
  - right; right; left; split; [rewrite (log2_state s i hr logState); reflexivity |].
    intros shift shiftReset inputs resets; apply setup_segment_correct; assumption.
  - right; right; right; left; split; [rewrite (shift_state s i hr shiftState); reflexivity | apply shifted; exact hr].
  - destruct (Z.eq_dec (word 6 (r9_ncnt_5Fvalue s)) 63) as [last|notLast].
    + right; right; right; right; split.
      * rewrite (compute_state s i hr computeState), last; reflexivity.
      * apply compute_correct_last; assumption.
    + right; right; right; left; split.
      * rewrite (compute_state s i hr computeState).
        assert (h : (word 6 (r9_ncnt_5Fvalue s)=?63)=false) by (apply Z.eqb_neq; exact notLast).
        rewrite h; reflexivity.
      * apply compute_correct_step; assumption.
  - destruct (finish_control s i finishState hr) as [idle|finish].
    + left; exact idle.
    + right; right; right; right; split; [exact finish | apply finish_preserves_correct; assumption].
Qed.
Theorem trace_invariant_run initial resetInput inputs n
  (reset : word 1 (nreset resetInput)=1) : TraceInvariant (run (step initial resetInput) inputs n).
Proof.
  induction n as [|n IH].
  - change (TraceInvariant (step initial resetInput)); left; rewrite (reset_idle initial resetInput reset); reflexivity.
  - change (TraceInvariant (step (run (step initial resetInput) inputs n) (inputs n))); apply trace_invariant_step; exact IH.
Qed.
Lemma trace_invariant_finish s (h : TraceInvariant s) : FinishInvariant s.
Proof.
  intro finish; destruct h as [h|[[h c]|[[h c]|[[h c]|[h c]]]]]; try congruence; exact c.
Qed.
Theorem all_assertions_after_reset initial resetInput inputs n
  (reset : word 1 (nreset resetInput)=1) : asserts (run (step initial resetInput) inputs n) (inputs n).
Proof.
  pose proof (trace_invariant_finish _ (trace_invariant_run initial resetInput inputs n reset)) as h.
  destruct n as [|n].
  - change (asserts (step initial resetInput) (inputs O)); apply finish_invariant_asserts; exact h.
  - change (asserts (step (run (step initial resetInput) inputs n) (inputs n)) (inputs (S n))).
    apply finish_invariant_asserts; exact h.
Qed.
End RadixTrace.
Print Assumptions RadixTrace.all_assertions_after_reset.
