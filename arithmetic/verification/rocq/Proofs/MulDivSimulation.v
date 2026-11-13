From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixDatapath RadixBalance MulDivControl MulDivTiming MulDivDivision MulDivRefinement.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement.
Open Scope Z_scope.
Module MulDivSimulation.
Module RD := RadixDatapath.RadixDatapath.
Module RB := RadixBalance.RadixBalance.
Lemma restoring_bound sh d (bound : RD.candidate sh<2*word 64 d) :
  RD.candidate (RD.restoringStep sh d)<2*word 64 d.
Proof.
  pose proof (Words.word_bound 65 (Z.shiftr (word 129 sh) 64) ltac:(lia)) as hc.
  change (0<=RD.candidate sh<2^65) in hc.
  assert (positive : 0<word 64 d) by lia.
  pose proof (RD.selected_digit_correct sh d positive bound) as [hi hr].
  change (0<=RD.reducedWord sh d<word 64 d) in hr.
  pose proof (Words.word_bound 64 sh ltac:(lia)) as hl.
  change (0<=RB.low sh<RB.base) in hl.
  rewrite RB.restoring_packed, RB.packed_candidate.
  - assert (RB.low sh/9223372036854775808<2) by (apply Z.div_lt_upper_bound; unfold RB.base in hl; lia); lia.
  - exact (Words.word_bound 64 _ ltac:(lia)).
  - exact hl.
  - apply RB.digit_bound.
Qed.
Fixpoint restoringRun n sh d := match n with O => word 129 sh | S k => RD.restoringStep (restoringRun k sh d) d end.
Lemma candidate_normal sh : RD.candidate (word 129 sh)=RD.candidate sh.
Proof. unfold RD.candidate; change (word 65 (Z.shiftr (word 129 (word 129 sh)) 64)=word 65 (Z.shiftr (word 129 sh) 64)); rewrite normalize by lia; reflexivity. Qed.
Lemma restoring_run_bound n sh d (bound : RD.candidate sh<2*word 64 d) :
  RD.candidate (restoringRun n sh d)<2*word 64 d.
Proof. induction n; cbn [restoringRun]; [rewrite candidate_normal; exact bound|apply restoring_bound; exact IHn]. Qed.
Lemma div_prefix n s inputs (state : word 3 (r0_nstate s)=3)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<65) (live : active inputs n) :
  word 3 (r0_nstate (run s inputs n))=3 /\
  word 7 (r3_ncount (run s inputs n))=word 7 (r3_ncount s)+Z.of_nat n.
Proof.
  induction n as [|n IH].
  - cbn [run]; rewrite Z.add_0_r; split; [exact state|reflexivity].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros t ht; apply live; lia)) as [hs count].
    destruct (live n ltac:(lia)) as [hr hk].
    assert (last : (word 7 (r3_ncount (run s inputs n))=?64)=false) by (apply Z.eqb_neq; rewrite Nat2Z.inj_succ in remaining; lia).
    change (word 3 (r0_nstate (step (run s inputs n) (inputs n)))=3 /\
      word 7 (r3_ncount (step (run s inputs n) (inputs n)))=word 7 (r3_ncount s)+Z.of_nat (S n)).
    split.
    + rewrite (div_state _ _ hs hr hk),last; reflexivity.
    + rewrite (compute_count _ _ (or_intror hs)),normalize by lia.
      rewrite small by (pose proof (count_bound s); rewrite count; change (0<=word 7 (r3_ncount s)+Z.of_nat n+1<128); rewrite Nat2Z.inj_succ in remaining; lia).
      rewrite count,Nat2Z.inj_succ; lia.
Qed.
Theorem simulate n s inputs d (state : word 3 (r0_nstate s)=3)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=65)
  (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (bound : RD.candidate (packed s)<2*word 64 d) (live : active inputs n) :
  packed (run s inputs n)=restoringRun n (packed s) d /\
  word 65 (r7_ndivisor (run s inputs n))=word 64 d.
Proof.
  induction n as [|n IH].
  - cbn [run restoringRun]; split; [unfold packed; symmetry; apply normalize; lia|exact divisor].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros t ht; apply live; lia)) as [prior dv].
    destruct (div_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros t ht; apply live; lia)) as [hs count].
    change (packed (step (run s inputs n) (inputs n))=RD.restoringStep (restoringRun n (packed s) d) d /\
      word 65 (r7_ndivisor (step (run s inputs n) (inputs n)))=word 64 d).
    split.
    + rewrite (packed_step _ _ d hs dv).
      * rewrite prior; reflexivity.
      * rewrite candidate_packed; change (RD.candidate (packed (run s inputs n))<2*word 64 d).
        rewrite prior; apply restoring_run_bound; exact bound.
    + rewrite (MulDivDivision.MulDivDivision.divisor_stable _ _ hs),normalize by lia; exact dv.
Qed.
End MulDivSimulation.
Print Assumptions MulDivSimulation.simulate.
