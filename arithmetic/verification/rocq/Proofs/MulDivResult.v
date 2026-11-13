From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixResult MulDivControl MulDivTiming MulDivRefinement MulDivSimulation.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivSimulation.MulDivSimulation.
Open Scope Z_scope.
Module MulDivResult.
Lemma run_normal n sh d : word 129 (restoringRun n sh d)=restoringRun n sh d.
Proof.
  destruct n; cbn [restoringRun]; [apply normalize; lia|].
  unfold RD.restoringStep; apply Words.word_idem; lia.
Qed.
Lemma run_balance n sh d (bound : RD.candidate sh<2*word 64 d) :
  exists q, 0<=q<2^Z.of_nat n /\
  restoringRun n sh d+2*RB.base*word 64 d*q=2^Z.of_nat n*word 129 sh+q.
Proof.
  induction n as [|n [q [size balance]]].
  - exists 0; cbn [restoringRun]; split; [cbn; lia|change (word 129 sh+2*RB.base*word 64 d*0=1*word 129 sh+0); ring].
  - pose proof (restoring_run_bound n sh d bound) as hb.
    pose proof (RB.restoringStep_balance (restoringRun n sh d) d hb) as edge.
    change (RD.restoringStep (restoringRun n sh d) d+2*RB.base*word 64 d*RD.quotientBit (restoringRun n sh d) d=
      2*word 129 (restoringRun n sh d)+RD.quotientBit (restoringRun n sh d) d) in edge.
    rewrite run_normal in edge.
    pose proof (RB.digit_bound (restoringRun n sh d) d) as digit.
    exists (2*q+RD.quotientBit (restoringRun n sh d) d).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    cbn [restoringRun]; split; [lia|nia].
Qed.
Lemma restoring_result n sh d a (limit : (n<=64)%nat)
  (bound : RD.candidate sh<2*word 64 d)
  (alignment : 2^Z.of_nat n*word 129 sh=2*RB.base*a) :
  word 64 (restoringRun n sh d)=a/word 64 d /\
  word 64 (Z.shiftr (restoringRun n sh d) 65)=a mod word 64 d.
Proof.
  destruct (run_balance n sh d bound) as [q [size balance]].
  pose proof (restoring_run_bound n sh d bound) as hb.
  rewrite RB.candidate_div in hb.
  change (word 129 (restoringRun n sh d)/RB.base<2*word 64 d) in hb.
  rewrite run_normal in hb.
  assert (hz : 0<=restoringRun n sh d).
  { rewrite <- run_normal; exact (proj1 (Words.word_bound 129 _ ltac:(lia))). }
  assert (power : 2^Z.of_nat n<=RB.base) by (change (2^Z.of_nat n<=2^64); apply Z.pow_le_mono_r; lia).
  rewrite alignment in balance.
  destruct (RadixResult.RadixResult.decode_balance _ a (word 64 d) q hz ltac:(lia) hb balance) as [hq hr].
  split; [exact hq|].
  pose proof (RadixResult.RadixResult.final_remainder (restoringRun n sh d)) as wire.
  change (word 64 (Z.shiftr (word 129 (restoringRun n sh d)) 65)=word 129 (restoringRun n sh d)/(2*RB.base)) in wire.
  rewrite run_normal in wire; rewrite wire; exact hr.
Qed.
Theorem compute_result n s inputs d a (state : word 3 (r0_nstate s)=3)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=65) (limit : (n<=64)%nat)
  (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (bound : RD.candidate (packed s)<2*word 64 d) (live : active inputs n)
  (alignment : 2^Z.of_nat n*packed s=2*RB.base*a) :
  word 64 (r8_nremainder (run s inputs n))=a/word 64 d /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs n))) 65)=a mod word 64 d.
Proof.
  destruct (simulate n s inputs d state remaining divisor bound live) as [sim dv].
  assert (normal : word 129 (packed s)=packed s) by (unfold packed; apply normalize; lia).
  destruct (restoring_result n (packed s) d a limit bound ltac:(rewrite normal; exact alignment)) as [hq hr].
  rewrite <- sim in hq,hr; unfold packed in hq,hr.
  rewrite narrow in hq by lia; split; [exact hq|].
  rewrite extract_normal in hr by lia; rewrite extract_normal by lia; exact hr.
Qed.
Local Opaque run step.
Theorem compute_64_result s inputs d a (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=1)
  (divisor : word 65 (r7_ndivisor s)=word 64 d) (positive : 0<word 64 d)
  (initial : packed s=2*word 64 a) (live : active inputs 64) :
  word 64 (r8_nremainder (run s inputs 64))=word 64 a/word 64 d /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs 64))) 65)=word 64 a mod word 64 d.
Proof.
  apply compute_result; try assumption.
  - rewrite count; vm_compute; discriminate.
  - lia.
  - rewrite RB.candidate_div.
    change (word 129 (packed s)/RB.base<2*word 64 d).
    assert (normal : word 129 (packed s)=packed s) by (unfold packed; apply normalize; lia).
    rewrite normal,initial.
    pose proof (Words.word_bound 64 a ltac:(lia)) as ha.
    change (0<=word 64 a<18446744073709551616) in ha.
    assert (small : 2*word 64 a/RB.base<2) by (apply Z.div_lt_upper_bound; unfold RB.base; lia).
    lia.
  - rewrite initial; change (2^64*(2*word 64 a)=2*18446744073709551616*word 64 a).
    change (2^64) with 18446744073709551616; ring.
Qed.
End MulDivResult.
Print Assumptions MulDivResult.compute_result.
Print Assumptions MulDivResult.compute_64_result.
