From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivDivision MulDivRefinement MulDivSimulation MulDivResult.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivSimulation.MulDivSimulation MulDivResult.MulDivResult.
Open Scope Z_scope.
Module MulDivInitialization.
Lemma initial_candidate a : RD.candidate (word 64 a)=0.
Proof.
  rewrite RB.candidate_div.
  change (word 129 (word 64 a)/RB.base=0).
  assert (widen : word 129 (word 64 a)=word 64 a) by (apply Words.word_widen; lia).
  rewrite widen; apply Z.div_small; exact (Words.word_bound 64 a ltac:(lia)).
Qed.
Lemma initial_restoring a d (positive : 0<word 64 d) :
  RD.restoringStep (word 64 a) d=2*word 64 a.
Proof.
  unfold RD.restoringStep,RD.reducedWord,RD.quotientBit.
  change (word 129 (Z.shiftl (Z.shiftl
    (word 64 (if word 64 d<=?RD.candidate (word 64 a)
      then RD.lowCandidate (word 64 a)-word 64 d else RD.lowCandidate (word 64 a))) 64+
    word 64 (Z.shiftr (word 129 (word 64 a)) 0)) 1+
    (if word 64 d<=?RD.candidate (word 64 a) then 1 else 0))=2*word 64 a).
  rewrite initial_candidate.
  assert (choose : (word 64 d<=?0)=false) by (apply Z.leb_gt; exact positive).
  rewrite choose.
  assert (low : RD.lowCandidate (word 64 a)=0).
  { rewrite RD.lowCandidate_mod,initial_candidate; reflexivity. }
  rewrite low; change (word 64 0) with 0; change (Z.shiftl 0 64) with 0.
  rewrite Z.add_0_l,Z.add_0_r,Z.shiftr_0_r,narrow,normalize by lia.
  rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2.
  rewrite small by (pose proof (Words.word_bound 64 a ltac:(lia)) as h;
    change (0<=word 64 a<18446744073709551616) in h;
    change (0<=word 64 a*2<680564733841876926926749214863536422912); lia).
  ring.
Qed.
Lemma first_edge s i a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=word 64 d) (positive : 0<word 64 d)
  (initial : packed s=word 64 a) (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  word 3 (r0_nstate (step s i))=3 /\ word 7 (r3_ncount (step s i))=1 /\
  word 65 (r7_ndivisor (step s i))=word 64 d /\ packed (step s i)=2*word 64 a.
Proof.
  split; [rewrite (div_state _ _ state hr hk),count; reflexivity|].
  split; [rewrite (compute_count _ _ (or_intror state)),count; reflexivity|].
  split.
  - rewrite (MulDivDivision.MulDivDivision.divisor_stable _ _ state),normalize by lia; exact divisor.
  - rewrite (packed_step _ _ d state divisor).
    + rewrite initial; apply initial_restoring; exact positive.
    + rewrite candidate_packed; change (RD.candidate (packed s)<2*word 64 d).
      rewrite initial,initial_candidate; lia.
Qed.
Local Opaque run step.
Theorem full_magnitude_result s inputs a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=word 64 d) (positive : 0<word 64 d)
  (initial : packed s=word 64 a) (live : active inputs 65) :
  word 64 (r8_nremainder (run s inputs 65))=word 64 a/word 64 d /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs 65))) 65)=word 64 a mod word 64 d.
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (first_edge s (inputs O) a d state count divisor positive initial hr hk) as [st [ct [dv sh]]].
  rewrite (run_from_next s inputs 64).
  apply compute_64_result; try assumption.
  unfold active; intros t ht; apply live; lia.
Qed.
End MulDivInitialization.
Print Assumptions MulDivInitialization.full_magnitude_result.
