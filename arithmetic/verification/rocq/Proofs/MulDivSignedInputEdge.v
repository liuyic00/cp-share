From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivRefinement MulDivDivision MulDivInitialization MulDivMetadata.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivMetadata.MulDivMetadata.
Open Scope Z_scope.
Module MulDivSignedInputEdge.
Definition sign64 x := word 1 (Z.shiftr (word 64 x) 63).
Definition magnitude x := if sign64 x=?1 then word 64 (-word 64 x) else word 64 x.
Lemma initial_slices s a (initial : packed s=word 64 a) :
  v84 s (mkInputs 0 0 0 0 0 0 0 0 0)=0 /\
  word 64 (r8_nremainder s)=word 64 a /\
  word 1 (Z.shiftr (word 130 (r8_nremainder s)) 63)=sign64 a.
Proof.
  split.
  - change (MulDivDivision.MulDivDivision.candidate (r8_nremainder s)=0).
    rewrite candidate_packed; change (RadixDatapath.RadixDatapath.candidate (packed s)=0).
    rewrite initial; apply MulDivInitialization.MulDivInitialization.initial_candidate.
  - split.
    + rewrite <- (narrow 129 64 (r8_nremainder s)) by lia.
      change (word 64 (packed s)=word 64 a); rewrite initial,normalize by lia; reflexivity.
    + rewrite extract_normal by lia.
      rewrite <- (extract_normal 129 1 63 (r8_nremainder s)) by lia.
      change (word 1 (Z.shiftr (packed s) 63)=sign64 a); rewrite initial; reflexivity.
Qed.
Lemma input_edge s i a (state : word 3 (r0_nstate s)=1)
  (initial : packed s=word 64 a) (select : word 1 (r6_nresHi s)=0) :
  r7_ndivisor (step s i)=(if sign64 (r7_ndivisor s)=?1 then word 65 (-word 65 (r7_ndivisor s)) else word 65 (r7_ndivisor s)) /\
  packed (step s i)=magnitude a /\
  metadata (step s i)=metadata s /\ r4_nneg_5Fout (step s i)=word 1 (r4_nneg_5Fout s).
Proof.
  destruct (initial_slices s a initial) as [candidate [low sign]].
  change (word 65 (Z.shiftr (word 130 (r8_nremainder s)) 64)=0) in candidate.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  assert (div : v42 s i=0) by (unfold v42,v41; rewrite state; reflexivity).
  assert (mul : v48 s i=0) by (unfold v48,v7; rewrite state; reflexivity).
  assert (neg : v53 s i=0) by (unfold v53,v52; rewrite state; reflexivity).
  assert (input : v55 s i=1) by (unfold v55,v54; rewrite state; reflexivity).
  assert (dSign : v106 s i=sign64 (r7_ndivisor s)).
  { unfold v106,sign64; rewrite !extract_normal by lia; reflexivity. }
  split.
  - cbn [step r7_ndivisor]; unfold v109,v108,v107,v85,v84.
    rewrite accept,input,dSign,candidate; rewrite Z.sub_0_l.
    unfold sign64 at 1; destruct (bit_cases (Z.shiftr (word 64 (r7_ndivisor s)) 63)) as [h|h];
      unfold sign64; rewrite h; clean; repeat rewrite normalize by lia; reflexivity.
  - split.
    + unfold packed at 1; cbn [step r8_nremainder]; unfold v151,v150,v149,v148,v142,v141,v140.
      rewrite accept,div,mul,neg,input,sign.
      unfold v147,v146,v145,v143,v119,v110; rewrite select.
      change (word 66 0) with 0; change (word 64 0) with 0; change (Z.shiftl 0 64) with 0.
      rewrite Z.add_0_l,Z.shiftr_0_r; rewrite (narrow 130 64),low by lia.
      unfold magnitude,sign64; destruct (bit_cases (Z.shiftr (word 64 a) 63)) as [h|h]; rewrite h; clean;
        repeat rewrite narrow by lia; repeat rewrite normalize by lia.
      * exact initial.
      * rewrite Z.sub_0_l; apply Words.word_widen; lia.
    + split.
      * destruct (busy_request_metadata s i ltac:(lia)) as [dw tag].
        assert (hi : r5_nisHi (step s i)=word 1 (r5_nisHi s)).
        { cbn [step r5_nisHi]; unfold v93; rewrite accept; cbn [Z.eqb]; apply normalize; lia. }
        unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; reflexivity.
      * cbn [step r4_nneg_5Fout]; unfold v92,v91,v90,v89,v31; rewrite accept,div; clean.
        destruct (bit_cases (r4_nneg_5Fout s)) as [h|h]; rewrite h; reflexivity.
Qed.
End MulDivSignedInputEdge.
Print Assumptions MulDivSignedInputEdge.input_edge.
