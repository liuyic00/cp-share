From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivRefinement MulDivTiming MulDivInitialization.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement.
Open Scope Z_scope.
Module MulDivUnsignedCapture.
Definition operand i x := if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then word 64 x else word 32 x.
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) :
  v6 s i=0 /\ v20 s i=0 /\ v29 s i=0 /\
  v79 s i=(if word 4 (nio_5Freq_5Fbits_5Ffn i)=?7 then 1 else 0).
Proof.
  unfold v79,v78,v77,v76,v75,v74,v29,v25,v24,v23,v22,v21,v20,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3.
  destruct operation as [op|op]; rewrite op; clean; repeat split; reflexivity.
Qed.
Lemma operand_bound i x : 0<=operand i x<2^64.
Proof.
  unfold operand; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1).
  - exact (Words.word_bound 64 x ltac:(lia)).
  - pose proof (Words.word_bound 32 x ltac:(lia)) as h; change (0<=word 32 x<4294967296) in h; change (0<=word 32 x<18446744073709551616); lia.
Qed.
Lemma split_operand i x :
  Z.shiftl (word 32 (if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1
    then word 32 (Z.shiftr (word 64 x) 32) else 0)) 32+
    word 32 (Z.shiftr (word 64 x) 0)=operand i x.
Proof.
  unfold operand; rewrite Z.shiftr_0_r,narrow by lia.
  destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1).
  - rewrite normalize by lia; rewrite Z.shiftr_div_pow2,Z.shiftl_mul_pow2 by lia.
    rewrite (Words.word_small 32) by (pose proof (Words.word_bound 64 x ltac:(lia)) as h;
      change (0<=word 64 x<18446744073709551616) in h;
      change (0<=word 64 x/4294967296<4294967296); split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    pose proof (Z.div_mod (word 64 x) (2^32) ltac:(vm_compute; discriminate)) as split.
    change (word 64 x=2^32*(word 64 x/2^32)+word 32 (word 64 x)) in split.
    rewrite narrow in split by lia; lia.
  - change (word 32 0) with 0; change (Z.shiftl 0 32) with 0; lia.
Qed.
Lemma capture s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) :
  r0_nstate (step s i)=3 /\ r3_ncount (step s i)=0 /\
  r7_ndivisor (step s i)=operand i (nio_5Freq_5Fbits_5Fin2 i) /\
  packed (step s i)=operand i (nio_5Freq_5Fbits_5Fin1 i) /\
  r4_nneg_5Fout (step s i)=0 /\
  r1_nreq_5Fdw (step s i)=word 1 (nio_5Freq_5Fbits_5Fdw i) /\
  r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\
  r5_nisHi (step s i)=(if word 4 (nio_5Freq_5Fbits_5Ffn i)=?7 then 1 else 0).
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [aSign [dSign high]]].
  split.
  - cbn [step r0_nstate]; rewrite reset; unfold v61; rewrite accept.
    unfold v34,v33,v32,v30,v31,v8; rewrite mul,aSign,dSign; reflexivity.
  - split.
    + cbn [step r3_ncount]; unfold v73; rewrite accept; unfold v67,v66,v65,v8; rewrite mul; reflexivity.
    + split.
      * cbn [step r7_ndivisor]; unfold v109; rewrite accept; unfold v105,v104,v103,v102,v101; rewrite dSign.
        change (word 32 (repeatWord 32 1 0)) with 0.
        change (word 65 (word 65 (Z.shiftl (Z.shiftl 0 32+word 32 (if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 32) else 0)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)))=operand i (nio_5Freq_5Fbits_5Fin2 i)).
        change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l,normalize,split_operand by lia.
        apply Words.word_small; pose proof (operand_bound i (nio_5Freq_5Fbits_5Fin2 i)); change (0<=operand i (nio_5Freq_5Fbits_5Fin2 i)<36893488147419103232); change (2^64) with 18446744073709551616 in H; lia.
      * split.
        -- unfold packed; cbn [step r8_nremainder]; unfold v151; rewrite accept; cbn [Z.eqb Pos.eqb].
           unfold v115,v114,v113,v112,v111,v110; rewrite aSign.
           change (word 66 0) with 0; change (word 32 (repeatWord 32 1 0)) with 0.
           change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l.
           repeat rewrite narrow by lia; rewrite split_operand.
           apply Words.word_small; pose proof (operand_bound i (nio_5Freq_5Fbits_5Fin1 i)); change (0<=operand i (nio_5Freq_5Fbits_5Fin1 i)<680564733841876926926749214863536422912); change (2^64) with 18446744073709551616 in H; lia.
        -- cbn [step r4_nneg_5Fout r1_nreq_5Fdw r2_nreq_5Ftag r5_nisHi].
           unfold v92,v81,v80,v62,v63,v93; rewrite accept,aSign,dSign,high.
           destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?7); clean; repeat rewrite normalize by lia; repeat split; reflexivity.
Qed.
Local Opaque run step.
Theorem accepted_nonzero_magnitudes s inputs
  (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : MulDivTiming.MulDivTiming.active inputs 66)
  (positive : 0<operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))) :
  let a := operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O)) in
  let d := operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O)) in
  word 64 (r8_nremainder (run s inputs 66))=a/d /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs 66))) 65)=a mod d.
Proof.
  cbn zeta.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation) as [st [ct [dv [sh rest]]]].
  assert (an : word 64 (operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O)))=operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O))) by (apply Words.word_small; apply operand_bound).
  assert (dn : word 64 (operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O)))=operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))) by (apply Words.word_small; apply operand_bound).
  pose proof (MulDivInitialization.MulDivInitialization.full_magnitude_result
    (step s (inputs O)) (fun t => inputs (S t))
    (operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O)))
    (operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O)))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(rewrite dv,dn; apply Words.word_small; pose proof (operand_bound (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))) as h; change (2^64) with 18446744073709551616 in h; change (0<=operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))<36893488147419103232); lia)
    ltac:(rewrite dn; exact positive) ltac:(rewrite an; exact sh)
    ltac:(unfold MulDivTiming.MulDivTiming.active; intros t ht; apply live; lia)) as result.
  rewrite an,dn in result.
  rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs 65); exact result.
Qed.
End MulDivUnsignedCapture.
Print Assumptions MulDivUnsignedCapture.capture.
Print Assumptions MulDivUnsignedCapture.accepted_nonzero_magnitudes.
