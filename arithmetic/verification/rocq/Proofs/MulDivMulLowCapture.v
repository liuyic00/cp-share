From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivTiming MulDivSignedBits MulDivMultiplyCapture MulDivMultiplySignedProduct MulDivMulLowProduct MulDivControl MulDivRefinement MulDivSignedInputEdge MulDivUnsignedCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivSignedInputEdge.MulDivSignedInputEdge.
Open Scope Z_scope.
Module MulDivMulLowCapture.
Definition divisorSign i := sign64 (nio_5Freq_5Fbits_5Fin2 i).
Definition outputNegative i := if sign64 (nio_5Freq_5Fbits_5Fin1 i)=?sign64 (nio_5Freq_5Fbits_5Fin2 i) then 0 else 1.
Definition divisorBits i := word 65 (Z.shiftl (divisorSign i) 64+word 64 (nio_5Freq_5Fbits_5Fin2 i)).
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  v6 s i=1 /\ v20 s i=sign64 (nio_5Freq_5Fbits_5Fin1 i) /\ v29 s i=divisorSign i /\ v79 s i=0.
Proof.
  unfold v79,v78,v77,v76,v75,v74,v29,v28,v27,v26,v25,v24,v23,v22,v21,v20,v19,v18,v17,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3,divisorSign,sign64.
  rewrite full; rewrite operation; clean;
    destruct (bit_cases (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin1 i)) 63)) as [ha|ha];
    destruct (bit_cases (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 63)) as [hb|hb]; rewrite ?ha,?hb; repeat split; reflexivity.
Qed.
Lemma full_join i x (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  Z.shiftl (word 32 (word 32 (Z.shiftr (word 64 x) 32))) 32+word 32 (Z.shiftr (word 64 x) 0)=word 64 x.
Proof.
  pose proof (MulDivUnsignedCapture.MulDivUnsignedCapture.split_operand i x) as h.
  unfold MulDivUnsignedCapture.MulDivUnsignedCapture.operand in h; rewrite full in h; exact h.
Qed.
Lemma capture s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  r0_nstate (step s i)=2 /\ r3_ncount (step s i)=0 /\
  r7_ndivisor (step s i)=divisorBits i /\
  r8_nremainder (step s i)=word 64 (nio_5Freq_5Fbits_5Fin1 i) /\
  r4_nneg_5Fout (step s i)=outputNegative i /\
  r1_nreq_5Fdw (step s i)=1 /\
  r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\ r5_nisHi (step s i)=0.
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation full) as [mul [a [b hi]]].
  split.
  - cbn [step r0_nstate]; rewrite reset; unfold v61,v34,v7; rewrite accept,mul; reflexivity.
  - split.
    + cbn [step r3_ncount]; unfold v73,v67,v66,v65,v64,v31,v8; rewrite accept,mul,full; reflexivity.
    + split.
      * cbn [step r7_ndivisor]; unfold v109,v105,v104,v103,v101; rewrite accept,full,b; cbn [Z.eqb Pos.eqb].
        rewrite normalize by lia; unfold divisorBits.
        replace (Z.shiftl (Z.shiftl (divisorSign i) 32+word 32 (word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 32))) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)) with
          (Z.shiftl (divisorSign i) 64+(Z.shiftl (word 32 (word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 32))) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)))
          by (rewrite !Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; change (2^64) with 18446744073709551616; ring).
        rewrite (full_join i _ full); reflexivity.
      * split.
        -- cbn [step r8_nremainder]; unfold v151,v115,v114,v113,v111,v110; rewrite accept,full; cbn [Z.eqb Pos.eqb].
           change (word 66 0) with 0; change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l,normalize by lia.
           rewrite (full_join i _ full); apply Words.word_widen; lia.
        -- cbn [step r4_nneg_5Fout r1_nreq_5Fdw r2_nreq_5Ftag r5_nisHi].
           unfold v92,v81,v80,v62,v63,v93; rewrite accept,a,b,hi,full; clean.
           repeat rewrite normalize by lia.
           unfold outputNegative,divisorSign,sign64.
           destruct (bit_cases (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin1 i)) 63)) as [ha|ha];
             destruct (bit_cases (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 63)) as [hb|hb];
             rewrite ha,hb; repeat split; reflexivity.
Qed.
Lemma divisor_value i : SignedWords.signed 65 (divisorBits i)=SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin2 i).
Proof.
  change (SignedWords.signed 65 (MulDivSignedBits.MulDivSignedBits.extended65 (nio_5Freq_5Fbits_5Fin2 i))=SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin2 i)).
  rewrite MulDivSignedBits.MulDivSignedBits.extended_signed; apply SignedWords.signed_extend; lia.
Qed.
Local Opaque run step.
Theorem accepted_product s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : MulDivTiming.MulDivTiming.active inputs 65) :
  word 64 (MulDivMultiply.MulDivMultiply.packed (run s inputs 65))=
    word 64 (word 64 (nio_5Freq_5Fbits_5Fin1 (inputs O))*word 64 (nio_5Freq_5Fbits_5Fin2 (inputs O))).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation full) as [st [ct [dv [sh rest]]]].
  pose proof (MulDivMultiply.MulDivMultiply.bounds 64 (nio_5Freq_5Fbits_5Fin1 (inputs O)) ltac:(lia)) as ha.
  destruct (MulDivMultiplyCapture.MulDivMultiplyCapture.captured_layout (step s (inputs O)) _ ha sh) as [pk sg].
  assert (hb : -(2^64)<SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin2 (inputs O))<2^64).
  { pose proof (SignedWords.signed_range 64 (nio_5Freq_5Fbits_5Fin2 (inputs O)) ltac:(lia)); change (2^(64-1)) with 9223372036854775808 in H; change (2^64) with 18446744073709551616; lia. }
  pose proof (MulDivMulLowProduct.MulDivMulLowProduct.low_product (step s (inputs O)) (fun t => inputs (S t))
    _ _ ha hb ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(rewrite dv; apply divisor_value) sg pk ltac:(intros t ht; apply live; lia)) as product.
  rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs 64),product.
  assert (normal : forall a b, word 64 (a*SignedWords.signed 64 b)=word 64 (a*word 64 b)).
  { intros a b.
    assert (modular : word 64 (a*word 64 (SignedWords.signed 64 b))=word 64 (a*SignedWords.signed 64 b))
      by (unfold word; apply Z.mul_mod_idemp_r; discriminate).
    rewrite <- modular; rewrite SignedWords.word_signed by lia; reflexivity. }
  apply normal.
Qed.
End MulDivMulLowCapture.
Print Assumptions MulDivMulLowCapture.capture.
Print Assumptions MulDivMulLowCapture.accepted_product.
