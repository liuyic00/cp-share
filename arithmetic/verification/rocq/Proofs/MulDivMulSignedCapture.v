From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivTiming MulDivSignedBits MulDivMultiplyCapture MulDivMultiplySignedProduct MulDivControl MulDivRefinement MulDivSignedInputEdge MulDivUnsignedCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivSignedInputEdge.MulDivSignedInputEdge.
Open Scope Z_scope.
Module MulDivMulSignedCapture.
Definition divisorSign i := if word 4 (nio_5Freq_5Fbits_5Ffn i)=?1 then sign64 (nio_5Freq_5Fbits_5Fin2 i) else 0.
Definition divisorBits i := word 65 (Z.shiftl (divisorSign i) 64+word 64 (nio_5Freq_5Fbits_5Fin2 i)).
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  v6 s i=1 /\ v20 s i=sign64 (nio_5Freq_5Fbits_5Fin1 i) /\ v29 s i=divisorSign i /\ v79 s i=1.
Proof.
  unfold v79,v78,v77,v76,v75,v74,v29,v28,v27,v26,v25,v24,v23,v22,v21,v20,v19,v18,v17,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3,divisorSign,sign64.
  rewrite full; destruct operation as [op|op]; rewrite op; clean;
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
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  r0_nstate (step s i)=2 /\ r3_ncount (step s i)=0 /\
  r7_ndivisor (step s i)=divisorBits i /\
  r8_nremainder (step s i)=word 64 (nio_5Freq_5Fbits_5Fin1 i) /\
  r4_nneg_5Fout (step s i)=sign64 (nio_5Freq_5Fbits_5Fin1 i) /\
  r1_nreq_5Fdw (step s i)=1 /\
  r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\ r5_nisHi (step s i)=1.
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
           unfold v92,v81,v62,v63,v93; rewrite accept,a,hi,full; clean.
           repeat rewrite normalize by lia.
           destruct (bit_cases (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin1 i)) 63)) as [h|h]; unfold sign64; rewrite h; repeat split; reflexivity.
Qed.
Definition multiplicand i := if word 4 (nio_5Freq_5Fbits_5Ffn i)=?1
  then SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin2 i) else word 64 (nio_5Freq_5Fbits_5Fin2 i).
Lemma divisor_value i : SignedWords.signed 65 (divisorBits i)=multiplicand i.
Proof.
  unfold divisorBits,divisorSign,multiplicand; destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?1).
  - change (SignedWords.signed 65 (MulDivSignedBits.MulDivSignedBits.extended65 (nio_5Freq_5Fbits_5Fin2 i))=SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin2 i)).
    rewrite MulDivSignedBits.MulDivSignedBits.extended_signed; apply SignedWords.signed_extend; lia.
  - change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l,SignedWords.signed_normal by lia.
    apply SignedWords.signed_small; [lia|].
    pose proof (MulDivMultiply.MulDivMultiply.bounds 64 (nio_5Freq_5Fbits_5Fin2 i) ltac:(lia)); change (2^(65-1)) with (2^64); lia.
Qed.
Lemma multiplicand_bound i : -(2^64)<multiplicand i<2^64.
Proof.
  unfold multiplicand; destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?1).
  - pose proof (SignedWords.signed_range 64 (nio_5Freq_5Fbits_5Fin2 i) ltac:(lia)); change (2^(64-1)) with 9223372036854775808 in H; change (2^64) with 18446744073709551616; lia.
  - pose proof (MulDivMultiply.MulDivMultiply.bounds 64 (nio_5Freq_5Fbits_5Fin2 i) ltac:(lia)); change (2^64) with 18446744073709551616 in *; lia.
Qed.
Lemma sign_quotient x : sign64 x=word 64 x/2^63.
Proof.
  unfold sign64; rewrite Z.shiftr_div_pow2 by lia; apply Words.word_small.
  pose proof (MulDivMultiply.MulDivMultiply.bounds 64 x ltac:(lia)) as hx.
  split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  change (2^64) with 18446744073709551616 in hx; change (2^1) with 2; change (2^63) with 9223372036854775808; lia.
Qed.
Local Opaque run step.
Theorem accepted_product s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : MulDivTiming.MulDivTiming.active inputs 65) :
  SignedWords.signed 129 (MulDivMultiply.MulDivMultiply.packed (run s inputs 65))=
    SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin1 (inputs O))*multiplicand (inputs O).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation full) as [st [ct [dv [sh [neg rest]]]]].
  pose proof (MulDivMultiply.MulDivMultiply.bounds 64 (nio_5Freq_5Fbits_5Fin1 (inputs O)) ltac:(lia)) as ha.
  destruct (MulDivMultiplyCapture.MulDivMultiplyCapture.captured_layout (step s (inputs O)) _ ha sh) as [pk sg].
  rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs 64).
  rewrite (SignedWords.signed_from_bits 64 (nio_5Freq_5Fbits_5Fin1 (inputs O))) by lia.
  change (64-1) with 63; fold (sign64 (nio_5Freq_5Fbits_5Fin1 (inputs O))).
  apply MulDivMultiplySignedProduct.MulDivMultiplySignedProduct.product_from_packed.
  - exact ha.
  - apply multiplicand_bound.
  - rewrite st; reflexivity.
  - rewrite ct; reflexivity.
  - rewrite dv; apply divisor_value.
  - exact sg.
  - exact pk.
  - rewrite neg; unfold sign64; apply normalize; lia.
  - right; apply sign_quotient.
  - intros t ht; apply live; lia.
Qed.
End MulDivMulSignedCapture.
Print Assumptions MulDivMulSignedCapture.capture.
Print Assumptions MulDivMulSignedCapture.accepted_product.
