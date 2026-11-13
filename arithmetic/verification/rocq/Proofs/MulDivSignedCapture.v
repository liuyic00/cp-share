From Coq Require Import ZArith Lia Bool.
From Proofs Require Import Words MulDivControl MulDivRefinement MulDivSignedInputEdge MulDivSignedBits MulDivSignedOperands.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivSignedInputEdge.MulDivSignedInputEdge MulDivSignedBits.MulDivSignedBits MulDivSignedOperands.MulDivSignedOperands.
Open Scope Z_scope.
Module MulDivSignedCapture.
Definition needsNegation i := orb (inputSign i (nio_5Freq_5Fbits_5Fin1 i)=?1) (inputSign i (nio_5Freq_5Fbits_5Fin2 i)=?1).
Definition outputNegative i := if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then inputSign i (nio_5Freq_5Fbits_5Fin1 i)
  else if inputSign i (nio_5Freq_5Fbits_5Fin1 i)=?inputSign i (nio_5Freq_5Fbits_5Fin2 i) then 0 else 1.
Lemma sign_cases i x : inputSign i x=0 \/ inputSign i x=1.
Proof. rewrite <- operand_sign; unfold sign64; apply bit_cases. Qed.
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  v6 s i=0 /\ v20 s i=inputSign i (nio_5Freq_5Fbits_5Fin1 i) /\
  v29 s i=inputSign i (nio_5Freq_5Fbits_5Fin2 i) /\
  v79 s i=(if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0).
Proof.
  assert (a : v19 s i=inputSign i (nio_5Freq_5Fbits_5Fin1 i)).
  { unfold v19,v18,v17,inputSign,sign64; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); apply normalize; lia. }
  assert (b : v28 s i=inputSign i (nio_5Freq_5Fbits_5Fin2 i)).
  { unfold v28,v27,v26,inputSign,sign64; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); apply normalize; lia. }
  unfold v79,v78,v77,v76,v75,v74,v29,v25,v24,v23,v22,v21,v20,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3.
  rewrite a,b; destruct operation as [op|op]; rewrite op; clean;
    destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [ha|ha];
    destruct (sign_cases i (nio_5Freq_5Fbits_5Fin2 i)) as [hb|hb]; rewrite ha,hb; repeat split; reflexivity.
Qed.
Lemma capture_control s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  r0_nstate (step s i)=(if needsNegation i then 1 else 3) /\
  r3_ncount (step s i)=0 /\ r6_nresHi (step s i)=0 /\
  r4_nneg_5Fout (step s i)=outputNegative i /\
  r1_nreq_5Fdw (step s i)=word 1 (nio_5Freq_5Fbits_5Fdw i) /\
  r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\
  r5_nisHi (step s i)=(if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0).
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [a [b hi]]].
  split.
  - cbn [step r0_nstate]; rewrite reset; unfold v61,v34,v33,v32,v30,v31,v8,v7; rewrite accept,mul,a,b.
    unfold needsNegation; destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [ha|ha];
      destruct (sign_cases i (nio_5Freq_5Fbits_5Fin2 i)) as [hb|hb]; rewrite ha,hb; reflexivity.
  - split.
    + cbn [step r3_ncount]; unfold v73,v67,v66,v65,v8; rewrite accept,mul; reflexivity.
    + split.
      * cbn [step r6_nresHi]; unfold v100,v94,v31; rewrite accept; reflexivity.
      * cbn [step r4_nneg_5Fout r1_nreq_5Fdw r2_nreq_5Ftag r5_nisHi].
        unfold v92,v81,v80,v62,v63,v93; rewrite accept,a,b,hi.
        unfold outputNegative; destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?6);
          destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [ha|ha];
          destruct (sign_cases i (nio_5Freq_5Fbits_5Fin2 i)) as [hb|hb]; rewrite ha,hb; clean;
          repeat rewrite normalize by lia; repeat split; reflexivity.
Qed.
Lemma extended_join i x :
  word 65 (Z.shiftl (Z.shiftl (inputSign i x) 32+highWord i x) 32+
    word 32 (Z.shiftr (word 64 x) 0))=extended65 (operand i x).
Proof.
  unfold extended65; rewrite operand_sign,operand_normal.
  rewrite <- (joined_exact i x).
  rewrite !Z.shiftl_mul_pow2 by lia; f_equal.
  change (2^32) with 4294967296; change (2^64) with 18446744073709551616; ring.
Qed.
Lemma capture_data s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  r7_ndivisor (step s i)=extended65 (operand i (nio_5Freq_5Fbits_5Fin2 i)) /\
  packed (step s i)=operand i (nio_5Freq_5Fbits_5Fin1 i).
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [a [b hi]]].
  split.
  - cbn [step r7_ndivisor]; unfold v109; rewrite accept; cbn [Z.eqb Pos.eqb].
    unfold v105,v104,v103,v102,v101; rewrite b.
    change (word 65 (word 65 (Z.shiftl (Z.shiftl (inputSign i (nio_5Freq_5Fbits_5Fin2 i)) 32+highWord i (nio_5Freq_5Fbits_5Fin2 i)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)))=extended65 (operand i (nio_5Freq_5Fbits_5Fin2 i))).
    rewrite normalize by lia; apply extended_join.
  - unfold packed; cbn [step r8_nremainder]; unfold v151; rewrite accept; cbn [Z.eqb Pos.eqb].
    unfold v115,v114,v113,v112,v111,v110; rewrite a.
    change (word 66 0) with 0; change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l.
    repeat rewrite narrow by lia.
    change (word 129 (Z.shiftl (highWord i (nio_5Freq_5Fbits_5Fin1 i)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin1 i)) 0))=operand i (nio_5Freq_5Fbits_5Fin1 i)).
    rewrite joined_exact.
    rewrite <- (operand_normal i (nio_5Freq_5Fbits_5Fin1 i)) at 1.
    transitivity (word 64 (operand i (nio_5Freq_5Fbits_5Fin1 i))); [apply Words.word_widen; lia|apply operand_normal].
Qed.
End MulDivSignedCapture.
Print Assumptions MulDivSignedCapture.capture_control.
Print Assumptions MulDivSignedCapture.capture_data.
