From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivTiming MulDivMulWordBalance MulDivControl MulDivRefinement MulDivSignedInputEdge MulDivSignedBits MulDivSignedOperands MulDivSignedCapture MulDivMultiplyCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivSignedInputEdge.MulDivSignedInputEdge MulDivSignedBits.MulDivSignedBits MulDivSignedOperands.MulDivSignedOperands MulDivSignedCapture.MulDivSignedCapture.
Open Scope Z_scope.
Module MulDivMulWordCapture.
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=0) :
  v6 s i=1 /\ v20 s i=inputSign i (nio_5Freq_5Fbits_5Fin1 i) /\
  v29 s i=inputSign i (nio_5Freq_5Fbits_5Fin2 i) /\
  v79 s i=0.
Proof.
  assert (a : v19 s i=inputSign i (nio_5Freq_5Fbits_5Fin1 i)).
  { unfold v19,v18,v17,inputSign,sign64; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); apply normalize; lia. }
  assert (b : v28 s i=inputSign i (nio_5Freq_5Fbits_5Fin2 i)).
  { unfold v28,v27,v26,inputSign,sign64; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); apply normalize; lia. }
  unfold v79,v78,v77,v76,v75,v74,v29,v25,v24,v23,v22,v21,v20,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3.
  rewrite a,b; rewrite operation; clean;
    destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [ha|ha];
    destruct (sign_cases i (nio_5Freq_5Fbits_5Fin2 i)) as [hb|hb]; rewrite ha,hb; repeat split; reflexivity.
Qed.
Lemma capture_control s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=0)
  (mode : word 1 (nio_5Freq_5Fbits_5Fdw i)=0) :
  r0_nstate (step s i)=2 /\ r3_ncount (step s i)=32 /\
  r1_nreq_5Fdw (step s i)=0 /\ r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\ r5_nisHi (step s i)=0.
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [a [b hi]]].
  split.
  - cbn [step r0_nstate]; rewrite reset; unfold v61,v34,v7; rewrite accept,mul; reflexivity.
  - split.
    + cbn [step r3_ncount]; unfold v73,v67,v66,v65,v64,v31,v8; rewrite accept,mul,mode; reflexivity.
    + cbn [step r1_nreq_5Fdw r2_nreq_5Ftag r5_nisHi]; unfold v62,v63,v93; rewrite accept,mode,hi; clean; repeat rewrite normalize by lia; repeat split; reflexivity.
Qed.
Lemma capture_data s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=0) :
  r7_ndivisor (step s i)=extended65 (operand i (nio_5Freq_5Fbits_5Fin2 i)) /\
  r8_nremainder (step s i)=operand i (nio_5Freq_5Fbits_5Fin1 i).
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [a [b hi]]].
  split.
  - cbn [step r7_ndivisor]; unfold v109; rewrite accept; cbn [Z.eqb Pos.eqb].
    unfold v105,v104,v103,v102,v101; rewrite b.
    change (word 65 (word 65 (Z.shiftl (Z.shiftl (inputSign i (nio_5Freq_5Fbits_5Fin2 i)) 32+highWord i (nio_5Freq_5Fbits_5Fin2 i)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)))=extended65 (operand i (nio_5Freq_5Fbits_5Fin2 i))).
    rewrite normalize by lia; apply extended_join.
  - cbn [step r8_nremainder]; unfold v151; rewrite accept; cbn [Z.eqb Pos.eqb].
    unfold v115,v114,v113,v112,v111,v110; rewrite a.
    change (word 66 0) with 0; change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l.
    repeat rewrite normalize by lia.
    change (word 130 (Z.shiftl (highWord i (nio_5Freq_5Fbits_5Fin1 i)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin1 i)) 0))=operand i (nio_5Freq_5Fbits_5Fin1 i)).
    rewrite joined_exact.
    rewrite <- (operand_normal i (nio_5Freq_5Fbits_5Fin1 i)) at 1.
    transitivity (word 64 (operand i (nio_5Freq_5Fbits_5Fin1 i))); [apply Words.word_widen; lia|apply operand_normal].
Qed.
Lemma divisor_value i x (mode : word 1 (nio_5Freq_5Fbits_5Fdw i)=0) :
  SignedWords.signed 65 (extended65 (operand i x))=SignedWords.signed 32 x.
Proof.
  rewrite extended_signed,SignedWords.signed_extend by lia.
  unfold operand; rewrite mode; cbn [Z.eqb].
  apply SignedWords.signed_extend; lia.
Qed.
Lemma operand_low i x (mode : word 1 (nio_5Freq_5Fbits_5Fdw i)=0) : word 32 (operand i x)=word 32 x.
Proof.
  unfold operand; rewrite mode; cbn [Z.eqb]; rewrite narrow by lia.
  apply SignedWords.word_signed; lia.
Qed.
Local Opaque step run.
Theorem accepted_slice s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (mode : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=0)
  (live : MulDivTiming.MulDivTiming.active inputs 33) :
  word 32 (Z.shiftr (MulDivMultiply.MulDivMultiply.packed (run s inputs 33)) 32)=
    word 32 (SignedWords.signed 32 (nio_5Freq_5Fbits_5Fin2 (inputs O))*word 32 (nio_5Freq_5Fbits_5Fin1 (inputs O))).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture_control s (inputs O) idle valid hr operation mode) as [st [ct rest]].
  destruct (capture_data s (inputs O) idle valid operation) as [dv sh].
  assert (ha : 0<=operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O))<2^64).
  { unfold operand; rewrite mode; apply MulDivMultiply.MulDivMultiply.bounds; lia. }
  destruct (MulDivMultiplyCapture.MulDivMultiplyCapture.captured_layout (step s (inputs O)) _ ha sh) as [pk sg].
  assert (hb : -(2^64)<SignedWords.signed 32 (nio_5Freq_5Fbits_5Fin2 (inputs O))<2^64).
  { pose proof (SignedWords.signed_range 32 (nio_5Freq_5Fbits_5Fin2 (inputs O)) ltac:(lia)); change (2^(32-1)) with 2147483648 in H; change (2^64) with 18446744073709551616; lia. }
  pose proof (MulDivMulWordBalance.MulDivMulWordBalance.word_slice (step s (inputs O)) (fun t => inputs (S t))
    _ _ ha hb ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(rewrite dv; apply divisor_value; exact mode) sg pk ltac:(intros t ht; apply live; lia)) as result.
  rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs 32),result,operand_low by exact mode; reflexivity.
Qed.
End MulDivMulWordCapture.
Print Assumptions MulDivMulWordCapture.capture_control.
Print Assumptions MulDivMulWordCapture.capture_data.
Print Assumptions MulDivMulWordCapture.accepted_slice.
