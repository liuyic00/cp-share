From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivRefinement MulDivTiming MulDivUnsignedCapture MulDivMultiply MulDivMultiplyRun.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivUnsignedCapture.MulDivUnsignedCapture MulDivMultiply.MulDivMultiply.
Open Scope Z_scope.
Module MulDivMultiplyCapture.
Lemma decode s i (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=3) :
  v6 s i=1 /\ v20 s i=0 /\ v29 s i=0 /\ v79 s i=1.
Proof.
  unfold v79,v78,v77,v76,v75,v74,v29,v25,v24,v23,v22,v21,v20,v16,v14,v15,v13,v12,v11,v10,v9,v6,v5,v4,v3.
  rewrite operation; clean; repeat split; reflexivity.
Qed.
Lemma capture s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=3)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw i)=1) :
  r0_nstate (step s i)=2 /\ r3_ncount (step s i)=0 /\
  r7_ndivisor (step s i)=operand i (nio_5Freq_5Fbits_5Fin2 i) /\
  r8_nremainder (step s i)=operand i (nio_5Freq_5Fbits_5Fin1 i) /\
  r4_nneg_5Fout (step s i)=0 /\
  r1_nreq_5Fdw (step s i)=word 1 (nio_5Freq_5Fbits_5Fdw i) /\
  r2_nreq_5Ftag (step s i)=word 5 (nio_5Freq_5Fbits_5Ftag i) /\
  r5_nisHi (step s i)=1.
Proof.
  assert (accept : v2 s i=1) by (unfold v2,v1,v0; rewrite idle,valid; reflexivity).
  destruct (decode s i operation) as [mul [aSign [dSign high]]].
  split.
  - cbn [step r0_nstate]; rewrite reset; unfold v61; rewrite accept.
    unfold v34,v33,v32,v30,v31,v8; rewrite mul,aSign,dSign; reflexivity.
  - split.
    + cbn [step r3_ncount]; unfold v73; rewrite accept; unfold v67,v66,v65,v64,v31,v8; rewrite mul,full; reflexivity.
    + split.
      * cbn [step r7_ndivisor]; unfold v109; rewrite accept; unfold v105,v104,v103,v102,v101; rewrite dSign.
        change (word 32 (repeatWord 32 1 0)) with 0.
        change (word 65 (word 65 (Z.shiftl (Z.shiftl 0 32+word 32 (if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 32) else 0)) 32+word 32 (Z.shiftr (word 64 (nio_5Freq_5Fbits_5Fin2 i)) 0)))=operand i (nio_5Freq_5Fbits_5Fin2 i)).
        change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l,normalize,split_operand by lia.
        apply Words.word_small; pose proof (operand_bound i (nio_5Freq_5Fbits_5Fin2 i)); change (0<=operand i (nio_5Freq_5Fbits_5Fin2 i)<36893488147419103232); change (2^64) with 18446744073709551616 in H; lia.
      * split.
        -- cbn [step r8_nremainder]; unfold v151; rewrite accept; cbn [Z.eqb Pos.eqb].
           unfold v115,v114,v113,v112,v111,v110; rewrite aSign.
           change (word 66 0) with 0; change (word 32 (repeatWord 32 1 0)) with 0.
           change (Z.shiftl 0 32) with 0; rewrite Z.add_0_l.
           repeat rewrite normalize by lia; rewrite split_operand.
           apply Words.word_small; pose proof (operand_bound i (nio_5Freq_5Fbits_5Fin1 i)); change (0<=operand i (nio_5Freq_5Fbits_5Fin1 i)<1361129467683753853853498429727072845824); change (2^64) with 18446744073709551616 in H; lia.
        -- cbn [step r4_nneg_5Fout r1_nreq_5Fdw r2_nreq_5Ftag r5_nisHi].
           unfold v92,v81,v80,v62,v63,v93; rewrite accept,aSign,dSign,high.
           clean; repeat rewrite normalize by lia; repeat split; reflexivity.
Qed.
Lemma captured_layout s a (ha : 0<=a<2^64) (initial : r8_nremainder s=a) :
  packed s=a /\ sign s=0.
Proof.
  assert (w130 : word 130 a=a) by (apply Words.word_small; change (2^64) with 18446744073709551616 in ha; change (0<=a<1361129467683753853853498429727072845824); lia).
  assert (w64 : word 64 a=a) by (apply Words.word_small; exact ha).
  assert (shift64 : Z.shiftr a 64=0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; exact ha).
  assert (shift65 : Z.shiftr a 65=0).
  { rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; change (2^64) with 18446744073709551616 in ha; change (0<=a<36893488147419103232); lia. }
  unfold packed,sign; rewrite initial,w130,w64,shift64,shift65.
  change (word 65 0) with 0; change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l; split; [|reflexivity].
  apply Words.word_small; change (2^64) with 18446744073709551616 in ha; change (0<=a<680564733841876926926749214863536422912); lia.
Qed.
Local Opaque run step.
Theorem accepted_product s inputs
  (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=3)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : MulDivTiming.MulDivTiming.active inputs 65) :
  packed (run s inputs 65)=word 64 (nio_5Freq_5Fbits_5Fin1 (inputs O))*word 64 (nio_5Freq_5Fbits_5Fin2 (inputs O)).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation full) as [st [ct [dv [sh [neg rest]]]]].
  unfold operand in dv,sh; rewrite full in dv,sh; cbn [Z.eqb Pos.eqb] in dv,sh.
  pose proof (bounds 64 (nio_5Freq_5Fbits_5Fin1 (inputs O)) ltac:(lia)) as ha.
  pose proof (bounds 64 (nio_5Freq_5Fbits_5Fin2 (inputs O)) ltac:(lia)) as hb.
  destruct (captured_layout (step s (inputs O)) _ ha sh) as [pk sg].
  rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs 64).
  apply MulDivMultiplyRun.MulDivMultiplyRun.unsigned_product.
  - exact ha.
  - exact hb.
  - rewrite st; reflexivity.
  - rewrite ct; reflexivity.
  - rewrite dv; apply Words.word_widen; lia.
  - exact sg.
  - rewrite neg; reflexivity.
  - exact pk.
  - intros t ht; apply live; lia.
Qed.
End MulDivMultiplyCapture.
Print Assumptions MulDivMultiplyCapture.capture.
Print Assumptions MulDivMultiplyCapture.accepted_product.
