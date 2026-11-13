From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits MulDivCheckedProjection.
From Generated Require Import MulDiv MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked.
Open Scope Z_scope.
Module MulDivCheckedHistory.
Lemma normalize w x (hw : 0<=w) : word w (word w x)=word w x.
Proof. exact (Words.word_idem w x hw). Qed.
Lemma bounds w x (hw : 0<=w) : 0<=word w x<2^w.
Proof. exact (Words.word_bound w x hw). Qed.
Lemma bit_cases x : word 1 x=0 \/ word 1 x=1.
Proof. pose proof (bounds 1 x ltac:(lia)); change (2^1) with 2 in H; lia. Qed.
Lemma narrow w k x (hk : 0<=k) (fits : k<=w) : word k (word w x)=word k x.
Proof.
  pose proof (WordBits.extract_normal w k 0 x hk ltac:(lia) ltac:(lia)) as h.
  rewrite !Z.shiftr_0_r in h; exact h.
Qed.
Definition captured s := MulDiv.nMulDiv.mkInputs 0 1 (word 4 (r11_ncontractFn s))
  (word 1 (r12_ncontractDw s)) (word 64 (r13_ncontractA s)) (word 64 (r14_ncontractB s))
  (word 5 (r15_ncontractTag s)) 0 0.
Definition requestView i := MulDiv.nMulDiv.mkInputs 0 1 (word 4 (nio_5Freq_5Fbits_5Ffn i))
  (word 1 (nio_5Freq_5Fbits_5Fdw i)) (word 64 (nio_5Freq_5Fbits_5Fin1 i)) (word 64 (nio_5Freq_5Fbits_5Fin2 i))
  (word 5 (nio_5Freq_5Fbits_5Ftag i)) 0 0.
Definition legal i := word 4 (nio_5Freq_5Fbits_5Ffn i)<8 /\
  (word 1 (nio_5Freq_5Fbits_5Fdw i)=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ 4<=word 4 (nio_5Freq_5Fbits_5Ffn i)).
Lemma accept s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1) : v2 s i=1.
Proof. unfold v2,v1,v0; rewrite idle,valid; reflexivity. Qed.
Lemma no_accept s i (absent : word 3 (r0_nstate s)<>0 \/ word 1 (nio_5Freq_5Fvalid i)=0) : v2 s i=0.
Proof.
  unfold v2,v1,v0; change (word 3 0) with 0.
  destruct absent as [busy|invalid].
  - assert (neq : (word 3 (r0_nstate s)=?0)=false) by (apply Z.eqb_neq; exact busy).
    rewrite neq; reflexivity.
  - rewrite invalid,Z.land_0_r; reflexivity.
Qed.
Theorem capture s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1) :
  captured (step s i)=requestView i.
Proof.
  unfold captured,requestView; cbn [step r11_ncontractFn r12_ncontractDw r13_ncontractA r14_ncontractB r15_ncontractTag].
  unfold v169,v170,v171,v172,v173; rewrite accept by assumption; cbn [Z.eqb Pos.eqb].
  repeat rewrite normalize by lia; reflexivity.
Qed.
Theorem hold s i (absent : word 3 (r0_nstate s)<>0 \/ word 1 (nio_5Freq_5Fvalid i)=0) :
  captured (step s i)=captured s.
Proof.
  unfold captured; cbn [step r11_ncontractFn r12_ncontractDw r13_ncontractA r14_ncontractB r15_ncontractTag].
  unfold v169,v170,v171,v172,v173; rewrite no_accept by exact absent; cbn [Z.eqb].
  repeat rewrite normalize by lia; reflexivity.
Qed.
Theorem reset_monitors s i (reset : word 1 (nreset i)=1) :
  r9_ncontractPending (step s i)=0 /\ r10_ncontractAge (step s i)=0 /\
  r16_ncontractWasNegated (step s i)=0 /\ r21_ncontractWasStalled (step s i)=0.
Proof. cbn [step r9_ncontractPending r10_ncontractAge r16_ncontractWasNegated r21_ncontractWasStalled]; rewrite reset; repeat split; reflexivity. Qed.
Theorem capture_age s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1) :
  r10_ncontractAge (step s i)=0.
Proof.
  cbn [step r10_ncontractAge]; unfold v168; rewrite accept by assumption.
  destruct (word 1 (nreset i)=?1); reflexivity.
Qed.
Theorem capture_pending s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) (operation : legal i) :
  r9_ncontractPending (step s i)=1.
Proof.
  cbn [step r9_ncontractPending]; rewrite reset; unfold v163; rewrite accept by assumption; cbn [Z.eqb Pos.eqb].
  unfold v160,v159,v158,v157,v156,v155,v154,v153,v152,v31,v15; rewrite kill.
  destruct operation as [range width].
  pose proof (bounds 4 (nio_5Freq_5Fbits_5Ffn i) ltac:(lia)) as fnBound.
  assert (cases : word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=2 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=3 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=6 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) by lia.
  destruct (bit_cases (nio_5Freq_5Fbits_5Fdw i)) as [dw|dw]; rewrite dw in *;
    destruct cases as [h|[h|[h|[h|[h|[h|[h|h]]]]]]]; rewrite h in *; try (exfalso; lia); reflexivity.
Qed.
Definition witness s := (word 1 (r16_ncontractWasNegated s),word 64 (r17_ncontractQuotient s),word 64 (r18_ncontractResidue s)).
Theorem capture_witness s i (negating : word 3 (r0_nstate s)=5) (reset : word 1 (nreset i)=0) :
  witness (step s i)=(1,word 64 (r8_nremainder s),word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65)).
Proof.
  assert (absent : v2 s i=0) by (apply no_accept; left; lia).
  assert (flag : v53 s i=1) by (unfold v53,v52; rewrite negating; reflexivity).
  unfold witness; cbn [step r16_ncontractWasNegated r17_ncontractQuotient r18_ncontractResidue].
  rewrite reset; unfold v176,v175,v174,v178,v177,v31,v119,v144; rewrite absent,flag; cbn [Z.eqb Pos.eqb].
  destruct (bit_cases (r16_ncontractWasNegated s)) as [h|h]; rewrite h;
    repeat rewrite normalize by lia; rewrite Z.shiftr_0_r;
    rewrite narrow by lia; reflexivity.
Qed.
Theorem hold_witness s i (notNegating : word 3 (r0_nstate s)<>5)
  (absent : word 3 (r0_nstate s)<>0 \/ word 1 (nio_5Freq_5Fvalid i)=0)
  (reset : word 1 (nreset i)=0) : witness (step s i)=witness s.
Proof.
  assert (accept : v2 s i=0) by (apply no_accept; exact absent).
  assert (flag : v53 s i=0).
  { unfold v53,v52; change (word 3 5) with 5.
    assert (neq : (word 3 (r0_nstate s)=?5)=false) by (apply Z.eqb_neq; exact notNegating).
    rewrite neq; reflexivity. }
  unfold witness; cbn [step r16_ncontractWasNegated r17_ncontractQuotient r18_ncontractResidue].
  rewrite reset; unfold v176,v175,v174,v178,v177,v31; rewrite accept,flag; cbn [Z.eqb Pos.eqb].
  destruct (bit_cases (r16_ncontractWasNegated s)) as [h|h]; rewrite h;
    repeat rewrite normalize by lia; reflexivity.
Qed.
End MulDivCheckedHistory.
Print Assumptions MulDivCheckedHistory.capture.
Print Assumptions MulDivCheckedHistory.hold.
Print Assumptions MulDivCheckedHistory.reset_monitors.
Print Assumptions MulDivCheckedHistory.capture_pending.
Print Assumptions MulDivCheckedHistory.capture_witness.
Print Assumptions MulDivCheckedHistory.hold_witness.
