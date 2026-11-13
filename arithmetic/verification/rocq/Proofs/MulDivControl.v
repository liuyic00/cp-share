From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv.
Open Scope Z_scope.
Module MulDivControl.
Lemma normalize w x (hw : 0<=w) : word w (word w x)=word w x.
Proof. exact (Words.word_idem w x hw). Qed.
Ltac constants := repeat match goal with
  | |- context[word ?w ?x] => integer_literal w; integer_literal x;
    let y := eval vm_compute in (word w x) in change (word w x) with y
  end.
Ltac clean := repeat (progress (constants; rewrite ?Z.land_0_r, ?Z.land_0_l, ?Z.lor_0_r, ?Z.lor_0_l; cbn [Z.eqb Pos.eqb Z.land Z.lor Z.lxor Pos.land Pos.lor Pos.lxor Z.of_N])).
Ltac control := unfold v61, v60, v59, v58, v57, v56, v55, v54, v53, v52, v51, v50, v49,
  v48, v47, v46, v45, v44, v43, v42, v41, v40, v39, v38, v37, v36, v35,
  v31, v7, v4, v2, v1, v0.
Lemma reset_ready s i (hr : word 1 (nreset i)=1) : r0_nstate (step s i)=0.
Proof. cbn [step r0_nstate]; rewrite hr; reflexivity. Qed.
Lemma done_valid s i (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7) :
  nio_5Fresp_5Fvalid (observe s i)=1.
Proof. cbn [observe nio_5Fresp_5Fvalid]; unfold v38, v37, v36, v35, v4; destruct done as [h|h]; rewrite h; reflexivity. Qed.
Lemma mul_state s i (hs : word 3 (r0_nstate s)=2)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=if word 7 (r3_ncount s)=?63 then 6 else 2.
Proof.
  cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hk; clean.
  destruct (word 7 (r3_ncount s)=?63); clean; reflexivity.
Qed.
Lemma div_state s i (hs : word 3 (r0_nstate s)=3)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=if word 7 (r3_ncount s)=?64 then (if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7) else 3.
Proof.
  cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hk; clean.
  destruct (word 7 (r3_ncount s)=?64); clean; [|reflexivity].
  destruct (Words.bit_cases (r4_nneg_5Fout s)) as [h|h];
    change (Words.word 1 (r4_nneg_5Fout s)) with (word 1 (r4_nneg_5Fout s)) in h;
    rewrite h; reflexivity.
Qed.
Lemma negate_inputs_state s i (hs : word 3 (r0_nstate s)=1)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) : r0_nstate (step s i)=3.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hk; clean; reflexivity. Qed.
Lemma negate_output_state s i (hs : word 3 (r0_nstate s)=5)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) : r0_nstate (step s i)=7.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hk; clean; reflexivity. Qed.
Lemma compute_count s i (hs : word 3 (r0_nstate s)=2 \/ word 3 (r0_nstate s)=3) :
  r3_ncount (step s i)=word 7 (word 7 (r3_ncount s)+1).
Proof.
  cbn [step r3_ncount]; unfold v73, v72, v71, v70, v69, v68, v48, v42, v41, v7, v2, v1, v0.
  destruct hs as [h|h]; rewrite h; clean; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma negate_inputs_count s i (hs : word 3 (r0_nstate s)=1) :
  r3_ncount (step s i)=word 7 (r3_ncount s).
Proof.
  cbn [step r3_ncount]; unfold v73, v72, v71, v48, v42, v41, v7, v2, v1, v0.
  rewrite hs; clean; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma busy_no_accept s i (hs : word 3 (r0_nstate s)<>0) : v2 s i=0.
Proof.
  unfold v2, v1, v0; change (word 3 0) with 0.
  assert (h : (word 3 (r0_nstate s)=?0)=false) by (apply Z.eqb_neq; exact hs).
  rewrite h; reflexivity.
Qed.
Theorem kill_busy s i (hs : word 3 (r0_nstate s)<>0)
  (hk : word 1 (nio_5Fkill i)=1) : r0_nstate (step s i)=0.
Proof.
  assert (h2 : v2 s i=0) by (apply busy_no_accept; exact hs).
  assert (h39 : v39 s i=0 \/ v39 s i=1) by (unfold v39; apply Words.bit_cases).
  cbn [step r0_nstate]; destruct (word 1 (nreset i)=?1); [reflexivity|].
  unfold v61, v60, v40; rewrite h2, hk; destruct h39 as [h|h]; rewrite h; reflexivity.
Qed.
Lemma busy_request_metadata s i (hs : word 3 (r0_nstate s)<>0) :
  r1_nreq_5Fdw (step s i)=word 1 (r1_nreq_5Fdw s) /\
  r2_nreq_5Ftag (step s i)=word 5 (r2_nreq_5Ftag s).
Proof.
  cbn [step r1_nreq_5Fdw r2_nreq_5Ftag]; unfold v62, v63; rewrite busy_no_accept by exact hs.
  clean; repeat rewrite normalize by lia; split; reflexivity.
Qed.
Lemma bit_cases x : word 1 x=0 \/ word 1 x=1.
Proof. exact (Words.bit_cases x). Qed.
Lemma v32_bit s i : v32 s i=0 \/ v32 s i=1.
Proof. unfold v32; apply bit_cases. Qed.
Lemma v65_bit s i : v65 s i=0 \/ v65 s i=1.
Proof. unfold v65; apply bit_cases. Qed.
Local Opaque v6 v32 v65.
Lemma acceptance s i (hs : word 3 (r0_nstate s)=0)
  (hv : word 1 (nio_5Freq_5Fvalid i)=1) (hr : word 1 (nreset i)=0) :
  (r0_nstate (step s i)=2 \/ r0_nstate (step s i)=1 \/ r0_nstate (step s i)=3) /\
  (r3_ncount (step s i)=0 \/ r3_ncount (step s i)=32).
Proof.
  assert (accept : v2 s i=1).
  { unfold v2, v1, v0; rewrite hs, hv; reflexivity. }
  split.
  - cbn [step r0_nstate]; rewrite hr; unfold v61; rewrite accept.
    unfold v34; destruct (v6 s i=?1); [left; reflexivity|].
    unfold v33, v8, v31.
    assert (bit : v32 s i=0 \/ v32 s i=1) by apply v32_bit.
    destruct bit as [h|h]; rewrite h; [right; left|right; right]; reflexivity.
  - cbn [step r3_ncount]; unfold v73; rewrite accept; unfold v67, v8, v66.
    assert (bit : v65 s i=0 \/ v65 s i=1) by apply v65_bit.
    destruct bit as [h|h]; rewrite h; [left|right]; reflexivity.
Qed.
End MulDivControl.
Print Assumptions MulDivControl.mul_state.
Print Assumptions MulDivControl.div_state.
Print Assumptions MulDivControl.kill_busy.
