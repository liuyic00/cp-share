From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivSimulation MulDivMetadata MulDivDivision MulDivRefinement MulDivInitialization MulDivZero.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivSimulation.MulDivSimulation MulDivMetadata.MulDivMetadata.
Open Scope Z_scope.
Module MulDivSignedExecution.
Definition effectiveNegative d hi negative := if word 64 d=?0 then
  (if word 1 hi=?1 then word 1 negative else 0) else word 1 negative.
Lemma later_flag s i (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)<>0) :
  r4_nneg_5Fout (step s i)=word 1 (r4_nneg_5Fout s).
Proof.
  assert (zero : v83 s i=0).
  { unfold v83,v82; change (word 7 0) with 0.
    assert (h : (word 7 (r3_ncount s)=?0)=false) by (apply Z.eqb_neq; exact count).
    rewrite h; reflexivity. }
  cbn [step r4_nneg_5Fout]; unfold v92; rewrite busy_no_accept by lia.
  unfold v91,v90,v89,v31; rewrite zero; clean.
  destruct (bit_cases (r4_nneg_5Fout s)) as [h|h]; rewrite h; reflexivity.
Qed.
Theorem flags_run n s inputs (state : word 3 (r0_nstate s)=3)
  (positive : 0<word 7 (r3_ncount s)) (remaining : word 7 (r3_ncount s)+Z.of_nat n<=65)
  (live : active inputs n) :
  metadata (run s inputs n)=metadata s /\ word 1 (r4_nneg_5Fout (run s inputs n))=word 1 (r4_nneg_5Fout s).
Proof.
  induction n as [|n IH]; [split; reflexivity|].
  destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [meta flag].
  destruct (div_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  change (metadata (step (run s inputs n) (inputs n))=metadata s /\
    word 1 (r4_nneg_5Fout (step (run s inputs n) (inputs n)))=word 1 (r4_nneg_5Fout s)).
  split; [rewrite metadata_edge by exact st; exact meta|].
  rewrite later_flag by (assumption || lia); rewrite normalize by lia; exact flag.
Qed.
Lemma last_signed_edge s i (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=64) (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=(if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7) /\
  r6_nresHi (step s i)=word 1 (r5_nisHi s).
Proof.
  split; [rewrite (div_state _ _ state hr hk),count; reflexivity|].
  cbn [step r6_nresHi]; unfold v100,v99,v98,v97,v96,v95,v94,v51,v50,v49,v48,v42,v41,v7,v44,v43,v53,v52,v31.
  rewrite busy_no_accept by lia; rewrite state,count; clean.
  destruct (bit_cases (r5_nisHi s)) as [h|h]; rewrite h; reflexivity.
Qed.
Lemma first_flag s i a d (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (initial : MulDivRefinement.MulDivRefinement.packed s=word 64 a) :
  r4_nneg_5Fout (step s i)=effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s).
Proof.
  assert (candidateZero : MulDivDivision.MulDivDivision.candidate (r8_nremainder s)=0).
  { rewrite MulDivRefinement.MulDivRefinement.candidate_packed.
    change (RD.candidate (MulDivRefinement.MulDivRefinement.packed s)=0).
    rewrite initial; apply MulDivInitialization.MulDivInitialization.initial_candidate. }
  assert (sign : v86 s i=if word 64 d=?0 then 0 else 1).
  { change (MulDivDivision.MulDivDivision.signBit (r8_nremainder s) (r7_ndivisor s)=if word 64 d=?0 then 0 else 1).
    assert (normal : MulDivDivision.MulDivDivision.signBit (r8_nremainder s) (r7_ndivisor s)=MulDivDivision.MulDivDivision.signBit (r8_nremainder s) (word 64 d)).
    { unfold MulDivDivision.MulDivDivision.signBit,MulDivDivision.MulDivDivision.difference; rewrite divisor.
      assert (widen : word 65 (word 64 d)=word 64 d) by (apply Words.word_widen; lia); rewrite widen; reflexivity. }
    rewrite normal; destruct (word 64 d=?0) eqn:zero.
    - apply Z.eqb_eq in zero; rewrite zero; apply MulDivZero.MulDivZero.zero_sign; rewrite candidateZero; vm_compute; reflexivity.
    - apply Z.eqb_neq in zero.
      pose proof (Words.word_bound 64 d ltac:(lia)) as hd.
      change (0<=word 64 d<2^64) in hd.
      rewrite MulDivDivision.MulDivDivision.signBit_correct by (rewrite candidateZero; lia).
      rewrite candidateZero; assert (choose : (word 64 d<=?0)=false) by (apply Z.leb_gt; lia).
      rewrite choose; reflexivity. }
  cbn [step r4_nneg_5Fout]; unfold v92; rewrite busy_no_accept by lia.
  unfold v91,v90,v89,v88,v87,v83,v82,v42,v41,v31.
  rewrite state,count,sign; unfold effectiveNegative.
  destruct (word 64 d=?0); destruct (bit_cases (r5_nisHi s)) as [hi|hi];
    destruct (bit_cases (r4_nneg_5Fout s)) as [neg|neg]; rewrite hi,neg; reflexivity.
Qed.
Local Opaque run step.
Theorem finish64 s inputs (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=1) (live : active inputs 64) :
  word 3 (r0_nstate (run s inputs 64))=(if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7) /\
  word 1 (r6_nresHi (run s inputs 64))=word 1 (r5_nisHi s) /\ metadata (run s inputs 64)=metadata s.
Proof.
  destruct (div_prefix 63 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  destruct (flags_run 63 s inputs state ltac:(rewrite count; lia)
    ltac:(rewrite count; vm_compute; discriminate) ltac:(intros t ht; apply live; lia)) as [meta flag].
  assert (lastCount : word 7 (r3_ncount (run s inputs 63))=64) by (rewrite ct,count; reflexivity).
  destruct (live 63%nat ltac:(lia)) as [hr hk].
  destruct (last_signed_edge _ _ st lastCount hr hk) as [finish select].
  split.
  - change (word 3 (r0_nstate (step (run s inputs 63) (inputs 63%nat)))=(if word 1 (r4_nneg_5Fout s)=?1 then 5 else 7)).
    rewrite finish,flag; destruct (word 1 (r4_nneg_5Fout s)=?1); reflexivity.
  - split.
    + change (word 1 (r6_nresHi (step (run s inputs 63) (inputs 63%nat)))=word 1 (r5_nisHi s)).
      rewrite select,normalize by lia; exact (f_equal (@snd (Z*Z) Z) meta).
    + exact (proj1 (flags_run 64 s inputs state ltac:(rewrite count; lia) ltac:(rewrite count; vm_compute; discriminate) live)).
Qed.
Theorem finish65 s inputs a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (initial : MulDivRefinement.MulDivRefinement.packed s=word 64 a) (live : active inputs 65) :
  word 3 (r0_nstate (run s inputs 65))=(if effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s)=?1 then 5 else 7) /\
  word 1 (r6_nresHi (run s inputs 65))=word 1 (r5_nisHi s) /\ metadata (run s inputs 65)=metadata s.
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  assert (st : word 3 (r0_nstate (step s (inputs O)))=3) by (rewrite (div_state _ _ state hr hk),count; reflexivity).
  assert (ct : word 7 (r3_ncount (step s (inputs O)))=1) by (rewrite (compute_count _ _ (or_intror state)),count; reflexivity).
  destruct (finish64 (step s (inputs O)) (fun t => inputs (S t)) st ct
    ltac:(intros t ht; apply live; lia)) as [finish [select meta]].
  pose proof (first_flag s (inputs O) a d state count divisor initial) as flag.
  pose proof (metadata_edge s (inputs O) state) as captured.
  rewrite flag in finish.
  assert (normal : word 1 (effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s))=effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s)).
  { unfold effectiveNegative; destruct (word 64 d=?0); [destruct (word 1 (r5_nisHi s)=?1)|]; try reflexivity; apply normalize; lia. }
  rewrite normal in finish.
  rewrite (run_from_next s inputs 64).
  split; [exact finish|]; split.
  - rewrite select; exact (f_equal (@snd (Z*Z) Z) captured).
  - rewrite meta; exact captured.
Qed.
End MulDivSignedExecution.
Print Assumptions MulDivSignedExecution.finish64.
Print Assumptions MulDivSignedExecution.first_flag.
Print Assumptions MulDivSignedExecution.finish65.
