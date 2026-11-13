From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivMultiplyBalance MulDivMultiplyCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMultiplyBalance.MulDivMultiplyBalance.
Open Scope Z_scope.
Module MulDivMultiplyMetadata.
Definition metadata s := (word 1 (r1_nreq_5Fdw s), word 5 (r2_nreq_5Ftag s), word 1 (r5_nisHi s)).
Lemma metadata_edge s i (state : word 3 (r0_nstate s)=2) : metadata (step s i)=metadata s.
Proof.
  destruct (busy_request_metadata s i ltac:(lia)) as [dw tag].
  assert (hi : r5_nisHi (step s i)=word 1 (r5_nisHi s)).
  { cbn [step r5_nisHi]; unfold v93; rewrite busy_no_accept by lia; cbn [Z.eqb]; apply normalize; lia. }
  unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma nonnegative_edge s i (state : word 3 (r0_nstate s)=2)
  (nonnegative : word 1 (r4_nneg_5Fout s)=0) : r4_nneg_5Fout (step s i)=0.
Proof.
  cbn [step r4_nneg_5Fout]; unfold v92,v91; rewrite busy_no_accept by lia.
  rewrite nonnegative,Z.land_0_r; reflexivity.
Qed.
Theorem metadata_run n s inputs (state : word 3 (r0_nstate s)=2)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=64)
  (nonnegative : word 1 (r4_nneg_5Fout s)=0) (live : active inputs n) :
  metadata (run s inputs n)=metadata s /\ word 1 (r4_nneg_5Fout (run s inputs n))=0.
Proof.
  induction n as [|n IH]; [split; [reflexivity|exact nonnegative]|].
  destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [meta neg].
  destruct (compute_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [st count].
  change (metadata (step (run s inputs n) (inputs n))=metadata s /\ word 1 (r4_nneg_5Fout (step (run s inputs n) (inputs n)))=0).
  rewrite metadata_edge by exact st; rewrite nonnegative_edge by assumption.
  split; [exact meta|reflexivity].
Qed.
Lemma last_edge s i (state : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)=63)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=6 /\ r6_nresHi (step s i)=word 1 (r5_nisHi s).
Proof.
  split.
  - rewrite (mul_state _ _ state hr hk),count; reflexivity.
  - cbn [step r6_nresHi]; unfold v100,v99,v98,v97,v96,v95,v94,v51,v50,v49,v48,v42,v41,v7,v44,v43,v53,v52,v31.
    rewrite busy_no_accept by lia; rewrite state,count; clean.
    destruct (bit_cases (r5_nisHi s)) as [h|h]; rewrite h; reflexivity.
Qed.
Local Opaque run step.
Theorem metadata_preserved n s inputs (state : word 3 (r0_nstate s)=2)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=64) (live : active inputs n) :
  metadata (run s inputs n)=metadata s.
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct (compute_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [st count].
  change (run s inputs (S n)) with (step (run s inputs n) (inputs n)).
  rewrite metadata_edge by exact st; apply IH.
  - rewrite Nat2Z.inj_succ in remaining; lia.
  - intros t ht; apply live; lia.
Qed.
Theorem multiply_finish s inputs (state : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)=0) (live : active inputs 64) :
  word 3 (r0_nstate (run s inputs 64))=6 /\
  word 1 (r6_nresHi (run s inputs 64))=word 1 (r5_nisHi s) /\
  metadata (run s inputs 64)=metadata s.
Proof.
  destruct (compute_prefix 63 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  pose proof (metadata_preserved 63 s inputs state ltac:(rewrite count; vm_compute; discriminate)
    ltac:(intros t ht; apply live; lia)) as meta.
  assert (lastCount : word 7 (r3_ncount (run s inputs 63))=63) by (rewrite ct,count; reflexivity).
  destruct (live 63%nat ltac:(lia)) as [hr hk].
  destruct (last_edge _ _ st lastCount hr hk) as [finish select].
  split.
  - change (run s inputs 64) with (step (run s inputs 63) (inputs 63%nat)); rewrite finish; reflexivity.
  - split.
    + change (run s inputs 64) with (step (run s inputs 63) (inputs 63%nat)); rewrite select,normalize by lia.
      exact (f_equal (@snd (Z*Z) Z) meta).
    + apply metadata_preserved; [exact state|rewrite count; vm_compute; discriminate|exact live].
Qed.
Theorem unsigned_finish s inputs (state : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)=0) (nonnegative : word 1 (r4_nneg_5Fout s)=0)
  (live : active inputs 64) :
  word 3 (r0_nstate (run s inputs 64))=6 /\
  word 1 (r6_nresHi (run s inputs 64))=word 1 (r5_nisHi s) /\
  metadata (run s inputs 64)=metadata s.
Proof.
  destruct (compute_prefix 63 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  destruct (metadata_run 63 s inputs state ltac:(rewrite count; vm_compute; discriminate) nonnegative
    ltac:(intros t ht; apply live; lia)) as [meta neg].
  assert (lastCount : word 7 (r3_ncount (run s inputs 63))=63) by (rewrite ct,count; reflexivity).
  destruct (live 63%nat ltac:(lia)) as [hr hk].
  destruct (last_edge _ _ st lastCount hr hk) as [finish select].
  split.
  - change (word 3 (r0_nstate (step (run s inputs 63) (inputs 63%nat)))=6); rewrite finish; reflexivity.
  - split.
    + change (word 1 (r6_nresHi (step (run s inputs 63) (inputs 63%nat)))=word 1 (r5_nisHi s)).
      rewrite select,normalize by lia.
      exact (f_equal (@snd (Z*Z) Z) meta).
    + exact (proj1 (metadata_run 64 s inputs state ltac:(rewrite count; vm_compute; discriminate) nonnegative live)).
Qed.
Theorem unsigned_request_control s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=3)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : active inputs 65) :
  word 3 (r0_nstate (run s inputs 65))=6 /\
  word 1 (r6_nresHi (run s inputs 65))=1 /\
  metadata (run s inputs 65)=(word 1 (nio_5Freq_5Fbits_5Fdw (inputs O)),
    word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)), 1).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (MulDivMultiplyCapture.MulDivMultiplyCapture.capture s (inputs O) idle valid hr operation full)
    as [st [ct [dv [sh [neg [dw [tag hi]]]]]]].
  destruct (unsigned_finish (step s (inputs O)) (fun t => inputs (S t))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity) ltac:(rewrite neg; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [finish [select meta]].
  rewrite (run_from_next s inputs 64).
  split; [exact finish|].
  rewrite select,meta; unfold metadata; rewrite dw,tag,hi.
  repeat rewrite normalize by lia.
  split; reflexivity.
Qed.
End MulDivMultiplyMetadata.
Print Assumptions MulDivMultiplyMetadata.unsigned_finish.
Print Assumptions MulDivMultiplyMetadata.unsigned_request_control.
