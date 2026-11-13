From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivSimulation MulDivUnsignedCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivSimulation.MulDivSimulation.
Open Scope Z_scope.
Module MulDivMetadata.
Definition metadata s := (word 1 (r1_nreq_5Fdw s), word 5 (r2_nreq_5Ftag s), word 1 (r5_nisHi s)).
Lemma metadata_edge s i (state : word 3 (r0_nstate s)=3) : metadata (step s i)=metadata s.
Proof.
  destruct (busy_request_metadata s i ltac:(lia)) as [dw tag].
  assert (hi : r5_nisHi (step s i)=word 1 (r5_nisHi s)).
  { cbn [step r5_nisHi]; unfold v93; rewrite busy_no_accept by lia; cbn [Z.eqb]; apply normalize; lia. }
  unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma nonnegative_edge s i (state : word 3 (r0_nstate s)=3)
  (nonnegative : word 1 (r4_nneg_5Fout s)=0) : r4_nneg_5Fout (step s i)=0.
Proof.
  cbn [step r4_nneg_5Fout]; unfold v92,v91; rewrite busy_no_accept by lia.
  rewrite nonnegative,Z.land_0_r; reflexivity.
Qed.
Theorem metadata_run n s inputs (state : word 3 (r0_nstate s)=3)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=65)
  (nonnegative : word 1 (r4_nneg_5Fout s)=0) (live : active inputs n) :
  metadata (run s inputs n)=metadata s /\ word 1 (r4_nneg_5Fout (run s inputs n))=0.
Proof.
  induction n as [|n IH]; [split; [reflexivity|exact nonnegative]|].
  destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [meta neg].
  destruct (div_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [st count].
  change (metadata (step (run s inputs n) (inputs n))=metadata s /\ word 1 (r4_nneg_5Fout (step (run s inputs n) (inputs n)))=0).
  rewrite metadata_edge by exact st; rewrite nonnegative_edge by assumption.
  split; [exact meta|reflexivity].
Qed.
Lemma last_edge s i (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=64) (nonnegative : word 1 (r4_nneg_5Fout s)=0)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=7 /\ r6_nresHi (step s i)=word 1 (r5_nisHi s).
Proof.
  split.
  - rewrite (div_state _ _ state hr hk),count,nonnegative; reflexivity.
  - cbn [step r6_nresHi]; unfold v100,v99,v98,v97,v96,v95,v94,v51,v50,v49,v48,v42,v41,v7,v44,v43,v53,v52,v31.
    rewrite busy_no_accept by lia; rewrite state,count; clean.
    destruct (bit_cases (r5_nisHi s)) as [h|h]; rewrite h; reflexivity.
Qed.
Local Opaque run step.
Theorem unsigned_finish s inputs (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (nonnegative : word 1 (r4_nneg_5Fout s)=0)
  (live : active inputs 65) :
  word 3 (r0_nstate (run s inputs 65))=7 /\
  word 1 (r6_nresHi (run s inputs 65))=word 1 (r5_nisHi s) /\
  metadata (run s inputs 65)=metadata s.
Proof.
  destruct (div_prefix 64 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  destruct (metadata_run 64 s inputs state ltac:(rewrite count; vm_compute; discriminate) nonnegative
    ltac:(intros t ht; apply live; lia)) as [meta neg].
  assert (lastCount : word 7 (r3_ncount (run s inputs 64))=64) by (rewrite ct,count; reflexivity).
  destruct (live 64%nat ltac:(lia)) as [hr hk].
  destruct (last_edge _ _ st lastCount neg hr hk) as [finish select].
  split.
  - change (word 3 (r0_nstate (step (run s inputs 64) (inputs 64%nat)))=7); rewrite finish; reflexivity.
  - split.
    + change (word 1 (r6_nresHi (step (run s inputs 64) (inputs 64%nat)))=word 1 (r5_nisHi s)).
      rewrite select,normalize by lia.
      exact (f_equal (@snd (Z*Z) Z) meta).
    + exact (proj1 (metadata_run 65 s inputs state ltac:(rewrite count; vm_compute; discriminate) nonnegative live)).
Qed.
Theorem unsigned_request_control s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : active inputs 66) :
  word 3 (r0_nstate (run s inputs 66))=7 /\
  word 1 (r6_nresHi (run s inputs 66))=(if word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?7 then 1 else 0) /\
  metadata (run s inputs 66)=(word 1 (nio_5Freq_5Fbits_5Fdw (inputs O)),
    word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)), if word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?7 then 1 else 0).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (MulDivUnsignedCapture.MulDivUnsignedCapture.capture s (inputs O) idle valid hr operation)
    as [st [ct [dv [sh [neg [dw [tag hi]]]]]]].
  destruct (unsigned_finish (step s (inputs O)) (fun t => inputs (S t))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity) ltac:(rewrite neg; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [finish [select meta]].
  rewrite (run_from_next s inputs 65).
  split; [exact finish|].
  rewrite select,meta; unfold metadata; rewrite dw,tag,hi.
  repeat rewrite normalize by lia.
  destruct (word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?7); split; reflexivity.
Qed.
End MulDivMetadata.
Print Assumptions MulDivMetadata.unsigned_finish.
Print Assumptions MulDivMetadata.unsigned_request_control.
