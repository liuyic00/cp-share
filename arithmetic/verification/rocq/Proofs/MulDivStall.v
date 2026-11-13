From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl.
Open Scope Z_scope.
Module MulDivStall.
Lemma output_congruent s t i j
  (st : word 3 (r0_nstate s)=word 3 (r0_nstate t))
  (dw : word 1 (r1_nreq_5Fdw s)=word 1 (r1_nreq_5Fdw t))
  (hi : word 1 (r6_nresHi s)=word 1 (r6_nresHi t))
  (rem : word 130 (r8_nremainder s)=word 130 (r8_nremainder t)) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=nio_5Fresp_5Fbits_5Fdata (observe t j).
Proof.
  cbn [observe nio_5Fresp_5Fbits_5Fdata].
  unfold v160, v159, v158, v157, v156, v155, v154, v153, v152, v145, v144, v119.
  rewrite st, dw, hi, rem; reflexivity.
Qed.
Lemma done_registers s i
  (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0)
  (stall : word 1 (nio_5Fresp_5Fready i)=0) :
  r0_nstate (step s i)=word 3 (r0_nstate s) /\
  r6_nresHi (step s i)=word 1 (r6_nresHi s) /\
  r8_nremainder (step s i)=word 130 (r8_nremainder s).
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; destruct done; lia).
  assert (h42 : v42 s i=0) by (unfold v42,v41; destruct done as [h|h]; rewrite h; reflexivity).
  assert (h48 : v48 s i=0) by (unfold v48,v7; destruct done as [h|h]; rewrite h; reflexivity).
  assert (h53 : v53 s i=0) by (unfold v53,v52; destruct done as [h|h]; rewrite h; reflexivity).
  assert (h55 : v55 s i=0) by (unfold v55,v54; destruct done as [h|h]; rewrite h; reflexivity).
  split.
  - cbn [step r0_nstate]; rewrite hr; control; destruct done as [h|h]; rewrite h, hk, stall; clean; reflexivity.
  - split.
    + cbn [step r6_nresHi]; unfold v100,v99,v98,v97,v96,v95,v94,v51.
      rewrite accept,h42,h48,h53; clean.
      destruct (bit_cases (r6_nresHi s)) as [h|h]; rewrite h; reflexivity.
    + cbn [step r8_nremainder]; unfold v151,v150,v149,v148,v142,v141.
      rewrite accept,h42,h48,h53,h55; clean; repeat rewrite normalize by lia; reflexivity.
Qed.
Theorem stall_stable s i later
  (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0)
  (stall : word 1 (nio_5Fresp_5Fready i)=0) :
  nio_5Fresp_5Fvalid (observe (step s i) later)=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=nio_5Fresp_5Fbits_5Fdata (observe s i) /\
  nio_5Fresp_5Fbits_5Ftag (observe (step s i) later)=nio_5Fresp_5Fbits_5Ftag (observe s i).
Proof.
  destruct (done_registers s i done hr hk stall) as [st [hi rem]].
  destruct (busy_request_metadata s i ltac:(destruct done; lia)) as [dw tag].
  split.
  - apply done_valid; rewrite st, normalize by lia; exact done.
  - split.
    + apply output_congruent; [rewrite st|rewrite dw|rewrite hi|rewrite rem]; apply normalize; lia.
    + cbn [observe nio_5Fresp_5Fbits_5Ftag]; rewrite tag; apply normalize; lia.
Qed.
Local Opaque step run observe.
Theorem stall_run_stable n s inputs
  (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (hold : forall t, (t<n)%nat -> word 1 (nreset (inputs t))=0 /\
    word 1 (nio_5Fkill (inputs t))=0 /\ word 1 (nio_5Fresp_5Fready (inputs t))=0) :
  word 3 (r0_nstate (run s inputs n))=word 3 (r0_nstate s) /\
  nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs n) (inputs n))=nio_5Fresp_5Fbits_5Fdata (observe s (inputs O)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs n) (inputs n))=nio_5Fresp_5Fbits_5Ftag (observe s (inputs O)).
Proof.
  induction n as [|n IH].
  - change (word 3 (r0_nstate s)=word 3 (r0_nstate s) /\
      nio_5Fresp_5Fvalid (observe s (inputs O))=1 /\
      nio_5Fresp_5Fbits_5Fdata (observe s (inputs O))=nio_5Fresp_5Fbits_5Fdata (observe s (inputs O)) /\
      nio_5Fresp_5Fbits_5Ftag (observe s (inputs O))=nio_5Fresp_5Fbits_5Ftag (observe s (inputs O))).
    repeat split; try reflexivity; apply done_valid; exact done.
  - destruct (IH ltac:(intros t ht; apply hold; lia)) as [st [valid [data tag]]].
    assert (dn : word 3 (r0_nstate (run s inputs n))=6 \/ word 3 (r0_nstate (run s inputs n))=7) by (rewrite st; exact done).
    destruct (hold n ltac:(lia)) as [hr [hk ready]].
    destruct (done_registers _ _ dn hr hk ready) as [next _].
    destruct (stall_stable _ _ (inputs (S n)) dn hr hk ready) as [nv [nd nt]].
    change (word 3 (r0_nstate (step (run s inputs n) (inputs n)))=word 3 (r0_nstate s) /\
      nio_5Fresp_5Fvalid (observe (step (run s inputs n) (inputs n)) (inputs (S n)))=1 /\
      nio_5Fresp_5Fbits_5Fdata (observe (step (run s inputs n) (inputs n)) (inputs (S n)))=nio_5Fresp_5Fbits_5Fdata (observe s (inputs O)) /\
      nio_5Fresp_5Fbits_5Ftag (observe (step (run s inputs n) (inputs n)) (inputs (S n)))=nio_5Fresp_5Fbits_5Ftag (observe s (inputs O))).
    rewrite next, normalize by lia; rewrite st, nv, nd, nt, data, tag; repeat split; reflexivity.
Qed.
End MulDivStall.
Print Assumptions MulDivStall.stall_stable.
Print Assumptions MulDivStall.stall_run_stable.
