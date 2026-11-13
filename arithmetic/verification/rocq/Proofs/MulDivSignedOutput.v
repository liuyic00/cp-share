From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivRefinement MulDivMetadata MulDivFormat.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivMetadata.MulDivMetadata MulDivFormat.MulDivFormat.
Open Scope Z_scope.
Module MulDivSignedOutput.
Definition selected s := if word 1 (r6_nresHi s)=?1
  then word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65) else word 64 (r8_nremainder s).
Lemma selected_normal s : word 64 (selected s)=selected s.
Proof. unfold selected; destruct (word 1 (r6_nresHi s)=?1); apply normalize; lia. Qed.
Lemma negate_response s i (state : word 3 (r0_nstate s)=5)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  r0_nstate (step s i)=7 /\ r6_nresHi (step s i)=0 /\
  word 64 (r8_nremainder (step s i))=word 64 (-selected s) /\ metadata (step s i)=metadata s.
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  assert (div : v42 s i=0) by (unfold v42,v41; rewrite state; reflexivity).
  assert (mul : v48 s i=0) by (unfold v48,v7; rewrite state; reflexivity).
  assert (neg : v53 s i=1) by (unfold v53,v52; rewrite state; reflexivity).
  assert (input : v55 s i=0) by (unfold v55,v54; rewrite state; reflexivity).
  split; [apply negate_output_state; assumption|].
  split.
  - cbn [step r6_nresHi]; unfold v100,v99,v98,v97,v96,v95,v94,v51,v31.
    rewrite accept,div,mul,neg; clean; reflexivity.
  - split.
    + cbn [step r8_nremainder]; unfold v151,v150,v149,v148,v142,v141.
      rewrite accept,div,mul,neg,input; clean.
      unfold v147,v146,v145,v144,v143,v119,v110.
      change (word 66 0) with 0; change (word 64 0) with 0; change (Z.shiftl 0 64) with 0.
      rewrite Z.add_0_l,Z.sub_0_l,Z.shiftr_0_r.
      repeat rewrite narrow by lia; repeat rewrite normalize by lia.
      unfold selected; destruct (word 1 (r6_nresHi s)=?1); repeat rewrite normalize by lia; reflexivity.
    + destruct (busy_request_metadata s i ltac:(lia)) as [dw tag].
      assert (hi : r5_nisHi (step s i)=word 1 (r5_nisHi s)).
      { cbn [step r5_nisHi]; unfold v93; rewrite accept; cbn [Z.eqb]; apply normalize; lia. }
      unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; reflexivity.
Qed.
Definition completed s i negative := if word 1 negative=?1 then step s i else s.
Theorem completion_result s i pins negative
  (state : word 3 (r0_nstate s)=if word 1 negative=?1 then 5 else 7)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  nio_5Fresp_5Fvalid (observe (completed s i negative) pins)=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (completed s i negative) pins)=
    format (r1_nreq_5Fdw s) (if word 1 negative=?1 then -selected s else selected s) /\
  nio_5Fresp_5Fbits_5Ftag (observe (completed s i negative) pins)=word 5 (r2_nreq_5Ftag s).
Proof.
  unfold completed; destruct (word 1 negative=?1).
  - destruct (negate_response s i state hr hk) as [st [hi [value meta]]].
    unfold metadata in meta; injection meta as dw tag sameHi.
    assert (next : word 3 (r0_nstate (step s i))=7) by (rewrite st; reflexivity).
    split; [apply done_valid; right; exact next|].
    split.
    + rewrite observe_format by exact next; rewrite hi; cbn [Z.eqb]; rewrite value.
      unfold format. change (word 1 (r1_nreq_5Fdw (step s i))=word 1 (r1_nreq_5Fdw s)) in dw.
      rewrite dw; change (word 1 0) with 0; cbn [Z.eqb].
      destruct (word 1 (r1_nreq_5Fdw s)=?1); [apply normalize; lia|].
      unfold SignedWords.signed; change (word 64 (if word 32 (word 64 (-selected s)) <? 2^(32-1) then word 32 (word 64 (-selected s)) else word 32 (word 64 (-selected s))-2^32)=word 64 (if word 32 (-selected s) <? 2^(32-1) then word 32 (-selected s) else word 32 (-selected s)-2^32)).
      rewrite narrow by lia; reflexivity.
    + exact tag.
  - split; [apply done_valid; right; exact state|].
    split; [apply observe_format; exact state|reflexivity].
Qed.
End MulDivSignedOutput.
Print Assumptions MulDivSignedOutput.completion_result.
