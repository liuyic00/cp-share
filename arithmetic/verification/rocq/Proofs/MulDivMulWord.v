From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivRefinement MulDivFormat MulDivMultiply MulDivMultiplyBalance MulDivMultiplyMetadata MulDivMulLow MulDivMulWordCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivFormat.MulDivFormat MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyMetadata.MulDivMultiplyMetadata MulDivMulWordCapture.MulDivMulWordCapture.
Open Scope Z_scope.
Module MulDivMulWord.
Lemma observe_word s i (state : word 3 (r0_nstate s)=6)
  (mode : word 1 (r1_nreq_5Fdw s)=0) (selection : word 1 (r6_nresHi s)=0) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=word 64 (SignedWords.signed 32 (word 32 (Z.shiftr (packed s) 32))).
Proof.
  assert (slice : v156 s i=word 32 (Z.shiftr (packed s) 32)).
  { unfold v156,v154,v153; rewrite state,mode; clean; unfold v152,v145,v119; rewrite selection; cbn [Z.eqb Pos.eqb].
    rewrite Z.shiftr_0_r; repeat rewrite normalize by lia; rewrite narrow by lia.
    rewrite <- MulDivMulLow.MulDivMulLow.packed_low.
    repeat rewrite extract_normal by lia; reflexivity. }
  cbn [observe nio_5Fresp_5Fbits_5Fdata]; unfold v160,v159,v158,v157; rewrite mode; cbn [Z.eqb].
  rewrite normalize by lia; rewrite slice.
  pose proof (extend_wire (word 32 (Z.shiftr (packed s) 32))) as ext.
  rewrite Z.shiftr_0_r,normalize in ext by lia; exact ext.
Qed.
Local Opaque run step observe.
Theorem finish32 s inputs (state : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)=32) (live : active inputs 32) :
  word 3 (r0_nstate (run s inputs 32))=6 /\
  word 1 (r6_nresHi (run s inputs 32))=word 1 (r5_nisHi s) /\
  metadata (run s inputs 32)=metadata s.
Proof.
  destruct (compute_prefix 31 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  pose proof (metadata_preserved 31 s inputs state ltac:(rewrite count; vm_compute; discriminate)
    ltac:(intros t ht; apply live; lia)) as meta.
  assert (lastCount : word 7 (r3_ncount (run s inputs 31))=63) by (rewrite ct,count; reflexivity).
  destruct (live 31%nat ltac:(lia)) as [hr hk].
  destruct (last_edge _ _ st lastCount hr hk) as [finish select].
  split.
  - change (run s inputs 32) with (step (run s inputs 31) (inputs 31%nat)); rewrite finish; reflexivity.
  - split.
    + change (run s inputs 32) with (step (run s inputs 31) (inputs 31%nat)); rewrite select,normalize by lia.
      exact (f_equal (@snd (Z*Z) Z) meta).
    + apply metadata_preserved; [exact state|rewrite count; vm_compute; discriminate|exact live].
Qed.
Theorem request_control s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (mode : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=0) (live : active inputs 33) :
  word 3 (r0_nstate (run s inputs 33))=6 /\
  word 1 (r6_nresHi (run s inputs 33))=0 /\
  metadata (run s inputs 33)=(0,word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)),0).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture_control s (inputs O) idle valid hr operation mode) as [st [ct [dw [tag hi]]]].
  destruct (finish32 (step s (inputs O)) (fun t => inputs (S t))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [finish [selection meta]].
  rewrite (run_from_next s inputs 32); split; [exact finish|].
  rewrite selection,meta; unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; split; reflexivity.
Qed.
Definition specification i := word 64 (SignedWords.signed 32
  (word 32 (SignedWords.signed 32 (nio_5Freq_5Fbits_5Fin2 i)*word 32 (nio_5Freq_5Fbits_5Fin1 i)))).
Theorem accepted_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (mode : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=0) (live : active inputs 33) :
  nio_5Fresp_5Fvalid (observe (run s inputs 33) (inputs 33%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 33) (inputs 33%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 33) (inputs 33%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (request_control s inputs idle valid operation mode live) as [state [selection meta]].
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; left; exact state|]; split.
  - rewrite observe_word by assumption.
    rewrite (accepted_slice s inputs idle valid operation mode live); reflexivity.
  - exact tag.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (mode : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=0) (live : active inputs 33) :
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs 33) (inputs 33%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs 33) (inputs 33%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs 33) (inputs 33%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivMulWord.
Print Assumptions MulDivMulWord.observe_word.
Print Assumptions MulDivMulWord.finish32.
Print Assumptions MulDivMulWord.accepted_result.
Print Assumptions MulDivMulWord.after_reset_result.
