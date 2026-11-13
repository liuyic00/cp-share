From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivUnsignedCapture MulDivMetadata MulDivFormat MulDivZero.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivUnsignedCapture.MulDivUnsignedCapture MulDivMetadata.MulDivMetadata MulDivFormat.MulDivFormat.
Open Scope Z_scope.
Module MulDivUnsigned.
Definition specification i :=
  let a := operand i (nio_5Freq_5Fbits_5Fin1 i) in
  let d := operand i (nio_5Freq_5Fbits_5Fin2 i) in
  format (nio_5Freq_5Fbits_5Fdw i)
    (if word 4 (nio_5Freq_5Fbits_5Ffn i)=?7 then a mod d
      else if d=?0 then 2^64-1 else a/d).
Local Opaque run step observe.
Theorem accepted_nonzero_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : active inputs 66) (positive : 0<operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))) :
  nio_5Fresp_5Fvalid (observe (run s inputs 66) (inputs 66%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 66) (inputs 66%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 66) (inputs 66%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (unsigned_request_control s inputs idle valid operation live) as [state [selection meta]].
  destruct (accepted_nonzero_magnitudes s inputs idle valid operation live positive) as [quot rem].
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; right; exact state|].
  split.
  - rewrite observe_format by exact state.
    rewrite selection,quot,rem.
    unfold specification,format; rewrite width.
    assert (nz : (operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))=?0)=false) by (apply Z.eqb_neq; lia).
    rewrite nz.
    destruct (word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?7); reflexivity.
  - exact tag.
Qed.
Theorem accepted_zero_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : active inputs 66) (zero : operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))=0) :
  nio_5Fresp_5Fvalid (observe (run s inputs 66) (inputs 66%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 66) (inputs 66%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 66) (inputs 66%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (unsigned_request_control s inputs idle valid operation live) as [state [selection meta]].
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation) as [st [ct [dv [sh rest]]]].
  assert (an : word 64 (operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O)))=operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O))) by (apply Words.word_small; apply operand_bound).
  destruct (MulDivZero.MulDivZero.zero_magnitudes (step s (inputs O)) (fun t => inputs (S t))
    (operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O)))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(rewrite dv,zero; reflexivity) ltac:(rewrite an; exact sh)
    ltac:(intros t ht; apply live; lia)) as [quot rem].
  rewrite <- (run_from_next s inputs 65) in quot,rem; rewrite an in rem.
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; right; exact state|].
  split.
  - rewrite observe_format by exact state; rewrite selection,quot,rem.
    unfold specification,format; rewrite width,zero,Zmod_0_r.
    destruct (word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?7); reflexivity.
  - exact tag.
Qed.
Theorem accepted_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : active inputs 66) :
  nio_5Fresp_5Fvalid (observe (run s inputs 66) (inputs 66%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 66) (inputs 66%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 66) (inputs 66%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (Z.eq_dec (operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))) 0) as [zero|nonzero].
  - apply accepted_zero_result; assumption.
  - apply accepted_nonzero_result; try assumption.
    pose proof (operand_bound (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O))); lia.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=7)
  (live : active inputs 66) :
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs 66) (inputs 66%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs 66) (inputs 66%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs 66) (inputs 66%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivUnsigned.
Print Assumptions MulDivUnsigned.accepted_nonzero_result.
Print Assumptions MulDivUnsigned.accepted_result.
Print Assumptions MulDivUnsigned.after_reset_result.
