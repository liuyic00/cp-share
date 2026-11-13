From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivRefinement MulDivInitialization MulDivZero MulDivMetadata MulDivFormat MulDivSignedExecution MulDivSignedOutput.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivMetadata.MulDivMetadata MulDivFormat.MulDivFormat MulDivSignedExecution.MulDivSignedExecution MulDivSignedOutput.MulDivSignedOutput.
Open Scope Z_scope.
Module MulDivSignedCore.
Definition quotient a d := if word 64 d=?0 then 2^64-1 else word 64 a/word 64 d.
Definition coreResult a d hi negative :=
  let value := if word 1 hi=?1 then word 64 a mod word 64 d else quotient a d in
  if effectiveNegative d hi negative=?1 then -value else value.
Lemma effective_normal d hi negative : word 1 (effectiveNegative d hi negative)=effectiveNegative d hi negative.
Proof. unfold effectiveNegative; destruct (word 64 d=?0); [destruct (word 1 hi=?1)|]; try reflexivity; apply normalize; lia. Qed.
Local Opaque run step observe.
Lemma magnitudes s inputs a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (initial : packed s=word 64 a) (live : active inputs 65) :
  word 64 (r8_nremainder (run s inputs 65))=quotient a d /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs 65))) 65)=word 64 a mod word 64 d.
Proof.
  unfold quotient; destruct (word 64 d=?0) eqn:zero.
  - apply Z.eqb_eq in zero.
    destruct (MulDivZero.MulDivZero.zero_magnitudes s inputs a state count ltac:(rewrite divisor,zero; reflexivity) initial live) as [q r].
    rewrite zero,Zmod_0_r; split; assumption.
  - apply Z.eqb_neq in zero; apply MulDivInitialization.MulDivInitialization.full_magnitude_result; try assumption.
    pose proof (Words.word_bound 64 d ltac:(lia)) as hd; change (0<=word 64 d<2^64) in hd; lia.
Qed.
Theorem completed_result s inputs pins a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (initial : packed s=word 64 a) (live : active inputs 66) :
  let result := completed (run s inputs 65) (inputs 65%nat) (effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s)) in
  nio_5Fresp_5Fvalid (observe result pins)=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe result pins)=format (r1_nreq_5Fdw s) (coreResult a d (r5_nisHi s) (r4_nneg_5Fout s)) /\
  nio_5Fresp_5Fbits_5Ftag (observe result pins)=word 5 (r2_nreq_5Ftag s).
Proof.
  cbn zeta.
  assert (live65 : active inputs 65) by (intros t ht; apply live; lia).
  destruct (finish65 s inputs a d state count divisor initial live65) as [st [select meta]].
  destruct (magnitudes s inputs a d state count divisor initial live65) as [q r].
  destruct (live 65%nat ltac:(lia)) as [hr hk].
  destruct (completion_result (run s inputs 65) (inputs 65%nat) pins
    (effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s)) ltac:(rewrite effective_normal; exact st) hr hk) as [valid [data tag]].
  unfold metadata in meta; injection meta as width originalTag hi.
  split; [exact valid|]; split.
  - rewrite data,effective_normal; unfold selected; rewrite select,q,r.
    unfold coreResult,format; rewrite width; reflexivity.
  - rewrite tag; exact originalTag.
Qed.
Definition correctionEdges d hi negative : nat := if effectiveNegative d hi negative=?1 then 1%nat else 0%nat.
Theorem prepared_result_exact s inputs a d (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (initial : packed s=word 64 a) (live : active inputs 66) :
  exists n, n=(65+correctionEdges d (r5_nisHi s) (r4_nneg_5Fout s))%nat /\ (65<=n<=66)%nat /\
  nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs n) (inputs n))=format (r1_nreq_5Fdw s) (coreResult a d (r5_nisHi s) (r4_nneg_5Fout s)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs n) (inputs n))=word 5 (r2_nreq_5Ftag s).
Proof.
  unfold correctionEdges; destruct (effectiveNegative d (r5_nisHi s) (r4_nneg_5Fout s)=?1) eqn:neg.
  - exists 66%nat; split; [reflexivity|]; split; [lia|].
    pose proof (completed_result s inputs (inputs 66%nat) a d state count divisor initial live) as result.
    unfold completed in result; rewrite effective_normal,neg in result; exact result.
  - exists 65%nat; split; [reflexivity|]; split; [lia|].
    pose proof (completed_result s inputs (inputs 65%nat) a d state count divisor initial live) as result.
    unfold completed in result; rewrite effective_normal,neg in result; exact result.
Qed.
End MulDivSignedCore.
Print Assumptions MulDivSignedCore.prepared_result_exact.
