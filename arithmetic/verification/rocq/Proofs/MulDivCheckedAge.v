From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedHistory MulDivCheckedProjection MulDivControl.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedAge.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Lemma busy s i (state : word 3 (r0_nstate s)<>0) : v2 s i=0.
Proof. rewrite P.node_v2; apply MulDivControl.MulDivControl.busy_no_accept; exact state. Qed.
Lemma advance s i (reset : word 1 (nreset i)=0) (absent : v2 s i=0)
  (pending : word 1 (r9_ncontractPending s)=1) (valid : v38 s i=0) :
  word 7 (r10_ncontractAge (step s i))=word 7 (word 7 (r10_ncontractAge s)+1).
Proof.
  cbn [step r10_ncontractAge]; rewrite reset.
  unfold v168,v167,v166,v165,v164,v68,v31; rewrite absent,pending,valid.
  change (word 7 (word 7 (word 7 (word 7 (word 7 (r10_ncontractAge s)+1))))=word 7 (word 7 (r10_ncontractAge s)+1)).
  repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma hold_done s i (reset : word 1 (nreset i)=0) (absent : v2 s i=0)
  (valid : v38 s i=1) :
  word 7 (r10_ncontractAge (step s i))=word 7 (r10_ncontractAge s).
Proof.
  cbn [step r10_ncontractAge]; rewrite reset.
  unfold v168,v167,v165,v164,v31; rewrite absent,valid.
  change (word 7 (word 7 (word 7 (if word 1 (Z.land (word 1 (r9_ncontractPending s)) 0)=?1 then v166 s i else word 7 (r10_ncontractAge s))))=word 7 (r10_ncontractAge s)).
  rewrite Z.land_0_r; change (word 7 (word 7 (word 7 (word 7 (r10_ncontractAge s))))=word 7 (r10_ncontractAge s)).
  repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma width_hold s i (absent : v2 s i=0) :
  word 1 (r12_ncontractDw (step s i))=word 1 (r12_ncontractDw s).
Proof. cbn [step r12_ncontractDw]; unfold v170; rewrite absent; cbn [Z.eqb]; repeat rewrite normalize by lia; reflexivity. Qed.
Lemma fn_hold s i (absent : v2 s i=0) :
  word 4 (r11_ncontractFn (step s i))=word 4 (r11_ncontractFn s).
Proof. cbn [step r11_ncontractFn]; unfold v169; rewrite absent; cbn [Z.eqb]; repeat rewrite normalize by lia; reflexivity. Qed.
Lemma multiply_valid s i (state : word 3 (r0_nstate s)=2) : v38 s i=0.
Proof. unfold v38,v37,v36,v35,v4; rewrite state; reflexivity. Qed.
Lemma done_valid s i (state : word 3 (r0_nstate s)=6) : v38 s i=1.
Proof. unfold v38,v37,v36,v35,v4; rewrite state; reflexivity. Qed.
Theorem multiply_age s i (state : word 3 (r0_nstate s)=2)
  (reset : word 1 (nreset i)=0) (pending : word 1 (r9_ncontractPending s)=1)
  (range : word 7 (r10_ncontractAge s)<64) :
  word 7 (r10_ncontractAge (step s i))=word 7 (r10_ncontractAge s)+1.
Proof.
  assert (absent : v2 s i=0) by (apply busy; lia).
  rewrite (advance s i reset absent pending (multiply_valid s i state)).
  apply Words.word_small; pose proof (bounds 7 (r10_ncontractAge s) ltac:(lia)); change (2^7) with 128 in *; lia.
Qed.
End MulDivCheckedAge.
Print Assumptions MulDivCheckedAge.multiply_age.
