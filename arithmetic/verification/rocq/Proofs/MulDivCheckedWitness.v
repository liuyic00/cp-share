From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedHistory MulDivStall.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedWitness.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Definition raw s := (word 64 (r8_nremainder s),word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65)).
Definition selected s :=
  let '((flag,q),r) := witness s in if flag=?1 then (q,r) else raw s.
Lemma source_nodes s i : (v236 s i,v235 s i)=selected s.
Proof.
  unfold selected,witness,raw,v236,v235,v144,v119.
  destruct (word 1 (r16_ncontractWasNegated s)=?1);
    repeat rewrite normalize by lia; [reflexivity|].
  rewrite Z.shiftr_0_r,narrow by lia; reflexivity.
Qed.
Theorem capture s i (state : word 3 (r0_nstate s)=5) (reset : word 1 (nreset i)=0) :
  selected (step s i)=raw s.
Proof. unfold selected; rewrite (capture_witness s i state reset); reflexivity. Qed.
Theorem from_raw s (flag : word 1 (r16_ncontractWasNegated s)=0) : selected s=raw s.
Proof. unfold selected,witness; rewrite flag; reflexivity. Qed.
Theorem hold s i (state : word 3 (r0_nstate s)=7)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0)
  (ready : word 1 (nio_5Fresp_5Fready i)=0) : selected (step s i)=selected s.
Proof.
  assert (record : witness (step s i)=witness s) by (apply hold_witness; try assumption; [lia|left; lia]).
  assert (rem : r8_nremainder (step s i)=word 130 (r8_nremainder s)).
  { destruct (MulDivStall.MulDivStall.done_registers (P.state s) (P.inputs i) (or_intror state) reset kill ready) as [st [hi rem]].
    rewrite <-P.step_projects in rem; exact rem. }
  unfold selected; rewrite record; destruct (witness s) as [[flag q] r]; destruct (flag=?1); [reflexivity|].
  unfold raw; rewrite rem,normalize,narrow by lia; reflexivity.
Qed.
End MulDivCheckedWitness.
Print Assumptions MulDivCheckedWitness.capture.
Print Assumptions MulDivCheckedWitness.hold.
