From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedHistory.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedTimingChecks.
(* This interface refers directly to the generated monitor expressions. *)
Definition cycles s := if word 1 (r12_ncontractDw s)=?1 then 64 else 32.
Lemma multiply_latency s i (operation : word 4 (r11_ncontractFn s)<4) :
  v225 s i=cycles s.
Proof.
  pose proof (bounds 4 (r11_ncontractFn s) ltac:(lia)) as range.
  assert (cases : word 4 (r11_ncontractFn s)=0 \/ word 4 (r11_ncontractFn s)=1 \/
    word 4 (r11_ncontractFn s)=2 \/ word 4 (r11_ncontractFn s)=3) by lia.
  unfold v225,v191; destruct cases as [h|[h|[h|h]]]; rewrite h;
    change (word 7 (v224 s i)=cycles s);
    unfold v224,v43,v223,cycles;
    destruct (word 1 (r12_ncontractDw s)=?1); reflexivity.
Qed.
Lemma gate_pending s i (gate : v229 s i=1) : word 1 (r9_ncontractPending s)=1.
Proof.
  destruct (bit_cases (r9_ncontractPending s)) as [zero|one]; [|exact one].
  unfold v229,v227 in gate; rewrite zero in gate; change (0=1) in gate; discriminate.
Qed.
Lemma disabled s i (gate : v229 s i<>1) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  change (andb (orb (negb (v229 s i=?1)) (v226 s i=?1))
    (andb (orb (negb (v229 s i=?1)) (v231 s i=?1)) true)=true).
  apply Z.eqb_neq in gate; rewrite gate; reflexivity.
Qed.
Theorem inactive s i (pending : word 1 (r9_ncontractPending s)<>1) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof. apply disabled; intro gate; apply pending; exact (gate_pending s i gate). Qed.
Theorem reset_disabled s i (reset : word 1 (nreset i)=1) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  apply disabled; unfold v229,v228,v31; rewrite reset.
  change (word 1 (Z.land (v227 s i) 0)<>1).
  rewrite Z.land_0_r; discriminate.
Qed.
Theorem kill_disabled s i (kill : word 1 (nio_5Fkill i)=1) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  apply disabled; unfold v229,v227,v189,v31; rewrite kill.
  change (word 1 (Z.land (word 1 (Z.land (word 1 (r9_ncontractPending s)) 0)) (v228 s i))<>1).
  rewrite Z.land_0_r; change (0<>1); discriminate.
Qed.
Theorem after_reset_edge s resetInput i (reset : word 1 (nreset resetInput)=1) :
  forallb (fun b=>b) (firstn 2 (assertionChecks (step s resetInput) i))=true.
Proof.
  apply inactive; destruct (reset_monitors s resetInput reset) as [pending rest].
  rewrite pending; discriminate.
Qed.
Theorem sufficient s i
  (bound : v229 s i=1 -> word 7 (r10_ncontractAge s)<=v225 s i)
  (valid : v229 s i=1 -> v38 s i=
    if word 7 (r10_ncontractAge s)=?v225 s i then 1 else 0) :
  forallb (fun b=>b) (firstn 2 (assertionChecks s i))=true.
Proof.
  destruct (Z.eq_dec (v229 s i) 1) as [gate|gate]; [|apply disabled; exact gate].
  specialize (bound gate); specialize (valid gate).
  apply Z.leb_le in bound.
  change (andb (orb (negb (v229 s i=?1)) (v226 s i=?1))
    (andb (orb (negb (v229 s i=?1)) (v231 s i=?1)) true)=true).
  rewrite gate; unfold v226,v231,v230; rewrite bound,valid.
  destruct (word 7 (r10_ncontractAge s)=?v225 s i); reflexivity.
Qed.
End MulDivCheckedTimingChecks.
Print Assumptions MulDivCheckedTimingChecks.multiply_latency.
Print Assumptions MulDivCheckedTimingChecks.sufficient.
