From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedHistory.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedDivisionChecks.
Definition checks s i := forallb (fun b=>b) (firstn 4 (skipn 4 (assertionChecks s i)))=true.
Lemma sufficient s i
  (zero : v270 s i=0 \/ (v266 s i=1 /\ v273 s i=1))
  (nonzero : v283 s i=0 \/ (v282 s i=1 /\ v284 s i=1)) : checks s i.
Proof.
  unfold checks,assertionChecks; cbn [firstn skipn forallb].
  destruct zero as [z|[z1 z2]]; destruct nonzero as [n|[n1 n2]];
    rewrite ?z,?z1,?z2,?n,?n1,?n2; cbn [Z.eqb negb]; rewrite ?Bool.orb_true_r; reflexivity.
Qed.
Lemma widened_identity s i (identity : v236 s i*v216 s i+v235 s i=v272 s i) : v282 s i=1.
Proof.
  assert (q : 0<=v236 s i<2^64) by (unfold v236; apply bounds; lia).
  assert (d : 0<=v216 s i<2^64) by (unfold v216; apply bounds; lia).
  assert (r : 0<=v235 s i<2^64) by (unfold v235; apply bounds; lia).
  assert (a : 0<=v272 s i<2^64) by (unfold v272; apply bounds; lia).
  assert (powers : 2^64<=2^128 /\ 2^64<=2^129) by (split; apply Z.pow_le_mono_r; lia).
  assert (qn : word 128 (v236 s i)=v236 s i) by (apply Words.word_small; lia).
  assert (dn : word 128 (v216 s i)=v216 s i) by (apply Words.word_small; lia).
  assert (rn : word 129 (v235 s i)=v235 s i) by (apply Words.word_small; lia).
  assert (pn : word 128 (v236 s i*v216 s i)=v236 s i*v216 s i) by (apply Words.word_small; nia).
  assert (pn129 : word 129 (v236 s i*v216 s i)=v236 s i*v216 s i) by (apply Words.word_small; nia).
  unfold v282,v281,v280,v279,v278,v277,v276,v275,v274,v143,v8.
  change (word 65 0) with 0; change (word 64 0) with 0; change (word 1 0) with 0.
  rewrite !Z.shiftl_0_l,!Z.add_0_l,qn,dn,pn,pn129,rn,identity,Z.eqb_refl; reflexivity.
Qed.
Theorem nonzero_checks s i (positive : 0<v216 s i)
  (quotient : v236 s i=v272 s i/v216 s i)
  (residue : v235 s i=v272 s i mod v216 s i) : checks s i.
Proof.
  assert (nonzero : (v216 s i=?0)=false) by (apply Z.eqb_neq; lia).
  apply sufficient.
  - left; unfold v270,v269,v268,v143,v31; change (word 64 0) with 0; rewrite nonzero.
    change (word 1 (Z.land (Z.land (v267 s i) 0) (v228 s i))=0).
    rewrite Z.land_0_r,Z.land_0_l; reflexivity.
  - right; split.
    + apply widened_identity; rewrite quotient,residue; pose proof (Z.div_mod (v272 s i) (v216 s i) ltac:(lia)); nia.
    + unfold v284; rewrite residue.
      assert (small : (v272 s i mod v216 s i <? v216 s i)=true)
        by (apply Z.ltb_lt; pose proof (Z.mod_pos_bound (v272 s i) (v216 s i) positive); lia).
      rewrite small; reflexivity.
Qed.
Theorem zero_checks s i (zero : v216 s i=0)
  (quotient : v236 s i=18446744073709551615) (residue : v235 s i=v272 s i) : checks s i.
Proof.
  apply sufficient.
  - right; split.
    + unfold v266,v265; rewrite quotient; reflexivity.
    + unfold v273; rewrite residue,Z.eqb_refl; reflexivity.
  - left; unfold v283,v268,v143; rewrite zero; change (word 64 0) with 0.
    change (word 1 (Z.land (Z.land (v267 s i) 0) (v228 s i))=0).
    rewrite Z.land_0_r,Z.land_0_l; reflexivity.
Qed.
Theorem from_witness s i
  (quotient : v236 s i=if v216 s i=?0 then 18446744073709551615 else v272 s i/v216 s i)
  (residue : v235 s i=v272 s i mod v216 s i) : checks s i.
Proof.
  destruct (v216 s i=?0) eqn:zero.
  - apply Z.eqb_eq in zero; apply zero_checks; try assumption.
    rewrite zero,Zmod_0_r in residue; exact residue.
  - apply Z.eqb_neq in zero; apply nonzero_checks; try assumption.
    assert (bound : 0<=v216 s i<2^64) by (unfold v216; apply bounds; lia); lia.
Qed.
Lemma inactive_base s i (base : v267 s i=0) : checks s i.
Proof.
  apply sufficient; left; [unfold v270|unfold v283]; rewrite base,!Z.land_0_l; reflexivity.
Qed.
Lemma inactive_reset s i (reset : word 1 (nreset i)=1) : checks s i.
Proof.
  assert (gate : v228 s i=0) by (unfold v228,v31; rewrite reset; reflexivity).
  apply sufficient; left; [unfold v270|unfold v283]; rewrite gate,Z.land_0_r; reflexivity.
Qed.
End MulDivCheckedDivisionChecks.
Print Assumptions MulDivCheckedDivisionChecks.from_witness.
