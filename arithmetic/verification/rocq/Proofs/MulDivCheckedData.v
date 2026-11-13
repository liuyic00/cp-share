From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedHistory MulDivCheckedSignedOperands MulDivFormat.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedData.
Definition format width value := if word 1 width=?1 then word 64 value else word 64 (SignedWords.signed 32 value).
Lemma format_normal width value : format width (word 64 value)=format width value.
Proof.
  unfold format; destruct (word 1 width=?1); [apply normalize; lia|].
  unfold SignedWords.signed; change (Words.word 32 (word 64 value)) with (word 32 (word 64 value)).
  rewrite narrow by lia; reflexivity.
Qed.
Lemma expected_format s i : v263 s i=format (r12_ncontractDw s) (v258 s i).
Proof.
  assert (normal : word 64 (v258 s i)=v258 s i) by (unfold v258; apply normalize; lia).
  unfold v263,v262,v261,v260,v259,format; destruct (word 1 (r12_ncontractDw s)=?1); [reflexivity|].
  rewrite normalize by lia.
  rewrite <-normal at 1 2.
  apply MulDivCheckedSignedOperands.MulDivCheckedSignedOperands.extend_wire.
Qed.
Lemma division_expected s i (division : v191 s i=1) : v263 s i=format (r12_ncontractDw s) (v239 s i).
Proof. rewrite expected_format; unfold v258; rewrite division; cbn [Z.eqb Pos.eqb]; apply format_normal. Qed.
Lemma gate_active s i (enabled : v234 s i=1) : word 1 (r9_ncontractPending s)=1 /\ v38 s i=1.
Proof.
  destruct (bit_cases (r9_ncontractPending s)) as [p|p].
  - unfold v234,v233,v227 in enabled; rewrite p in enabled; discriminate.
  - split; [exact p|]; assert (valid : v38 s i=0 \/ v38 s i=1) by (unfold v38; apply bit_cases).
    destruct valid as [v|v]; [|exact v]; unfold v234,v233 in enabled; rewrite v,Z.land_0_r in enabled; discriminate.
Qed.
Theorem inactive s i (disabled : ~ (word 1 (r9_ncontractPending s)=1 /\ v38 s i=1)) :
  nth 3 (assertionChecks s i) false=true.
Proof.
  change (orb (negb (v234 s i=?1)) (v264 s i=?1)=true).
  destruct (v234 s i=?1) eqn:gate; [|reflexivity].
  apply Z.eqb_eq in gate; exfalso; apply disabled; apply gate_active; exact gate.
Qed.
Theorem of_correct s i (correct : nio_5Fresp_5Fbits_5Fdata (observe s i)=v263 s i) :
  nth 3 (assertionChecks s i) false=true.
Proof.
  change (v187 s i=v263 s i) in correct.
  change (orb (negb (v234 s i=?1)) (v264 s i=?1)=true).
  unfold v264; rewrite correct,Z.eqb_refl.
  destruct (v234 s i=?1); reflexivity.
Qed.
End MulDivCheckedData.
Print Assumptions MulDivCheckedData.expected_format.
Print Assumptions MulDivCheckedData.of_correct.
