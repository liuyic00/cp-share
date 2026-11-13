From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsProofs Require Import ArrayRefinementBase ArrayRefinementNodes016 ArrayRefinementStep ReferenceSigned.
From ReferenceProofs Require Import ArrayInvariant ArrayContract ArrayHold ArrayRowSum.
Open Scope Z_scope.
Module NativeArrayContract.

Lemma output_refines s i :
  R.nio_5Fresult (R.observe (state s) (inputs i)) =
  Zmod.unsigned (N.nio_5Fresult (N.observe s i)).
Proof. exact (node_16460 s i). Qed.

Lemma specification_refines i :
  ReferenceProofs.ArrayContract.ArrayContract.specification (inputs i) =
  (Zmod.signed (N.nio_5Fa i) * Zmod.signed (N.nio_5Fb i)) mod 2^130.
Proof.
  unfold ReferenceProofs.ArrayContract.ArrayContract.specification.
  rewrite inputs_nio_5Fa, inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite !signed_refines by lia; reflexivity.
Qed.

(* Data registers are not reset: this arithmetic contract needs only the two
   pipeline enables, just like the original Lean/reference contract. *)
Theorem two_edges (s : N.State) (first second after : N.Inputs)
  (capture : N.nio_5FregEnables_5F0 first = Zmod.one)
  (transfer : N.nio_5FregEnables_5F1 second = Zmod.one) :
  Zmod.unsigned (N.nio_5Fresult (N.observe (N.step (N.step s first) second) after)) =
    (Zmod.signed (N.nio_5Fa first) * Zmod.signed (N.nio_5Fb first)) mod 2^130.
Proof.
  assert (capture' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nio_5FregEnables_5F0 (inputs first)) = 1).
  { rewrite inputs_nio_5FregEnables_5F0, capture; reflexivity. }
  assert (transfer' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nio_5FregEnables_5F1 (inputs second)) = 1).
  { rewrite inputs_nio_5FregEnables_5F1, transfer; reflexivity. }
  pose proof (ReferenceProofs.ArrayRowSum.ArrayRowSum.two_edges
    (state s) (inputs first) (inputs second) (inputs after) capture' transfer') as H.
  rewrite <-step_refines, <-step_refines, output_refines in H.
  change (Zmod.unsigned (N.nio_5Fresult (N.observe (N.step (N.step s first) second) after)) =
    ReferenceProofs.ArrayContract.ArrayContract.specification (inputs first)) in H.
  rewrite specification_refines in H; exact H.
Qed.

Theorem valid_product_after_two_edges (s : N.State) (first second after : N.Inputs)
  (capture : N.nio_5FregEnables_5F0 first = Zmod.one)
  (transfer : N.nio_5FregEnables_5F1 second = Zmod.one)
  (r0 : N.nreset first = Zmod.zero) (r1 : N.nreset second = Zmod.zero) :
  N.r2537_nresultKnown (N.step (N.step s first) second) = Zmod.one /\
  Zmod.unsigned (N.nio_5Fresult (N.observe (N.step (N.step s first) second) after)) =
    (Zmod.signed (N.nio_5Fa first) * Zmod.signed (N.nio_5Fb first)) mod 2^130.
Proof.
  assert (capture' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nio_5FregEnables_5F0 (inputs first)) = 1).
  { rewrite inputs_nio_5FregEnables_5F0, capture; reflexivity. }
  assert (transfer' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nio_5FregEnables_5F1 (inputs second)) = 1).
  { rewrite inputs_nio_5FregEnables_5F1, transfer; reflexivity. }
  assert (r0' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nreset (inputs first)) = 0).
  { rewrite inputs_nreset, r0; reflexivity. }
  assert (r1' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nreset (inputs second)) = 0).
  { rewrite inputs_nreset, r1; reflexivity. }
  pose proof (ReferenceProofs.ArrayInvariant.ArrayInvariant.valid_product_after_two_edges
    (state s) (inputs first) (inputs second) (inputs after)
    capture' transfer' r0' r1') as H.
  rewrite <-step_refines, <-step_refines in H.
  rewrite state_r2537_nresultKnown, output_refines, specification_refines in H.
  destruct H as [known result]; split; [|exact result].
  apply Zmod.to_Z_inj; exact known.
Qed.

Theorem output_hold (s : N.State) (i before after : N.Inputs)
  (disabled : N.nio_5FregEnables_5F1 i = Zmod.zero) :
  N.nio_5Fresult (N.observe (N.step s i) after) =
  N.nio_5Fresult (N.observe s before).
Proof.
  assert (disabled' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nio_5FregEnables_5F1 (inputs i)) = 0).
  { rewrite inputs_nio_5FregEnables_5F1, disabled; reflexivity. }
  pose proof (ReferenceProofs.ArrayHold.ArrayHold.output_hold (state s) (inputs i) (inputs before) (inputs after) disabled') as H.
  apply (f_equal R.nio_5Fresult) in H.
  rewrite <-step_refines, !output_refines in H.
  apply Zmod.to_Z_inj; exact H.
Qed.
Print Assumptions valid_product_after_two_edges.
Print Assumptions two_edges.
Print Assumptions output_hold.
End NativeArrayContract.
