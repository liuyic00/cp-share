From Stdlib Require Import ZArith Zmod.Bits.
From BitsProofs Require Import ArrayRefinementBase ArrayRefinementStep ArrayRefinementChecks.
From ReferenceProofs Require Import ArrayInvariant.
Open Scope Z_scope.
Module NativeArrayInvariant.
Theorem all_assertions_after_reset (s : N.State) (resetInput : N.Inputs)
  (reset : N.nreset resetInput = Zmod.one)
  (pins : nat -> N.Inputs) n (later : N.Inputs) :
  N.asserts (N.run (N.step s resetInput) pins n) later.
Proof.
  assert (reset' : ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word 1
    (R.nreset (inputs resetInput)) = 1).
  { rewrite inputs_nreset, reset; reflexivity. }
  pose proof (ReferenceProofs.ArrayInvariant.ArrayInvariant.all_assertions_after_reset
    (state s) (inputs resetInput) reset' (fun k => inputs (pins k)) n (inputs later)) as H.
  rewrite <-step_refines, <-run_refines in H.
  apply (proj2 (asserts_refine _ _)); exact H.
Qed.
Print Assumptions all_assertions_after_reset.
End NativeArrayInvariant.
