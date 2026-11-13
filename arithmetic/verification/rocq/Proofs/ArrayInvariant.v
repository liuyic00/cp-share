From Coq Require Import ZArith Lia Bool.
From Generated Require Import ArrayMulDataModule.
From Proofs Require Import Words ArrayHold ArrayStall ArrayContract ArrayTree
  ArrayTreeOutput ArrayTreeCapture ArrayPacking ArrayRowSum.
Import ArrayMulDataModule.CIRCTBits ArrayMulDataModule.nArrayMulDataModule.
Open Scope Z_scope.
Module ArrayInvariant.

Definition FirstInvariant (s : State) : Prop :=
  forall later : Inputs, word 1 (r2535_nvalidFirst s) = 1 ->
    word 130 (inputPrefix130 s later) = word 130 (r2534_nexpectedFirst s).
Definition ResultInvariant (s : State) : Prop :=
  forall later : Inputs, word 1 (r2537_nresultKnown s) = 1 ->
    nio_5Fresult (observe s later) = word 130 (r2536_nexpectedResult s).
Definition PipelineInvariant (s : State) := FirstInvariant s /\ ResultInvariant s.

Lemma first_stage_capture (s : State) (i later : Inputs)
  (capture : word 1 (nio_5FregEnables_5F0 i) = 1) :
  word 130 (inputPrefix130 (step s i) later) = ArrayContract.specification i.
Proof.
  rewrite (tree_capture_prefix_130 s i later capture), captured_corrected_sum,
    ArrayRowSum.corrected_row_sum; reflexivity.
Qed.

Ltac normalize_known h :=
  repeat match type of h with
  | context[word ?w (word ?w ?x)] => rewrite (ArrayHold.normalize w x ltac:(lia)) in h
  end.

Lemma first_invariant_step (s : State) (i : Inputs) (old : FirstInvariant s) :
  FirstInvariant (step s i).
Proof.
  intros later known.
  destruct (ArrayStall.bit_cases (nreset i)) as [reset|reset].
  - destruct (ArrayStall.bit_cases (nio_5FregEnables_5F0 i)) as [disabled|enabled].
    + change (word 1 (if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16202 s i) = 1) in known.
      rewrite reset in known; cbn [Z.eqb] in known.
      unfold v16202 in known; rewrite disabled, Z.lor_0_l in known; normalize_known known.
      rewrite (tree_hold_prefix_130 s i later later disabled), (ArrayContract.first_hold s i disabled).
      rewrite ArrayHold.normalize by lia; apply old; exact known.
    + rewrite (first_stage_capture s i later enabled), (ArrayContract.first_capture s i enabled).
      unfold ArrayContract.specification; symmetry; apply ArrayHold.normalize; lia.
  - rewrite (proj1 (ArrayContract.reset_unknown s i reset)) in known; discriminate.
Qed.

Lemma result_invariant_step (s : State) (i : Inputs)
  (first : FirstInvariant s) (old : ResultInvariant s) : ResultInvariant (step s i).
Proof.
  intros later known.
  destruct (ArrayStall.bit_cases (nreset i)) as [reset|reset].
  - destruct (ArrayStall.bit_cases (nio_5FregEnables_5F1 i)) as [disabled|enabled].
    + change (word 1 (if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16204 s i) = 1) in known.
      rewrite reset in known; cbn [Z.eqb] in known.
      unfold v16204 in known; rewrite disabled in known; cbn [Z.eqb] in known; normalize_known known.
      pose proof (f_equal nio_5Fresult (ArrayHold.output_hold s i i later disabled)) as held.
      rewrite held, (ArrayContract.second_hold s i disabled), ArrayHold.normalize by lia.
      apply old; exact known.
    + change (word 1 (if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16204 s i) = 1) in known.
      rewrite reset in known; cbn [Z.eqb] in known.
      unfold v16204 in known; rewrite enabled in known; cbn [Z.eqb Pos.eqb] in known; normalize_known known.
      rewrite (tree_output_capture s i later enabled), (ArrayContract.transfer s i enabled), ArrayHold.normalize by lia.
      apply first; exact known.
  - rewrite (proj2 (ArrayContract.reset_unknown s i reset)) in known; discriminate.
Qed.

Theorem invariant_step (s : State) (i : Inputs) (old : PipelineInvariant s) :
  PipelineInvariant (step s i).
Proof. destruct old as [first result]; split; [apply first_invariant_step|apply result_invariant_step]; assumption. Qed.

Theorem invariant_after_reset (s : State) (resetInput : Inputs)
  (reset : word 1 (nreset resetInput) = 1) (inputs : nat -> Inputs) (n : nat) :
  PipelineInvariant (run (step s resetInput) inputs n).
Proof.
  induction n as [|n IH].
  - cbn [run]; destruct (ArrayContract.reset_unknown s resetInput reset) as [first result].
    split; intros later known; [rewrite first in known|rewrite result in known]; discriminate.
  - cbn [run]; apply invariant_step; exact IH.
Qed.

Local Opaque v16460.
Lemma product_check (s : State) (i : Inputs) (invariant : ResultInvariant s) :
  orb (negb (Z.eqb (v59795 s i) 1)) (Z.eqb (v59793 s i) 1) = true.
Proof.
  destruct (ArrayStall.bit_cases (r2537_nresultKnown s)) as [unknown|known].
  - unfold v59795; rewrite unknown, Z.land_0_l; reflexivity.
  - pose proof (invariant i known) as correct.
    change (v16460 s i = word 130 (r2536_nexpectedResult s)) in correct.
    assert (good : v59793 s i = 1).
    { unfold v59793; rewrite correct, Z.eqb_refl; reflexivity. }
    apply Bool.orb_true_intro; right; rewrite good; reflexivity.
Qed.

Theorem all_assertions_after_reset (s : State) (resetInput : Inputs)
  (reset : word 1 (nreset resetInput) = 1) (inputs : nat -> Inputs) (n : nat) (later : Inputs) :
  asserts (run (step s resetInput) inputs n) later.
Proof.
  apply ArrayStall.all_checks.
  - apply product_check; exact (proj2 (invariant_after_reset s resetInput reset inputs n)).
  - destruct n as [|n]; cbn [run]; apply ArrayStall.stall_check.
Qed.
Theorem valid_product_after_two_edges (s : State) (first second after : Inputs)
  (capture : word 1 (nio_5FregEnables_5F0 first) = 1)
  (transfer : word 1 (nio_5FregEnables_5F1 second) = 1)
  (r0 : word 1 (nreset first) = 0) (r1 : word 1 (nreset second) = 0) :
  r2537_nresultKnown (step (step s first) second) = 1 /\
  nio_5Fresult (observe (step (step s first) second) after) = ArrayContract.specification first.
Proof.
  split.
  - apply ArrayContract.known_after_two_edges; assumption.
  - exact (ArrayRowSum.two_edges s first second after capture transfer).
Qed.
Print Assumptions valid_product_after_two_edges.
Print Assumptions first_stage_capture.
Print Assumptions invariant_after_reset.
Print Assumptions all_assertions_after_reset.
End ArrayInvariant.
