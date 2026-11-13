From Coq Require Import ZArith Lia List Bool.
From Generated Require Import ArrayMulDataModule.
From Proofs Require Import Words ArrayHold ArrayCompressors.
Import ListNotations ArrayMulDataModule.CIRCTBits ArrayMulDataModule.nArrayMulDataModule.
Open Scope Z_scope.
Module ArrayStall.
Lemma bit_cases x : word 1 x = 0 \/ word 1 x = 1.
Proof. exact (Words.bit_cases x). Qed.

Lemma holding_disabled (s : State) (i : Inputs)
  (flag : word 1 (r2539_nwasHoldingKnownResult (step s i)) = 1) :
  word 1 (nio_5FregEnables_5F1 i) = 0.
Proof.
  change (word 1 (if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16462 s i) = 1) in flag.
  unfold v6, v16462, v16461, v3021 in flag.
  destruct (bit_cases (nreset i)) as [hr|hr];
  destruct (bit_cases (nio_5FregEnables_5F1 i)) as [he|he];
  destruct (bit_cases (r2537_nresultKnown s)) as [hk|hk];
  rewrite hr, he, hk in flag;
  vm_compute in flag; try discriminate; exact he.
Qed.

Lemma result_normal (s : State) (i : Inputs) : word 130 (v16460 s i) = v16460 s i.
Proof. unfold v16460; apply ArrayHold.normalize; lia. Qed.

(* Use the already proved output equalities without unfolding the entire DAG
   during Boolean rewriting. This changes tactic transparency, not the model. *)
Local Opaque v16460.

(* The actual stall check after every edge, independently of arithmetic/reset. *)
Theorem stall_check (s : State) (i later : Inputs) :
  orb (negb (Z.eqb (v59797 (step s i) later) 1))
      (Z.eqb (v59796 (step s i) later) 1) = true.
Proof.
  destruct (bit_cases (r2539_nwasHoldingKnownResult (step s i))) as [flag|flag].
  - unfold v59797; rewrite flag; rewrite Z.land_0_l; reflexivity.
  - pose proof (holding_disabled s i flag) as disabled.
    pose proof (f_equal nio_5Fresult (ArrayHold.output_hold s i i later disabled)) as held.
    change (v16460 (step s i) later = v16460 s i) in held.
    assert (good : v59796 (step s i) later = 1).
    { unfold v59796.
      change (word 1 (if Z.eqb (v16460 (step s i) later) (word 130 (v16460 s i)) then 1 else 0) = 1).
      rewrite held, result_normal, Z.eqb_refl; reflexivity. }
    apply Bool.orb_true_intro; right; apply Z.eqb_eq; exact good.
Qed.

(* Glue preserves the original order and both independent top-level obligations. *)
Theorem all_checks (s : State) (i : Inputs)
  (product : orb (negb (Z.eqb (v59795 s i) 1)) (Z.eqb (v59793 s i) 1) = true)
  (stall : orb (negb (Z.eqb (v59797 s i) 1)) (Z.eqb (v59796 s i) 1) = true) :
  asserts s i.
Proof.
  unfold asserts; rewrite checks_split, forallb_app.
  pose proof (all_compressor_assertions s i) as local.
  change (forallb (fun b => b) (concat (compressor_batches s i)) = true) in local.
  rewrite local; cbn [forallb]; rewrite product, stall; reflexivity.
Qed.

(* Explicitly excludes only index 3479: the pending pipeline-product assertion. *)
Theorem all_except_product_after_edge (s : State) (i later : Inputs) :
  let checks := assertionChecks (step s i) later in
  forallb (fun b => b) (firstn 3479 checks ++ skipn 3480 checks) = true.
Proof.
  cbn zeta; rewrite forallb_app, all_compressor_assertions.
  change (true && (orb (negb (Z.eqb (v59797 (step s i) later) 1))
      (Z.eqb (v59796 (step s i) later) 1) && true) = true)%bool.
  rewrite stall_check; reflexivity.
Qed.
Print Assumptions stall_check.
Print Assumptions all_except_product_after_edge.
End ArrayStall.
