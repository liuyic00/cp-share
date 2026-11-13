From Coq Require Import ZArith Lia List Bool.
From Generated Require Import Adder.
Import Adder.CIRCTBits Adder.nAdder.
Open Scope Z_scope.

Lemma word_idempotent w x (hw : 0 <= w) : word w (word w x) = word w x.
Proof. unfold word. apply Z.mod_mod. apply Z.pow_nonzero; lia. Qed.

(* Same overflow-aware result as nAdder.result_correct in Lean. *)
Theorem result_correct (s : State) (i : Inputs) :
  nio_5Fout (observe s i) =
    if Z.eqb (word 1 (nio_5Fvalid i)) 1
    then word 8 (word 8 (nio_5Fin1 i) + word 8 (nio_5Fin2 i))
    else 0.
Proof.
  unfold observe, v2, v1, v0; cbn [nio_5Fout].
  destruct (Z.eqb (word 1 (nio_5Fvalid i)) 1).
  - apply word_idempotent; lia.
  - reflexivity.
Qed.

(* Same universal source assertion as nAdder.assertions_hold in Lean. *)
Theorem assertions_hold (s : State) (i : Inputs) : asserts s i.
Proof.
  assert (valid_cases : word 1 (nio_5Fvalid i) = 0 \/ word 1 (nio_5Fvalid i) = 1).
  { unfold word. pose proof (Z.mod_pos_bound (nio_5Fvalid i) 2 ltac:(lia)).
    change (2 ^ 1) with 2. lia. }
  unfold asserts, assertionChecks, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  destruct valid_cases as [h|h]; rewrite h;
    cbn [forallb orb negb Z.eqb Pos.eqb andb];
    repeat rewrite word_idempotent by lia;
    try rewrite Z.eqb_refl;
    cbn [word Z.pow Z.modulo Z.lxor Z.land Z.lor Z.eqb];
    try rewrite Bool.orb_true_r; try reflexivity.
Qed.

Print Assumptions result_correct.
Print Assumptions assertions_hold.
