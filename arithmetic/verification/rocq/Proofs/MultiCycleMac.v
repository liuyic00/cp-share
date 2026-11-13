From Coq Require Import ZArith Lia List Bool.
From Generated Require Import MultiCycleMac.
From Proofs Require Import Words.
Import MultiCycleMac.CIRCTBits MultiCycleMac.nMultiCycleMac.
Open Scope Z_scope.

Theorem reset_idle (s : State) (i : Inputs) (reset : word 1 (nreset i) = 1) :
  r0_nstate (step s i) = 0.
Proof. unfold step; cbn [r0_nstate]; rewrite reset; reflexivity. Qed.

Lemma accepting_state (s : State) (i : Inputs)
  (idle : word 2 (r0_nstate s) = 0)
  (reset : word 1 (nreset i) = 0) (valid : word 1 (nio_5Fin_5Fvalid i) = 1) :
  r0_nstate (step s i) = 1.
Proof.
  unfold step; cbn [r0_nstate].
  unfold v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite idle, reset, valid. reflexivity.
Qed.

Lemma adding_state (s : State) (i : Inputs)
  (adding : word 2 (r0_nstate s) = 1)
  (reset : word 1 (nreset i) = 0) :
  r0_nstate (step s i) = 2.
Proof.
  unfold step; cbn [r0_nstate]. unfold v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite adding, reset. reflexivity.
Qed.

Lemma multiplying_state (s : State) (i : Inputs)
  (multiplying : word 2 (r0_nstate s) = 2)
  (reset : word 1 (nreset i) = 0) :
  r0_nstate (step s i) = 3.
Proof.
  unfold step; cbn [r0_nstate]. unfold v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite multiplying, reset. reflexivity.
Qed.

Lemma output_valid (s : State) (i : Inputs)
  (done : word 2 (r0_nstate s) = 3)
  (reset : word 1 (nreset i) = 0) :
  nio_5Fout_5Fvalid (observe s i) = 1.
Proof. unfold observe; cbn [nio_5Fout_5Fvalid].
  unfold v11, v10, v9, v8, v6. rewrite done, reset. reflexivity.
Qed.

Theorem no_early_output (s : State) (accept add multiply : Inputs)
  (idle : word 2 (r0_nstate s) = 0)
  (r0 : word 1 (nreset accept) = 0) (valid : word 1 (nio_5Fin_5Fvalid accept) = 1)
  (r1 : word 1 (nreset add) = 0) (r2 : word 1 (nreset multiply) = 0) :
  nio_5Fout_5Fvalid (observe (step s accept) add) = 0 /\
  nio_5Fout_5Fvalid (observe (step (step s accept) add) multiply) = 0.
Proof.
  pose proof (accepting_state s accept idle r0 valid) as h1.
  assert (h2 : word 2 (r0_nstate (step s accept)) = 1) by (rewrite h1; reflexivity).
  pose proof (adding_state _ add h2 r1) as h3.
  unfold observe; cbn [nio_5Fout_5Fvalid].
  unfold v11, v10, v9, v8, v6.
  rewrite h1, h3, r1, r2. split; reflexivity.
Qed.

Print Assumptions reset_idle.
Print Assumptions no_early_output.

Lemma capture_operands (s : State) (i : Inputs)
  (idle : word 2 (r0_nstate s) = 0)
  (reset : word 1 (nreset i) = 0) (valid : word 1 (nio_5Fin_5Fvalid i) = 1) :
  r1_noperands_5Fa (step s i) = word 8 (nio_5Fin_5Fbits_5Fa i) /\
  r2_noperands_5Fb (step s i) = word 8 (nio_5Fin_5Fbits_5Fb i) /\
  r3_noperands_5Fc (step s i) = word 8 (nio_5Fin_5Fbits_5Fc i).
Proof.
  unfold step; cbn [r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc].
  unfold v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite idle, reset, valid.
  change (word 8 (word 8 (nio_5Fin_5Fbits_5Fa i)) = word 8 (nio_5Fin_5Fbits_5Fa i) /\
          word 8 (word 8 (nio_5Fin_5Fbits_5Fb i)) = word 8 (nio_5Fin_5Fbits_5Fb i) /\
          word 8 (word 8 (nio_5Fin_5Fbits_5Fc i)) = word 8 (nio_5Fin_5Fbits_5Fc i)).
  repeat split; apply Words.word_idem; lia.
Qed.

Lemma adding_sum (s : State) (i : Inputs)
  (adding : word 2 (r0_nstate s) = 1) :
  r4_nsum (step s i) = word 9 (word 8 (r1_noperands_5Fa s) + word 8 (r2_noperands_5Fb s)).
Proof.
  unfold step; cbn [r4_nsum]. unfold v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite adding.
  change (word 9 (word 9 (word 9 (word 8 (r1_noperands_5Fa s)) +
                          word 9 (word 8 (r2_noperands_5Fb s)))) = word 9 (word 8 (r1_noperands_5Fa s) + word 8 (r2_noperands_5Fb s))).
  rewrite Words.word_idem by lia.
  repeat rewrite Words.word_widen by lia. reflexivity.
Qed.

Lemma busy_operands (s : State) (i : Inputs)
  (busy : word 2 (r0_nstate s) <> 0) :
  r1_noperands_5Fa (step s i) = word 8 (r1_noperands_5Fa s) /\
  r2_noperands_5Fb (step s i) = word 8 (r2_noperands_5Fb s) /\
  r3_noperands_5Fc (step s i) = word 8 (r3_noperands_5Fc s).
Proof.
  unfold step; cbn [r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc].
  unfold v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  assert (h : (word 2 (r0_nstate s) =? word 2 0) = false) by (apply Z.eqb_neq; exact busy).
  rewrite h.
  change (word 8 (word 8 (r1_noperands_5Fa s)) = word 8 (r1_noperands_5Fa s) /\
          word 8 (word 8 (r2_noperands_5Fb s)) = word 8 (r2_noperands_5Fb s) /\
          word 8 (word 8 (r3_noperands_5Fc s)) = word 8 (r3_noperands_5Fc s)).
  repeat split; apply Words.word_idem; lia.
Qed.

Lemma multiplying_result (s : State) (i : Inputs)
  (multiplying : word 2 (r0_nstate s) = 2) :
  r5_nresult (step s i) = word 17 (word 9 (r4_nsum s) * word 8 (r3_noperands_5Fc s)).
Proof.
  unfold step; cbn [r5_nresult]. unfold v39, v38, v37, v36, v35, v34, v33, v32, v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite multiplying.
  change (word 17 (word 17 (word 17 (word 9 (r4_nsum s)) *
                             word 17 (word 8 (r3_noperands_5Fc s)))) = word 17 (word 9 (r4_nsum s) * word 8 (r3_noperands_5Fc s))).
  rewrite Words.word_idem by lia.
  repeat rewrite Words.word_widen by lia. reflexivity.
Qed.

Definition arithmetic (a b c : Z) : Z :=
  word 17 (word 9 (word 8 a + word 8 b) * word 8 c).

Lemma output_bits (s : State) (i : Inputs)
  (done : word 2 (r0_nstate s) = 3)
  (reset : word 1 (nreset i) = 0) :
  nio_5Fout_5Fbits (observe s i) = word 17 (r5_nresult s).
Proof.
  unfold observe; cbn [nio_5Fout_5Fbits].
  unfold v46, v45, v11, v10, v9, v8, v6. rewrite done, reset.
  change (word 17 (word 17 (r5_nresult s)) = word 17 (r5_nresult s)).
  apply Words.word_idem; lia.
Qed.

(* The same accepted operands, exact latency and arbitrary later inputs as Lean. *)
Theorem completes_after_two (s : State) (accept add multiply output : Inputs)
  (idle : word 2 (r0_nstate s) = 0)
  (r0 : word 1 (nreset accept) = 0) (valid : word 1 (nio_5Fin_5Fvalid accept) = 1)
  (r1 : word 1 (nreset add) = 0) (r2 : word 1 (nreset multiply) = 0)
  (r3 : word 1 (nreset output) = 0) :
  let final := observe (step (step (step s accept) add) multiply) output in
  nio_5Fout_5Fvalid final = 1 /\
  nio_5Fout_5Fbits final = arithmetic (nio_5Fin_5Fbits_5Fa accept)
    (nio_5Fin_5Fbits_5Fb accept) (nio_5Fin_5Fbits_5Fc accept).
Proof.
  pose proof (accepting_state s accept idle r0 valid) as hs1.
  assert (h1 : word 2 (r0_nstate (step s accept)) = 1) by (rewrite hs1; reflexivity).
  pose proof (adding_state _ add h1 r1) as hs2.
  assert (h2 : word 2 (r0_nstate (step (step s accept) add)) = 2) by (rewrite hs2; reflexivity).
  pose proof (multiplying_state _ multiply h2 r2) as hs3.
  assert (h3 : word 2 (r0_nstate (step (step (step s accept) add) multiply)) = 3)
    by (rewrite hs3; reflexivity).
  cbn zeta. split; [apply output_valid; assumption|].
  rewrite output_bits by assumption.
  rewrite multiplying_result by assumption.
  rewrite adding_sum by assumption.
  destruct (capture_operands s accept idle r0 valid) as [ha [hb hc]].
  destruct (busy_operands (step s accept) add ltac:(rewrite h1; lia)) as [_ [_ hc2]].
  rewrite hc2, ha, hb, hc.
  unfold arithmetic. repeat rewrite Words.word_idem by lia. reflexivity.
Qed.

Theorem arithmetic_to_Z (a b c : Z) :
  arithmetic a b c = (word 8 a + word 8 b) * word 8 c.
Proof.
  pose proof (Words.word_bound 8 a ltac:(lia)) as ha.
  pose proof (Words.word_bound 8 b ltac:(lia)) as hb.
  pose proof (Words.word_bound 8 c ltac:(lia)) as hc.
  change (2^8) with 256 in ha, hb, hc.
  unfold arithmetic.
  change (Words.word 17 (Words.word 9 (Words.word 8 a + Words.word 8 b) * Words.word 8 c) = (Words.word 8 a + Words.word 8 b) * Words.word 8 c).
  rewrite (Words.word_small 9 (Words.word 8 a + Words.word 8 b)) by (change (2^9) with 512; lia).
  apply Words.word_small. change (2^17) with 131072. nia.
Qed.

Print Assumptions completes_after_two.
Print Assumptions arithmetic_to_Z.
