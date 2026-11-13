From Coq Require Import ZArith Lia List Bool.
From Generated Require Import MultiCycleMac.
From Proofs Require Import Words MultiCycleMac.
Import Generated.MultiCycleMac.CIRCTBits Generated.MultiCycleMac.nMultiCycleMac.
Open Scope Z_scope.

Ltac unfold_mac :=
  unfold step, observe;
  cbn [r0_nstate r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc r4_nsum r5_nresult r6_naccepted r7_nwasAdding r8_nwasMultiplying r9_nstalled r10_npreviousOutput nio_5Fin_5Fready nio_5Fout_5Fvalid nio_5Fout_5Fbits];
  unfold v60, v59, v58, v57, v56, v55, v54, v53, v52, v51, v50, v49, v48, v47, v46, v45, v44, v43, v42, v41, v40, v39, v38, v37, v36, v35, v34, v33, v32, v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.

Ltac mac_constants :=
  repeat first [progress Words.word_constants |
    match goal with |- context[word ?w ?x] =>
      integer_literal w; integer_literal x;
      let v := eval vm_compute in (word w x) in change (word w x) with v
    end | progress cbn beta iota zeta delta [negb orb andb] |
    rewrite Words.word_idem by lia |
    rewrite Words.word_widen by lia |
    rewrite Z.shiftl_0_l | rewrite Z.add_0_l | rewrite Z.land_0_l |
    rewrite Z.land_0_r | rewrite Z.lor_0_l | rewrite Z.lor_0_r |
    rewrite Z.eqb_refl].

Theorem stall_stable (s : State) (i j : Inputs)
  (state : word 2 (r0_nstate s) = 3) (reset : word 1 (nreset i) = 0)
  (ready : word 1 (nio_5Fout_5Fready i) = 0) (nextReset : word 1 (nreset j) = 0) :
  nio_5Fout_5Fvalid (observe (step s i) j) = 1 /\
  nio_5Fout_5Fbits (observe (step s i) j) = nio_5Fout_5Fbits (observe s i).
Proof.
  assert (hs : r0_nstate (step s i) = 3).
  { unfold_mac. rewrite state, reset, ready. reflexivity. }
  assert (hr : r5_nresult (step s i) = word 17 (r5_nresult s)).
  { unfold_mac. rewrite state. mac_constants. reflexivity. }
  split.
  - apply output_valid; [rewrite hs; reflexivity|assumption].
  - rewrite !output_bits by (try assumption; rewrite hs; reflexivity).
    rewrite hr. apply Words.word_idem; lia.
Qed.

(* The Lean stage/history invariant over the corresponding finite-word values. *)
Definition Invariant (s : State) : Prop :=
  ((word 2 (r0_nstate s) = 2 \/ word 2 (r0_nstate s) = 3) ->
    word 9 (r4_nsum s) = word 9 (word 8 (r1_noperands_5Fa s) + word 8 (r2_noperands_5Fb s))) /\
  (word 2 (r0_nstate s) = 3 -> word 17 (r5_nresult s) =
    arithmetic (r1_noperands_5Fa s) (r2_noperands_5Fb s) (r3_noperands_5Fc s)) /\
  (word 1 (r6_naccepted s) = 1 -> word 2 (r0_nstate s) = 1) /\
  (word 1 (r7_nwasAdding s) = 1 -> word 2 (r0_nstate s) = 2) /\
  (word 1 (r8_nwasMultiplying s) = 1 -> word 2 (r0_nstate s) = 3) /\
  (word 1 (r9_nstalled s) = 1 -> word 2 (r0_nstate s) = 3 /\
    word 17 (r10_npreviousOutput s) = word 17 (r5_nresult s)).

Theorem reset_invariant (s : State) (i : Inputs) (reset : word 1 (nreset i) = 1) :
  Invariant (step s i).
Proof.
  unfold Invariant. unfold_mac. rewrite reset. mac_constants.
  intuition discriminate.
Qed.

Lemma state_cases x : word 2 x = 0 \/ word 2 x = 1 \/ word 2 x = 2 \/ word 2 x = 3.
Proof. pose proof (Words.word_bound 2 x ltac:(lia)); change (0 <= word 2 x < 4) in H. lia. Qed.

Lemma mac_bit_cases x : word 1 x = 0 \/ word 1 x = 1.
Proof. exact (Words.bit_cases x). Qed.

Theorem invariant_step (s : State) (i : Inputs) (h : Invariant s) :
  Invariant (step s i).
Proof.
  destruct (state_cases (r0_nstate s)) as [hs|[hs|[hs|hs]]];
  destruct (mac_bit_cases (nreset i)) as [hr|hr];
  destruct (mac_bit_cases (nio_5Fin_5Fvalid i)) as [hv|hv];
  destruct (mac_bit_cases (nio_5Fout_5Fready i)) as [hd|hd];
  unfold Invariant in *;
  unfold_mac; rewrite hs, hr, hv, hd;
  unfold arithmetic in *;
  mac_constants;
  rewrite hs in h;
  intuition (try congruence).
  all: unfold Words.word, word in *; congruence.
Qed.

Theorem invariant_asserts (s : State) (i : Inputs) (h : Invariant s) : asserts s i.
Proof.
  destruct (state_cases (r0_nstate s)) as [hs|[hs|[hs|hs]]];
  destruct (mac_bit_cases (r6_naccepted s)) as [ha|ha];
  destruct (mac_bit_cases (r7_nwasAdding s)) as [hb|hb];
  destruct (mac_bit_cases (r8_nwasMultiplying s)) as [hc|hc];
  destruct (mac_bit_cases (r9_nstalled s)) as [hd|hd];
  unfold Invariant in h; rewrite hs, ha, hb, hc, hd in h;
  try solve [intuition discriminate];
  destruct (mac_bit_cases (nreset i)) as [hr|hr];
  unfold asserts, assertionChecks;
  unfold_mac; rewrite hs, ha, hb, hc, hd, hr;
  unfold arithmetic in *; mac_constants;
  cbn [forallb];
  intuition (try discriminate).
  all: unfold word, Words.word in *;
    repeat match goal with
    | |- context[Z.eqb ?a ?b] =>
      let E := fresh "eqbit" in
      assert (E : Z.eqb a b = true) by (apply Z.eqb_eq; congruence);
      rewrite E; clear E
    end;
    cbn [negb orb andb]; try reflexivity.
Qed.

Theorem assertions_after_reset (s : State) (resetInput : Inputs)
  (reset : word 1 (nreset resetInput) = 1) (inputs : nat -> Inputs) (n : nat) :
  asserts (run (step s resetInput) inputs n) (inputs n).
Proof.
  apply invariant_asserts. induction n as [|n IH].
  - exact (reset_invariant s resetInput reset).
  - apply invariant_step; exact IH.
Qed.

Print Assumptions stall_stable.
Print Assumptions assertions_after_reset.
