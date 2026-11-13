From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl.
Open Scope Z_scope.
Module RadixTemporal.
Lemma small w x (h : 0 <= x < 2^w) : word w x = x.
Proof. exact (Words.word_small w x h). Qed.
Lemma count_bound s : 0 <= word 6 (r9_ncnt_5Fvalue s) < 64.
Proof. exact (Words.word_bound 6 _ ltac:(lia)). Qed.
Theorem compute_finishes n s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (hc : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n = 64)
  (hr : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0) :
  word 3 (r0_nstate (run s inputs n)) = 4.
Proof.
  revert s inputs hs hc hr; induction n as [|n IH]; intros.
  - pose proof (count_bound s); cbn in hc; lia.
  - assert (hreset : word 1 (nreset (inputs O)) = 0) by (apply hr; lia).
    pose proof (compute_state s (inputs O) hreset hs) as hstate.
    destruct (Z.eqb (word 6 (r9_ncnt_5Fvalue s)) 63) eqn:heq.
    + apply Z.eqb_eq in heq.
      assert (hn : n = O) by (rewrite Nat2Z.inj_succ in hc; lia).
      subst n; change (word 3 (r0_nstate (step s (inputs O))) = 4).
      rewrite hstate; reflexivity.
    + apply Z.eqb_neq in heq.
      rewrite run_from_next. apply IH.
      * rewrite hstate; reflexivity.
      * rewrite (compute_count s (inputs O) hreset hs), normalize by lia.
        rewrite (small 6 (word 6 (r9_ncnt_5Fvalue s) + 1)).
        -- rewrite Nat2Z.inj_succ in hc; lia.
        -- pose proof (count_bound s); cbn; lia.
      * intros t ht; apply hr; lia.
Qed.
Lemma run_shift s inputs k n :
  run s inputs (n + k) = run (run s inputs k) (fun t => inputs (t + k)%nat) n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (step (run s inputs (n + k)) (inputs (n + k)%nat) =
    step (run (run s inputs k) (fun t => inputs (t + k)%nat) n) (inputs (n + k)%nat)).
  now rewrite IH.
Qed.
Theorem accepted_completes s inputs
  (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (hr : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1.
Proof.
  assert (h1 : r0_nstate (run s inputs 1) = 1).
  { apply accept_state; auto; apply hr; lia. }
  assert (h2 : r0_nstate (run s inputs 2) = 2).
  { exact (log2_state (run s inputs 1) (inputs 1%nat) (hr 1%nat ltac:(lia)) ltac:(rewrite h1; reflexivity)). }
  assert (h3 : word 3 (r0_nstate (run s inputs 3)) = 3).
  { change (word 3 (r0_nstate (step (run s inputs 2) (inputs 2%nat))) = 3).
    rewrite (shift_state (run s inputs 2) (inputs 2%nat) (hr 2%nat ltac:(lia)) ltac:(rewrite h2; reflexivity)); reflexivity. }
  set (c := word 6 (r9_ncnt_5Fvalue (run s inputs 3))).
  assert (hc : 0 <= c < 64) by apply count_bound.
  set (n := Z.to_nat (64 - c)).
  assert (hn : Z.of_nat n = 64 - c) by (unfold n; rewrite Z2Nat.id; lia).
  assert (hb : (1 <= n <= 64)%nat) by lia.
  exists (n + 3)%nat; split; [lia |].
  apply finish_valid. rewrite run_shift. apply compute_finishes.
  - exact h3.
  - change (c + Z.of_nat n = 64); lia.
  - intros t ht; apply hr; lia.
Qed.
End RadixTemporal.
Print Assumptions RadixTemporal.compute_finishes.
Print Assumptions RadixTemporal.accepted_completes.
