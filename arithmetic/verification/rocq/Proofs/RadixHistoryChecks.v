From Coq Require Import ZArith Lia Bool List.
From Proofs Require Import Words RadixControl.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl.
Open Scope Z_scope.
Module RadixHistoryChecks.
Lemma bit_cases x : word 1 x = 0 \/ word 1 x = 1.
Proof. apply Words.bit_cases. Qed.
Lemma triple_enabled a b c
  (ha : word 1 a = a) (hb : word 1 b = b) (hc : word 1 c = c)
  (h : word 1 (Z.land (Z.land a b) c) = 1) : a=1 /\ b=1 /\ c=1.
Proof.
  destruct (bit_cases a) as [a0|a1]; destruct (bit_cases b) as [b0|b1]; destruct (bit_cases c) as [c0|c1];
    rewrite ha in *; rewrite hb in *; rewrite hc in *;
    subst; try discriminate; repeat split; reflexivity.
Qed.
Lemma eq_enabled a b (h : word 1 (if a =? b then 1 else 0) = 1) : a=b.
Proof. destruct (a =? b) eqn:e; [apply Z.eqb_eq; exact e | discriminate]. Qed.
Lemma history_reset s i (h : word 1 (r10_nhistoryValid (step s i)) = 1) : word 1 (nreset i) = 0.
Proof.
  cbn [step r10_nhistoryValid] in h.
  destruct (bit_cases (nreset i)) as [hr|hr]; [exact hr | rewrite hr in h; discriminate].
Qed.
Lemma previous_state s i : word 3 (r11_npreviousState (step s i)) = word 3 (r0_nstate s).
Proof. cbn [step r11_npreviousState]; apply normalize; lia. Qed.
Lemma checked enable value (h : enable=1 -> value=1) :
  orb (negb (enable =? 1)) (value =? 1) = true.
Proof. destruct (enable =? 1) eqn:e; [apply Z.eqb_eq in e; rewrite (h e); reflexivity | reflexivity]. Qed.
Local Opaque step.
Theorem log2_check s i j :
  orb (negb (v433 (step s i) j =? 1)) (v6 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled.
  unfold v433 in enabled.
  destruct (triple_enabled _ _ _ ltac:(apply normalize; lia)
    ltac:(unfold v432; apply normalize; lia)
    ltac:(unfold v415; apply normalize; lia) enabled) as [history [prev active]].
  apply history_reset in history.
  unfold v432, v3 in prev; change (word 3 1) with 1 in prev.
  apply eq_enabled in prev; rewrite previous_state in prev.
  unfold v6, v5; rewrite (log2_state s i history prev); reflexivity.
Qed.
Theorem shift_check s i j :
  orb (negb (v435 (step s i) j =? 1)) (v8 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled.
  unfold v435 in enabled.
  destruct (triple_enabled _ _ _ ltac:(apply normalize; lia)
    ltac:(unfold v434; apply normalize; lia)
    ltac:(unfold v415; apply normalize; lia) enabled) as [history [prev active]].
  apply history_reset in history.
  unfold v434, v5 in prev; change (word 3 2) with 2 in prev.
  apply eq_enabled in prev; rewrite previous_state in prev.
  unfold v8, v7; rewrite (shift_state s i history prev); reflexivity.
Qed.
Local Transparent step.
Lemma previous_count s i : word 6 (r12_npreviousCount (step s i)) = word 6 (r9_ncnt_5Fvalue s).
Proof. cbn [step r12_npreviousCount]; apply normalize; lia. Qed.
Local Opaque step.
Lemma compute_enabled s i j (enabled : v440 (step s i) j = 1) :
  word 1 (nreset i) = 0 /\ word 3 (r0_nstate s) = 3.
Proof.
  unfold v440 in enabled.
  destruct (triple_enabled _ _ _ ltac:(apply normalize; lia)
    ltac:(unfold v439; apply normalize; lia)
    ltac:(unfold v415; apply normalize; lia) enabled) as [history [prev active]].
  apply history_reset in history.
  unfold v439, v7 in prev; change (word 3 3) with 3 in prev.
  apply eq_enabled in prev; rewrite previous_state in prev; auto.
Qed.
Theorem compute_state_check s i j :
  orb (negb (v440 (step s i) j =? 1)) (v438 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled; destruct (compute_enabled s i j enabled) as [hr hs].
  unfold v438, v437, v436, v9, v11, v7.
  rewrite previous_count, (compute_state s i hr hs).
  change (word 6 63) with 63.
  destruct (word 6 (r9_ncnt_5Fvalue s) =? 63); reflexivity.
Qed.
Theorem compute_count_check s i j :
  orb (negb (v440 (step s i) j =? 1)) (v443 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled; destruct (compute_enabled s i j enabled) as [hr hs].
  unfold v443, v442, v441, v436, v394, v9, v62.
  rewrite previous_count, (compute_count s i hr hs), normalize by lia.
  change (word 6 63) with 63; change (word 6 1) with 1; change (word 6 0) with 0.
  destruct (word 6 (r9_ncnt_5Fvalue s) =? 63) eqn:h.
  - apply Z.eqb_eq in h; rewrite h; reflexivity.
  - change (word 1 (if word 6 (word 6 (r9_ncnt_5Fvalue s)+1) =? word 6 (word 6 (word 6 (r9_ncnt_5Fvalue s)+1)) then 1 else 0)=1).
    rewrite normalize, Z.eqb_refl by lia; reflexivity.
Qed.
Lemma pair_enabled a b (ha : word 1 a = a) (hb : word 1 b = b)
  (h : word 1 (Z.land a b) = 1) : a=1 /\ b=1.
Proof.
  destruct (bit_cases a) as [a0|a1]; destruct (bit_cases b) as [b0|b1];
    rewrite ha in *; rewrite hb in *; subst; try discriminate; split; reflexivity.
Qed.
Local Transparent step.
Lemma stalled_history s i (h : word 1 (r13_nwasStalled (step s i)) = 1) :
  word 1 (nreset i) = 0 /\ word 3 (r0_nstate s) = 4 /\ word 1 (nio_5Fout_5Fready i) = 0.
Proof.
  cbn [step r13_nwasStalled] in h.
  destruct (bit_cases (nreset i)) as [hr|hr]; rewrite hr in h; [|discriminate].
  change (word 1 (v401 s i)=1) in h; unfold v401 in h; rewrite normalize in h by lia.
  destruct (pair_enabled _ _ ltac:(unfold v399; apply normalize; lia)
    ltac:(unfold v400; apply normalize; lia) h) as [hs ready].
  unfold v399, v11 in hs; change (word 3 4) with 4 in hs; apply eq_enabled in hs.
  split; [exact hr | split; [exact hs |]].
  unfold v400, v22 in ready.
  destruct (bit_cases (nio_5Fout_5Fready i)) as [h0|h1]; [exact h0 | rewrite h1 in ready; discriminate].
Qed.
Lemma previous_output s i : word 64 (r14_npreviousOutput (step s i)) = v412 s i.
Proof. cbn [step r14_npreviousOutput]; unfold v412; apply normalize; lia. Qed.
Local Opaque step.
Lemma stalled_enabled s i j (h : v444 (step s i) j = 1) :
  word 1 (nreset i) = 0 /\ word 3 (r0_nstate s) = 4 /\ word 1 (nio_5Fout_5Fready i) = 0.
Proof.
  unfold v444 in h.
  destruct (pair_enabled _ _ ltac:(apply normalize; lia)
    ltac:(unfold v415; apply normalize; lia) h) as [past active].
  apply stalled_history; exact past.
Qed.
Theorem stalled_valid_check s i j :
  orb (negb (v444 (step s i) j =? 1)) (v399 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled; destruct (stalled_enabled s i j enabled) as [hr [hs ready]].
  exact (proj1 (stall_stable s i j hs hr ready)).
Qed.
Theorem stalled_data_check s i j :
  orb (negb (v444 (step s i) j =? 1)) (v445 (step s i) j =? 1) = true.
Proof.
  apply checked; intro enabled; destruct (stalled_enabled s i j enabled) as [hr [hs ready]].
  pose proof (proj2 (stall_stable s i j hs hr ready)) as data.
  change (v412 (step s i) j = v412 s i) in data.
  unfold v445; rewrite previous_output, data, Z.eqb_refl; reflexivity.
Qed.
Theorem temporal_assertions_step s i j :
  forallb (fun b => b) (skipn 5 (assertionChecks (step s i) j)) = true.
Proof.
  unfold assertionChecks; cbn [skipn forallb].
  rewrite log2_check, shift_check, compute_state_check, compute_count_check, stalled_valid_check, stalled_data_check; reflexivity.
Qed.
Theorem temporal_assertions_run s first inputs n :
  forallb (fun b => b) (skipn 5 (assertionChecks (run (step s first) inputs n) (inputs n))) = true.
Proof.
  destruct n; [exact (temporal_assertions_step s first (inputs O)) |].
  change (forallb (fun b => b) (skipn 5 (assertionChecks (step (run (step s first) inputs n) (inputs n)) (inputs (S n)))) = true).
  apply temporal_assertions_step.
Qed.
End RadixHistoryChecks.
Print Assumptions RadixHistoryChecks.log2_check.
Print Assumptions RadixHistoryChecks.shift_check.
Print Assumptions RadixHistoryChecks.compute_state_check.
Print Assumptions RadixHistoryChecks.compute_count_check.
Print Assumptions RadixHistoryChecks.temporal_assertions_run.
