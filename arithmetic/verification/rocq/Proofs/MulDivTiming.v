From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl.
Open Scope Z_scope.
Module MulDivTiming.
Lemma small w x (h : 0<=x<2^w) : word w x=x.
Proof. exact (Words.word_small w x h). Qed.
Lemma count_bound s : 0<=word 7 (r3_ncount s)<128.
Proof. exact (Words.word_bound 7 _ ltac:(lia)). Qed.
Lemma run_from_next s inputs n : run s inputs (S n)=run (step s (inputs O)) (fun t => inputs (S t)) n.
Proof.
  induction n; [reflexivity|].
  change (step (run s inputs (S n)) (inputs (S n))=step (run (step s (inputs O)) (fun t => inputs (S t)) n) (inputs (S n))); now rewrite IHn.
Qed.
Definition active inputs n := forall t, (t<n)%nat -> word 1 (nreset (inputs t))=0 /\ word 1 (nio_5Fkill (inputs t))=0.
Theorem multiply_finishes n s inputs (hs : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)+Z.of_nat n=64) (live : active inputs n)
  (bound : word 7 (r3_ncount s)<64) : word 3 (r0_nstate (run s inputs n))=6.
Proof.
  revert s inputs hs count live bound; induction n as [|n IH]; intros.
  - cbn in count; lia.
  - destruct (live O ltac:(lia)) as [hr hk].
    pose proof (mul_state s (inputs O) hs hr hk) as next.
    destruct (word 7 (r3_ncount s)=?63) eqn:last.
    + apply Z.eqb_eq in last; assert (n=O) by (rewrite Nat2Z.inj_succ in count; lia); subst n.
      change (word 3 (r0_nstate (step s (inputs O)))=6); rewrite next; reflexivity.
    + apply Z.eqb_neq in last; rewrite run_from_next; apply IH.
      * rewrite next; reflexivity.
      * rewrite (compute_count s (inputs O) (or_introl hs)), normalize by lia.
        rewrite (small 7 (word 7 (r3_ncount s)+1)) by (pose proof (count_bound s); change (0<=word 7 (r3_ncount s)+1<128); lia).
        rewrite Nat2Z.inj_succ in count; lia.
      * intros t ht; apply live; lia.
      * rewrite (compute_count s (inputs O) (or_introl hs)), normalize by lia.
        rewrite (small 7 (word 7 (r3_ncount s)+1)) by (pose proof (count_bound s); change (0<=word 7 (r3_ncount s)+1<128); lia); lia.
Qed.
Theorem divide_finishes n s inputs (hs : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)+Z.of_nat n=65) (live : active inputs n)
  (bound : word 7 (r3_ncount s)<=64) :
  word 3 (r0_nstate (run s inputs n))=5 \/ word 3 (r0_nstate (run s inputs n))=7.
Proof.
  revert s inputs hs count live bound; induction n as [|n IH]; intros.
  - cbn in count; lia.
  - destruct (live O ltac:(lia)) as [hr hk].
    pose proof (div_state s (inputs O) hs hr hk) as next.
    destruct (word 7 (r3_ncount s)=?64) eqn:last.
    + apply Z.eqb_eq in last; assert (n=O) by (rewrite Nat2Z.inj_succ in count; lia); subst n.
      change (word 3 (r0_nstate (step s (inputs O)))=5 \/ word 3 (r0_nstate (step s (inputs O)))=7).
      rewrite next; destruct (word 1 (r4_nneg_5Fout s)=?1); [left|right]; reflexivity.
    + apply Z.eqb_neq in last; rewrite run_from_next; apply IH.
      * rewrite next; reflexivity.
      * rewrite (compute_count s (inputs O) (or_intror hs)), normalize by lia.
        rewrite (small 7 (word 7 (r3_ncount s)+1)) by (pose proof (count_bound s); change (0<=word 7 (r3_ncount s)+1<128); lia).
        rewrite Nat2Z.inj_succ in count; lia.
      * intros t ht; apply live; lia.
      * rewrite (compute_count s (inputs O) (or_intror hs)), normalize by lia.
        rewrite (small 7 (word 7 (r3_ncount s)+1)) by (pose proof (count_bound s); change (0<=word 7 (r3_ncount s)+1<128); lia); lia.
Qed.
Theorem divide_completes s inputs (hs : word 3 (r0_nstate s)=3)
  (bound : word 7 (r3_ncount s)<=64) (live : active inputs 66) :
  exists n, (1<=n<=66)%nat /\ nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1.
Proof.
  set (n := Z.to_nat (65-word 7 (r3_ncount s))).
  pose proof (count_bound s) as hb.
  assert (hn : Z.of_nat n=65-word 7 (r3_ncount s)) by (unfold n; rewrite Z2Nat.id; lia).
  assert (size : (1<=n<=65)%nat) by lia.
  destruct (divide_finishes n s inputs hs ltac:(lia) ltac:(unfold active; intros t ht; apply live; lia) bound) as [neg|done].
  - exists (S n); split; [lia|].
    apply done_valid; right.
    change (word 3 (r0_nstate (step (run s inputs n) (inputs n)))=7).
    destruct (live n ltac:(lia)) as [hr hk]; rewrite (negate_output_state _ _ neg hr hk); reflexivity.
  - exists n; split; [lia|]; apply done_valid; right; exact done.
Qed.
Theorem multiply_completes s inputs (hs : word 3 (r0_nstate s)=2)
  (bound : word 7 (r3_ncount s)<64) (live : active inputs 64) :
  exists n, (1<=n<=64)%nat /\ nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1.
Proof.
  set (n := Z.to_nat (64-word 7 (r3_ncount s))).
  pose proof (count_bound s) as hb.
  assert (hn : Z.of_nat n=64-word 7 (r3_ncount s)) by (unfold n; rewrite Z2Nat.id; lia).
  assert (size : (1<=n<=64)%nat) by lia.
  exists n; split; [exact size|].
  apply done_valid; left; apply multiply_finishes; try assumption; try lia.
  unfold active; intros t ht; apply live; lia.
Qed.
Theorem signed_divide_completes s inputs (hs : word 3 (r0_nstate s)=1)
  (bound : word 7 (r3_ncount s)<=64) (live : active inputs 67) :
  exists n, (2<=n<=67)%nat /\ nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1.
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  assert (next : word 3 (r0_nstate (step s (inputs O)))=3).
  { rewrite (negate_inputs_state s (inputs O) hs hr hk); reflexivity. }
  assert (count : word 7 (r3_ncount (step s (inputs O)))<=64).
  { rewrite (negate_inputs_count s (inputs O) hs), normalize by lia; exact bound. }
  destruct (divide_completes (step s (inputs O)) (fun t => inputs (S t)) next count
    ltac:(unfold active; intros t ht; apply live; lia)) as [n [size done]].
  exists (S n); split; [lia|].
  rewrite run_from_next; exact done.
Qed.
Local Opaque step run.
Theorem accepted_completes s inputs (hs : word 3 (r0_nstate s)=0)
  (hv : word 1 (nio_5Freq_5Fvalid (inputs O))=1) (live : active inputs 68) :
  exists n, (1<=n<=68)%nat /\ nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1.
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (acceptance s (inputs O) hs hv hr) as [state count].
  assert (bound : word 7 (r3_ncount (step s (inputs O)))<=32).
  { destruct count as [h|h]; rewrite h; vm_compute; discriminate. }
  destruct state as [mul|[neg|div]].
  - assert (st : word 3 (r0_nstate (step s (inputs O)))=2) by (rewrite mul; reflexivity).
    destruct (multiply_completes (step s (inputs O)) (fun t => inputs (S t)) st ltac:(lia)
      ltac:(unfold active; intros t ht; apply live; lia)) as [n [size done]].
    exists (S n); split; [lia|]; rewrite run_from_next; exact done.
  - assert (st : word 3 (r0_nstate (step s (inputs O)))=1) by (rewrite neg; reflexivity).
    destruct (signed_divide_completes (step s (inputs O)) (fun t => inputs (S t)) st ltac:(lia)
      ltac:(unfold active; intros t ht; apply live; lia)) as [n [size done]].
    exists (S n); split; [lia|]; rewrite run_from_next; exact done.
  - assert (st : word 3 (r0_nstate (step s (inputs O)))=3) by (rewrite div; reflexivity).
    destruct (divide_completes (step s (inputs O)) (fun t => inputs (S t)) st ltac:(lia)
      ltac:(unfold active; intros t ht; apply live; lia)) as [n [size done]].
    exists (S n); split; [lia|]; rewrite run_from_next; exact done.
Qed.
Theorem after_reset_completes initial resetInput inputs
  (hr : word 1 (nreset resetInput)=1)
  (hv : word 1 (nio_5Freq_5Fvalid (inputs O))=1) (live : active inputs 68) :
  exists n, (1<=n<=68)%nat /\
    nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs n) (inputs n))=1.
Proof.
  apply accepted_completes; try assumption.
  rewrite (reset_ready initial resetInput hr); reflexivity.
Qed.
End MulDivTiming.
Print Assumptions MulDivTiming.multiply_finishes.
Print Assumptions MulDivTiming.divide_completes.
Print Assumptions MulDivTiming.multiply_completes.
Print Assumptions MulDivTiming.signed_divide_completes.
Print Assumptions MulDivTiming.accepted_completes.
Print Assumptions MulDivTiming.after_reset_completes.
