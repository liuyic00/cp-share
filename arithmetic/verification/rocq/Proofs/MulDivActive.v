From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivStall.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl.
Open Scope Z_scope.
Module MulDivActive.
Definition Active s :=
  (word 3 (r0_nstate s)=1 /\ word 7 (r3_ncount s)=0) \/
  (word 3 (r0_nstate s)=2 /\ word 7 (r3_ncount s)<64) \/
  (word 3 (r0_nstate s)=3 /\ word 7 (r3_ncount s)<=64) \/
  word 3 (r0_nstate s)=5 \/ word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7.
Lemma active_not_idle s (active : Active s) : word 3 (r0_nstate s)<>0.
Proof. unfold Active in active; intuition lia. Qed.
Lemma capture_active s i (accepted : v2 s i=1) (reset : word 1 (nreset i)=0) : Active (step s i).
Proof.
  assert (mul : v6 s i=0 \/ v6 s i=1) by (unfold v6; apply bit_cases).
  pose proof (v32_bit s i) as neg.
  unfold Active; cbn [step r0_nstate r3_ncount]; rewrite reset; unfold v61,v73; rewrite accepted; clean.
  unfold v34,v33,v67,v66,v65,v64,v7,v8,v31.
  destruct mul as [mul|mul]; destruct neg as [neg|neg];
    destruct (bit_cases (nio_5Freq_5Fbits_5Fdw i)) as [width|width]; rewrite mul,neg,width; vm_compute; intuition discriminate.
Qed.
Lemma uncancelled s i (live : v40 s i=0) : word 1 (nio_5Fkill i)=0.
Proof.
  assert (ready : v39 s i=0 \/ v39 s i=1) by (unfold v39; apply bit_cases).
  unfold v40 in live; destruct ready as [r|r]; destruct (bit_cases (nio_5Fkill i)) as [k|k]; rewrite r,k in live; try discriminate; exact k.
Qed.
Lemma stalled_done s i (done : word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7)
  (live : v40 s i=0) : word 1 (nio_5Fresp_5Fready i)=0.
Proof.
  pose proof (done_valid s i done) as valid; change (v38 s i=1) in valid.
  pose proof (uncancelled s i live) as kill.
  unfold v40,v39 in live; rewrite kill,valid in live.
  destruct (bit_cases (nio_5Fresp_5Fready i)) as [r|r]; [exact r|rewrite r in live; discriminate].
Qed.
Lemma increment_small s (count : word 7 (r3_ncount s)<65) :
  word 7 (word 7 (r3_ncount s)+1)=word 7 (r3_ncount s)+1.
Proof.
  apply Words.word_small.
  pose proof (Words.word_bound 7 (r3_ncount s) ltac:(lia)) as bound.
  change (0<=word 7 (r3_ncount s)<128) in bound; change (0<=word 7 (r3_ncount s)+1<128); lia.
Qed.
Theorem active_edge s i (active : Active s) (reset : word 1 (nreset i)=0) (live : v40 s i=0) : Active (step s i).
Proof.
  pose proof (uncancelled s i live) as kill.
  destruct active as [[st ct]|[[st ct]|[[st ct]|[st|done]]]].
  - unfold Active; right; right; left; rewrite (negate_inputs_state s i st reset kill),(negate_inputs_count s i st),normalize,ct by lia; split; [reflexivity|lia].
  - unfold Active; rewrite (mul_state s i st reset kill),(compute_count s i (or_introl st)),normalize by lia.
    destruct (word 7 (r3_ncount s)=?63) eqn:last.
    + right; right; right; right; left; reflexivity.
    + apply Z.eqb_neq in last; right; left; rewrite increment_small by lia; split; [reflexivity|lia].
  - unfold Active; rewrite (div_state s i st reset kill),(compute_count s i (or_intror st)),normalize by lia.
    destruct (word 7 (r3_ncount s)=?64) eqn:last.
    + destruct (word 1 (r4_nneg_5Fout s)=?1); [right; right; right; left|right; right; right; right; right]; reflexivity.
    + apply Z.eqb_neq in last; right; right; left; rewrite increment_small by lia; split; [reflexivity|lia].
  - unfold Active; right; right; right; right; right; rewrite (negate_output_state s i st reset kill); reflexivity.
  - destruct (MulDivStall.MulDivStall.done_registers s i done reset kill (stalled_done s i done live)) as [st rest].
    unfold Active; right; right; right; right; rewrite st,normalize by lia; exact done.
Qed.
End MulDivActive.
Print Assumptions MulDivActive.capture_active.
Print Assumptions MulDivActive.active_edge.
