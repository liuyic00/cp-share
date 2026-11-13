From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMulSpec MulDivCheckedHistory MulDivCheckedAge.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge.
Open Scope Z_scope.
Module MulDivCheckedMulFuture.
Module M := MulDivCheckedMulSpec.MulDivCheckedMulSpec.
Module Core := MulDiv.nMulDiv.
Module T := MulDivTiming.MulDivTiming.
Definition remaining s := (64-Z.to_nat (word 7 (r3_ncount s)))%nat.
Definition Computing s := forall pins, T.active pins (remaining s) ->
  Core.nio_5Fresp_5Fbits_5Fdata (Core.observe (Core.run (P.state s) pins (remaining s)) (pins (remaining s)))=M.specification (captured s).
Lemma capture_spec s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1) :
  M.specification (captured (step s i))=M.specification (P.inputs i).
Proof.
  rewrite (capture s i idle valid); apply M.specification_congruent;
    cbn [requestView P.inputs Core.nio_5Freq_5Fbits_5Ffn Core.nio_5Freq_5Fbits_5Fdw Core.nio_5Freq_5Fbits_5Fin1 Core.nio_5Freq_5Fbits_5Fin2];
    apply Words.word_idem; lia.
Qed.
Lemma capture_count s i (accepted : v2 s i=1) (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)<4) :
  word 7 (r3_ncount (step s i))=if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then 0 else 32.
Proof.
  pose proof (bounds 4 (nio_5Freq_5Fbits_5Ffn i) ltac:(lia)) as bound.
  assert (cases : word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/
    word 4 (nio_5Freq_5Fbits_5Ffn i)=2 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=3) by lia.
  assert (mul : v6 s i=1) by (unfold v6,v5,v4,v3; destruct cases as [fn|[fn|[fn|fn]]]; rewrite fn; reflexivity).
  cbn [step r3_ncount]; unfold v73,v67,v66,v65,v64,v31,v8; rewrite accepted,mul.
  destruct (bit_cases (nio_5Freq_5Fbits_5Fdw i)) as [dw|dw]; rewrite dw; reflexivity.
Qed.
Local Opaque Core.run Core.step Core.observe run step observe.
Theorem capture_computing s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) (legal : M.Legal (P.inputs i)) : Computing (step s i).
Proof.
  assert (total : M.total (P.inputs i)=S (remaining (step s i))).
  { unfold remaining; rewrite (capture_count s i (accept s i idle valid) (proj1 legal)).
    unfold M.total; change (MulDiv.CIRCTBits.word 1 (Core.nio_5Freq_5Fbits_5Fdw (P.inputs i))) with (word 1 (nio_5Freq_5Fbits_5Fdw i)).
    destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); reflexivity. }
  intros pins live; set (extended := fun t => match t with O => P.inputs i | S n => pins n end).
  assert (all : T.active extended (M.total (extended O))).
  { change (T.active extended (M.total (P.inputs i))); rewrite total; intros t bound; destruct t as [|t]; [split; assumption|apply live; lia]. }
  pose proof (M.accepted_result (P.state s) extended idle valid legal all) as result.
  change (Core.nio_5Fresp_5Fbits_5Fdata (Core.observe (Core.run (P.state s) extended (M.total (P.inputs i))) (extended (M.total (P.inputs i))))=M.specification (P.inputs i)) in result.
  rewrite total,T.run_from_next in result.
  rewrite P.step_projects,(capture_spec s i idle valid); exact result.
Qed.
Theorem computing_step s i (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)<63)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) (computing : Computing s) : Computing (step s i).
Proof.
  assert (counter : word 7 (r3_ncount (step s i))=word 7 (r3_ncount s)+1).
  { change (word 7 (Core.r3_ncount (P.state (step s i)))=word 7 (r3_ncount s)+1).
    rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_introl state)).
    change (word 7 (word 7 (word 7 (r3_ncount s)+1))=word 7 (r3_ncount s)+1).
    rewrite normalize by lia; apply Words.word_small; pose proof (bounds 7 (r3_ncount s) ltac:(lia)); change (2^7) with 128 in *; lia. }
  assert (rest : remaining s=S (remaining (step s i))).
  { unfold remaining; rewrite counter,Z2Nat.inj_add by (pose proof (bounds 7 (r3_ncount s) ltac:(lia)); lia).
    change (Z.to_nat 1) with 1%nat; assert (small : (Z.to_nat (word 7 (r3_ncount s))<63)%nat) by lia; lia. }
  intros pins live; set (extended := fun t => match t with O => P.inputs i | S n => pins n end).
  assert (all : T.active extended (remaining s)).
  { rewrite rest; intros t bound; destruct t as [|t]; [split; assumption|apply live; lia]. }
  specialize (computing extended all); rewrite rest,T.run_from_next in computing.
  assert (busy : word 3 (r0_nstate s)<>0) by lia.
  rewrite P.step_projects,(hold s i (or_introl busy)); exact computing.
Qed.
Theorem computing_last s i later (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=63)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) (computing : Computing s) :
  nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=M.specification (captured (step s i)).
Proof.
  assert (rest : remaining s=1%nat) by (unfold remaining; rewrite count; reflexivity).
  set (pins := fun t : nat => match t with O => P.inputs i | S _ => P.inputs later end).
  assert (live : T.active pins (remaining s)).
  { rewrite rest; intros t bound; assert (t=O) by lia; subst t; split; assumption. }
  specialize (computing pins live); rewrite rest in computing.
  change (Core.nio_5Fresp_5Fbits_5Fdata (Core.observe (Core.step (P.state s) (P.inputs i)) (P.inputs later))=M.specification (captured s)) in computing.
  rewrite <-P.step_projects,<-P.observe_projects in computing.
  assert (busy : word 3 (r0_nstate s)<>0) by lia.
  rewrite (hold s i (or_introl busy)); exact computing.
Qed.
End MulDivCheckedMulFuture.
Print Assumptions MulDivCheckedMulFuture.capture_computing.
Print Assumptions MulDivCheckedMulFuture.computing_last.
