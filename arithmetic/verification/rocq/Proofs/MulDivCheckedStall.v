From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedProjection MulDivCheckedHistory MulDivStall.
From Generated Require Import MulDiv MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory ListNotations.
Open Scope Z_scope.
Module MulDivCheckedStall.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Lemma stall_origin s i (flag : word 1 (r21_ncontractWasStalled (step s i))=1) :
  (word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7) /\ word 1 (nreset i)=0 /\
  word 1 (nio_5Fkill i)=0 /\ word 1 (nio_5Fresp_5Fready i)=0.
Proof.
  pose proof (bounds 3 (r0_nstate s) ltac:(lia)) as range; change (2^3) with 8 in range.
  assert (states : word 3 (r0_nstate s)=0 \/ word 3 (r0_nstate s)=1 \/ word 3 (r0_nstate s)=2 \/
    word 3 (r0_nstate s)=3 \/ word 3 (r0_nstate s)=4 \/ word 3 (r0_nstate s)=5 \/
    word 3 (r0_nstate s)=6 \/ word 3 (r0_nstate s)=7) by lia.
  cbn [step r21_ncontractWasStalled] in flag.
  unfold v190,v189,v188,v38,v37,v36,v35,v4,v31,v8 in flag.
  destruct (bit_cases (nreset i)) as [hr|hr];
    destruct (bit_cases (nio_5Fkill i)) as [hk|hk];
    destruct (bit_cases (nio_5Fresp_5Fready i)) as [ready|ready];
    destruct (bit_cases (r9_ncontractPending s)) as [pending|pending];
    destruct states as [st|[st|[st|[st|[st|[st|[st|st]]]]]]];
    rewrite hr,hk,ready,pending,st in flag; try discriminate;
    repeat split; auto.
Qed.
Lemma previous_data s i : word 64 (r19_ncontractPreviousData (step s i))=nio_5Fresp_5Fbits_5Fdata (observe s i).
Proof. cbn [step r19_ncontractPreviousData observe nio_5Fresp_5Fbits_5Fdata]; unfold v187; apply normalize; lia. Qed.
Lemma previous_tag s i : word 5 (r20_ncontractPreviousTag (step s i))=nio_5Fresp_5Fbits_5Ftag (observe s i).
Proof. cbn [step r20_ncontractPreviousTag observe nio_5Fresp_5Fbits_5Ftag]; apply normalize; lia. Qed.
Local Opaque step run observe MulDiv.nMulDiv.step MulDiv.nMulDiv.observe.
Theorem stable_after_recorded_stall s i later (flag : word 1 (r21_ncontractWasStalled (step s i))=1) :
  nio_5Fresp_5Fvalid (observe (step s i) later)=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=word 64 (r19_ncontractPreviousData (step s i)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (step s i) later)=word 5 (r20_ncontractPreviousTag (step s i)).
Proof.
  destruct (stall_origin s i flag) as [done [hr [hk ready]]].
  pose proof (MulDivStall.MulDivStall.stall_stable (P.state s) (P.inputs i) (P.inputs later) done hr hk ready) as stable.
  rewrite <- (P.step_projects s i), <- (P.observe_projects (step s i) later), <- (P.observe_projects s i) in stable.
  change (nio_5Fresp_5Fvalid (observe (step s i) later)=1 /\
    nio_5Fresp_5Fbits_5Fdata (observe (step s i) later)=nio_5Fresp_5Fbits_5Fdata (observe s i) /\
    nio_5Fresp_5Fbits_5Ftag (observe (step s i) later)=nio_5Fresp_5Fbits_5Ftag (observe s i)) in stable.
  rewrite previous_data,previous_tag; exact stable.
Qed.
Lemma last_checks s i
  (correct : word 1 (r21_ncontractWasStalled s)=1 ->
    nio_5Fresp_5Fvalid (observe s i)=1 /\
    nio_5Fresp_5Fbits_5Fdata (observe s i)=word 64 (r19_ncontractPreviousData s) /\
    nio_5Fresp_5Fbits_5Ftag (observe s i)=word 5 (r20_ncontractPreviousTag s)) :
  forallb (fun b => b) (skipn 8 (assertionChecks s i))=true.
Proof.
  cbn [skipn assertionChecks].
  destruct (v285 s i=?1) eqn:enabled; [|reflexivity].
  apply Z.eqb_eq in enabled.
  assert (flag : word 1 (r21_ncontractWasStalled s)=1).
  { destruct (bit_cases (r21_ncontractWasStalled s)) as [zero|one]; [|exact one].
    unfold v285 in enabled; rewrite zero,!Z.land_0_l in enabled; discriminate. }
  destruct (correct flag) as [valid [data tag]].
  change (v38 s i=1) in valid; change (v187 s i=word 64 (r19_ncontractPreviousData s)) in data.
  change (word 5 (r2_nreq_5Ftag s)=word 5 (r20_ncontractPreviousTag s)) in tag.
  unfold v286,v287; rewrite valid,data,tag,!Z.eqb_refl; reflexivity.
Qed.
Theorem stall_assertions s i later : forallb (fun b => b) (skipn 8 (assertionChecks (step s i) later))=true.
Proof. apply last_checks; apply stable_after_recorded_stall. Qed.
Theorem stall_assertions_trace initial first pins n :
  forallb (fun b => b) (skipn 8 (assertionChecks (run (step initial first) pins n) (pins n)))=true.
Proof.
  destruct n as [|n].
  - change (forallb (fun b => b) (skipn 8 (assertionChecks (step initial first) (pins O)))=true); apply stall_assertions.
  - change (run (step initial first) pins (S n)) with (step (run (step initial first) pins n) (pins n)); apply stall_assertions.
Qed.
End MulDivCheckedStall.
Print Assumptions MulDivCheckedStall.stall_assertions_trace.
