From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Section Fold.
Variables (Job Value : Type).
Variable update : SVM.key -> Job -> Value -> option Value.
Definition instance_update path job (acc : option (SVM.t Value)) :=
 match acc with
 | None => None
 | Some states => match SVM.find path states with
   | None => None
   | Some before => match update path job before with
     | None => None | Some after => Some (SVM.add path after states) end
   end
 end.
Variable initial : SVM.t Value.
Definition fold_progress (done : SVM.t Job) (acc : option (SVM.t Value)) :=
 forall states, acc = Some states -> forall path,
 match SVM.find path done with
 | None => SVM.find path states = SVM.find path initial
 | Some job => exists before after,
   SVM.find path initial = Some before /\ update path job before = Some after /\
   SVM.find path states = Some after
 end.

Lemma instance_fold_progress jobs :
 fold_progress jobs (SVM.fold instance_update jobs (Some initial)).
Proof.
 apply (SVM.Lemmas.P.fold_rec (P := fold_progress)).
 - intros done empty states same path. inversion same; subst states.
   destruct (SVM.find path done) as [job|] eqn:Found; [|reflexivity].
   exfalso. apply (empty path job). apply SVM.Lemmas.find_mapsto_iff. exact Found.
 - intros path job acc done next member fresh added IH states ran query.
   destruct acc as [current|]; [|discriminate].
   unfold instance_update in ran.
   destruct (SVM.find path current) as [before|] eqn:Before; try discriminate.
   destruct (update path job before) as [after|] eqn:After; try discriminate.
   inversion ran; subst states.
   have Unseen : SVM.find path done = None.
   { destruct (SVM.find path done) as [x|] eqn:E; [|reflexivity].
     exfalso. apply fresh. exists x. apply SVM.Lemmas.find_mapsto_iff. exact E. }
   have Kept := IH current (Logic.eq_refl _) path. rewrite Unseen in Kept.
   unfold SVM.Lemmas.P.Add in added. rewrite (added query).
   destruct (query == path) eqn:Same.
   + rewrite SVM.Lemmas.find_add_eq; [|exact Same].
     move/eqP: Same => Same. subst query.
     exists before, after. split; [rewrite -Kept; exact Before|].
     split; [exact After|apply SVM.Lemmas.find_add_eq; reflexivity].
   + have Different : ~ query == path by rewrite Same.
     rewrite SVM.Lemmas.find_add_neq; [|exact Different].
     have Result := IH current (Logic.eq_refl _) query.
     destruct (SVM.find query done) as [prior|] eqn:Q.
     * destruct Result as [b [a [B [A R]]]].
       exists b,a. split; [exact B|]. split; [exact A|].
       rewrite SVM.Lemmas.find_add_neq; assumption.
     * rewrite SVM.Lemmas.find_add_neq; assumption.
Qed.

Lemma instance_fold_lookup jobs final path job
 (ran : SVM.fold instance_update jobs (Some initial) = Some final)
 (found : SVM.find path jobs = Some job) :
 exists before after, SVM.find path initial = Some before /\
 update path job before = Some after /\ SVM.find path final = Some after.
Proof. have H := instance_fold_progress jobs final ran path. rewrite found in H. exact H. Qed.
End Fold.
Print Assumptions instance_fold_lookup.

Lemma instance_fold_ext (Job Acc : Type) (jobs : SVM.t Job) (initial : Acc)
 (f g : SVM.key -> Job -> Acc -> Acc)
 (same : forall path job acc, f path job acc = g path job acc) :
 SVM.fold f jobs initial = SVM.fold g jobs initial.
Proof.
 rewrite !SVM.fold_1. generalize (SVM.elements jobs). intros entries.
 revert initial. induction entries as [|[path job] entries IH]; intros initial; [reflexivity|].
 cbn [List.fold_left fst snd]. rewrite same. apply IH.
Qed.

Definition local_instance_update invalid modules snapshot set_regs path module_id before :=
 match SVM.find path snapshot, find_module modules module_id, memory_map_for_module modules module_id with
 | Some old, Some (FInmod _ _ stmts), Some mm =>
     value_iter_with_memory_policy (invalid path) mm old set_regs before stmts
 | _, _, _ => None
 end.
Definition original_instance_step invalid modules snapshot set_regs path module_id acc :=
 match acc, SVM.find path snapshot,
       (match acc with Some states => SVM.find path states | None => None end),
       find_module modules module_id, memory_map_for_module modules module_id with
 | Some states, Some old, Some before, Some (FInmod _ _ stmts), Some mm =>
    match value_iter_with_memory_policy (invalid path) mm old set_regs before stmts with
    | Some result => Some (SVM.add path result states) | None => None end
 | _, _, _, _, _ => None
 end.
Lemma original_instance_step_update invalid modules snapshot set_regs path module_id acc :
 original_instance_step invalid modules snapshot set_regs path module_id acc =
 instance_update _ _ (local_instance_update invalid modules snapshot set_regs) path module_id acc.
Proof.
 destruct acc as [states|]; [|reflexivity].
 unfold original_instance_step, instance_update, local_instance_update.
 destruct (SVM.find path snapshot); destruct (SVM.find path states);
 destruct (find_module modules module_id) as [m|]; try destruct m;
 destruct (memory_map_for_module modules module_id); reflexivity.
Qed.

Lemma original_instance_fold_lookup invalid modules snapshot set_regs instances evaluated path module_id
 (ran : SVM.fold (original_instance_step invalid modules snapshot set_regs) instances (Some snapshot) = Some evaluated)
 (found : SVM.find path instances = Some module_id) :
 exists before after, SVM.find path snapshot = Some before /\
 local_instance_update invalid modules snapshot set_regs path module_id before = Some after /\
 SVM.find path evaluated = Some after.
Proof.
 rewrite (instance_fold_ext _ _ _ _ _ _ (original_instance_step_update invalid modules snapshot set_regs)) in ran.
 eapply instance_fold_lookup; eassumption.
Qed.
Print Assumptions original_instance_fold_lookup.

Lemma circuit_iteration_local_steps invalid modules top snapshot set_regs final
 (ran : circuit_value_iter_with_memory_policy invalid modules top snapshot set_regs = Some final) :
 exists instances evaluated,
 find_circuit_instances modules top = Some instances /\
 sync_circuit_ports modules instances evaluated = Some final /\
 forall path module_id, SVM.find path instances = Some module_id ->
 exists before after,
 SVM.find path snapshot = Some before /\
 local_instance_update invalid modules snapshot set_regs path module_id before = Some after /\
 SVM.find path evaluated = Some after.
Proof.
 unfold circuit_value_iter_with_memory_policy in ran.
 destruct (find_circuit_instances modules top) as [instances|] eqn:Instances; try discriminate.
 change (match SVM.fold (original_instance_step invalid modules snapshot set_regs) instances (Some snapshot) with
 | Some evaluated => sync_circuit_ports modules instances evaluated | None => None end = Some final) in ran.
 destruct (SVM.fold (original_instance_step invalid modules snapshot set_regs) instances (Some snapshot)) as [evaluated|] eqn:Evaluated; try discriminate.
 exists instances,evaluated. split; [reflexivity|]. split; [exact ran|].
 intros path module_id found. eapply original_instance_fold_lookup; eassumption.
Qed.
Print Assumptions circuit_iteration_local_steps.

Lemma fold_establishes_at_key (Job State : Type) (jobs : SVM.t Job)
 (step : SVM.key -> Job -> option State -> option State) initial focus (P : State -> Prop)
 (none_stays : forall path job, step path job None = None)
 (establishes : forall job before after,
   SVM.find focus jobs = Some job -> step focus job (Some before) = Some after -> P after)
 (preserves : forall path job before after,
   SVM.find path jobs = Some job -> path <> focus -> P before ->
   step path job (Some before) = Some after -> P after) :
 forall final job, SVM.fold step jobs (Some initial) = Some final ->
 SVM.find focus jobs = Some job -> P final.
Proof.
 have Invariant : forall final, SVM.fold step jobs (Some initial) = Some final ->
   forall job, SVM.find focus jobs = Some job -> P final.
 { apply (SVM.Lemmas.P.fold_rec
     (P := fun done acc => forall final, acc = Some final ->
       forall job, SVM.find focus done = Some job -> P final)).
   - intros done empty final ran job found.
     exfalso. apply (empty focus job). apply SVM.Lemmas.find_mapsto_iff. exact found.
   - intros path job acc done next member fresh added IH final ran found_job found.
     destruct acc as [before|]; [|rewrite none_stays in ran; discriminate].
     have Member : SVM.find path jobs = Some job by (apply SVM.Lemmas.find_mapsto_iff; exact member).
     destruct (focus == path) eqn:Same.
     + move/eqP: Same => Same. subst path. eapply establishes; eassumption.
     + have Different : ~ focus == path by rewrite Same.
       unfold SVM.Lemmas.P.Add in added. rewrite (added focus) SVM.Lemmas.find_add_neq in found; [|exact Different].
       eapply preserves; [exact Member| |eapply IH; [reflexivity|exact found]|exact ran].
       intros equal. subst path. rewrite eqxx in Same. discriminate. }
 intros final job ran found. eapply Invariant; eassumption.
Qed.
Print Assumptions fold_establishes_at_key.
