From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts.

Definition port_identifier (port : @hfport VarOrder.T) : VarOrder.T :=
 match port with Finput id _ | Foutput id _ => id end.

Lemma sync_instance_child_private instance ports parent_old child_old watched :
 all (fun port => port_identifier port != watched) ports ->
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance ports parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 VM.find watched child_after = VM.find watched child_before.
Proof.
 induction ports as [|port ports IH]; intros private parent_before child_before parent_after child_after synced.
 - inversion synced; reflexivity.
 - move/andP: private => [different tail_private].
   destruct port as [id t|id t]; cbn [port_identifier] in different;
     cbn [sync_instance_ports] in synced;
     repeat match type of synced with
     | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
     | context [if ?x then _ else _] => destruct x eqn:?
     end; try discriminate;
     rewrite (IH tail_private _ _ _ _ synced);
     apply find_add_other; exact different.
Qed.

Lemma sync_instance_parent_private instance ports parent_old child_old watched
 (different : instance != watched) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance ports parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 VM.find watched parent_after = VM.find watched parent_before.
Proof.
 induction ports as [|port ports IH]; intros parent_before child_before parent_after child_after synced.
 - inversion synced; reflexivity.
 - destruct port; cbn [sync_instance_ports] in synced;
     repeat match type of synced with
     | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
     | context [if ?x then _ else _] => destruct x eqn:?
     end; try discriminate;
     rewrite (IH _ _ _ _ synced);
     apply find_add_other; exact different.
Qed.
Print Assumptions sync_instance_child_private.

Lemma ground_value_passive value ground
 (typed : type_of_val value = Gtyp ground) : is_passive_value value = true.
Proof. destruct value; simpl in typed; try discriminate; inversion typed; reflexivity. Qed.

Definition child_port_frames watched (port : @hfport VarOrder.T) :=
 match port with
 | Finput id _ => id != watched
 | Foutput _ (Gtyp _) => true
 | _ => false
 end.
Lemma sync_instance_child_output instance ports parent_old child_old watched :
 all (child_port_frames watched) ports ->
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance ports parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 VM.find watched child_after = VM.find watched child_before.
Proof.
 induction ports as [|port ports IH]; intros frames parent_before child_before parent_after child_after synced.
 - inversion synced; reflexivity.
 - move/andP: frames => [head_frame tail_frame].
   destruct port as [id t|id t].
   + cbn [child_port_frames] in head_frame.
     cbn [sync_instance_ports] in synced.
     repeat match type of synced with
     | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
     | context [if ?x then _ else _] => destruct x eqn:?
     end; try discriminate.
     rewrite (IH tail_frame _ _ _ _ synced). apply find_add_other. exact head_frame.
   + destruct t; cbn [child_port_frames] in head_frame; try discriminate.
     cbn [sync_instance_ports] in synced.
     destruct (eval_href (Esubfield (Eid instance) id) parent_old parent_old) as [pv|] eqn:P; try discriminate.
     destruct (VM.find id child_old) as [cv|] eqn:C; try discriminate.
     destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
     destruct (VM.find id child_before) as [child|] eqn:Child; try discriminate.
     destruct ((type_of_val pv == Gtyp f) && (type_of_val cv == Gtyp f)) eqn:Types; try discriminate.
     move/andP: Types => [/eqP PT CT].
     rewrite (replace_source_passive child pv (ground_value_passive _ _ PT)) in synced.
     destruct (repl_val_part (Esubfield (Eid instance) id) (replace_writeable Sink) pb cv parent_old) eqn:R; try discriminate.
     rewrite (IH tail_frame _ _ _ _ synced).
     destruct (N.eq_dec id watched) as [same|different].
     * subst id. rewrite VM.Lemmas.find_add_eq; [symmetry; exact Child|reflexivity].
     * apply VM.Lemmas.find_add_neq. move/eqP=> same. apply different. symmetry. exact same.
Qed.
Print Assumptions sync_instance_child_output.

Definition circuit_lookup path id (states : SVM.t (VM.t hvalue)) :=
 match SVM.find path states with Some env => VM.find id env | None => None end.

Lemma two_instance_updates_preserve_lookup query watched states path parent child_before parent_before child_after parent_after
 (child_found : SVM.find path states = Some child_before)
 (parent_found : SVM.find parent states = Some parent_before)
 (child_preserved : query = path -> VM.find watched child_after = VM.find watched child_before)
 (parent_preserved : query = parent -> VM.find watched parent_after = VM.find watched parent_before) :
 circuit_lookup query watched (SVM.add path child_after (SVM.add parent parent_after states)) =
 circuit_lookup query watched states.
Proof.
 unfold circuit_lookup.
 destruct (query == path) eqn:Child.
 - rewrite SVM.Lemmas.find_add_eq; [|exact Child].
   move/eqP: Child => Child. subst query. rewrite child_found.
   apply child_preserved. reflexivity.
 - have Cneq : ~ query == path by rewrite Child.
   rewrite SVM.Lemmas.find_add_neq; [|exact Cneq].
   destruct (query == parent) eqn:Parent.
   + rewrite SVM.Lemmas.find_add_eq; [|exact Parent].
     move/eqP: Parent => Parent. subst query. rewrite parent_found.
     apply parent_preserved. reflexivity.
   + rewrite SVM.Lemmas.find_add_neq; [reflexivity|rewrite Parent; discriminate].
Qed.

Definition sync_step modules snapshot path module_id acc :=
 match acc with
 | None => None
 | Some states => match path with
   | [::] => Some states
   | instance :: parent =>
     match find_module modules module_id,
       SVM.find parent snapshot, SVM.find path snapshot,
       SVM.find parent states, SVM.find path states with
     | Some (FInmod _ ports _), Some po, Some co, Some pn, Some cn =>
       match sync_instance_ports instance ports po co pn cn with
       | Some (p,c) => Some (SVM.add path c (SVM.add parent p states))
       | None => None end
     | _, _, _, _, _ => None end
   end
 end.

Lemma sync_step_preserves_lookup modules snapshot query watched path module_id states final
 (child_frames : forall instance parent id ports body,
   path = instance :: parent -> find_module modules module_id = Some (FInmod id ports body) ->
   query = path -> all (child_port_frames watched) ports = true)
 (parent_frames : forall instance parent, path = instance :: parent -> query = parent -> instance != watched)
 (ran : sync_step modules snapshot path module_id (Some states) = Some final) :
 circuit_lookup query watched final = circuit_lookup query watched states.
Proof.
 destruct path as [|instance parent]; [inversion ran; reflexivity|].
 unfold sync_step in ran.
 destruct (find_module modules module_id) as [m|] eqn:Module; try discriminate.
 destruct m as [id ports body|]; try discriminate.
 destruct (SVM.find parent snapshot) as [po|] eqn:Po; try discriminate.
 destruct (SVM.find (instance :: parent) snapshot) as [co|] eqn:Co; try discriminate.
 destruct (SVM.find parent states) as [pn|] eqn:Pn; try discriminate.
 destruct (SVM.find (instance :: parent) states) as [cn|] eqn:Cn; try discriminate.
 destruct (sync_instance_ports instance ports po co pn cn) as [[p c]|] eqn:Sync; try discriminate.
 inversion ran; subst final.
 eapply two_instance_updates_preserve_lookup; [exact Cn|exact Pn| |].
 - intros Q. eapply sync_instance_child_output; [eapply child_frames; eassumption || reflexivity|exact Sync].
 - intros Q. eapply sync_instance_parent_private; [eapply parent_frames; eassumption || reflexivity|exact Sync].
Qed.

Lemma sync_circuit_preserves_lookup modules instances snapshot final query watched
 (child_frames : forall path module_id instance parent id ports body,
   SVM.find path instances = Some module_id -> path = instance :: parent ->
   find_module modules module_id = Some (FInmod id ports body) ->
   query = path -> all (child_port_frames watched) ports = true)
 (parent_frames : forall path module_id instance parent,
   SVM.find path instances = Some module_id -> path = instance :: parent ->
   query = parent -> instance != watched)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_lookup query watched final = circuit_lookup query watched snapshot.
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 have Invariant : forall result,
   SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some result ->
   circuit_lookup query watched result = circuit_lookup query watched snapshot.
 { apply (SVM.Lemmas.P.fold_rec
     (P := fun _ acc => forall result, acc = Some result ->
       circuit_lookup query watched result = circuit_lookup query watched snapshot)).
   - intros done empty result same. inversion same; reflexivity.
   - intros path module_id acc done next member fresh added IH result Step.
     destruct acc as [states|]; [|discriminate].
     have Original := IH states (Logic.eq_refl _).
     rewrite -Original.
     eapply sync_step_preserves_lookup; [| |exact Step].
     + intros instance parent id ports body Path Module Query.
       eapply child_frames; [apply SVM.Lemmas.find_mapsto_iff; exact member|exact Path|exact Module|exact Query].
     + intros instance parent Path Query.
       eapply parent_frames; [apply SVM.Lemmas.find_mapsto_iff; exact member|exact Path|exact Query]. }
 exact (Invariant final ran).
Qed.
Print Assumptions sync_circuit_preserves_lookup.

Lemma sync_instance_input_value instance prefix suffix parent_old child_old input ground bits
 (frames : all (child_port_frames input) suffix = true)
 (source : eval_href (Esubfield (Eid instance) input) parent_old parent_old = Some (Gval ground bits)) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance (prefix ++ Finput input (Gtyp ground) :: suffix)
   parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 VM.find input child_after = Some (Gval ground bits).
Proof.
 induction prefix as [|port prefix IH]; intros parent_before child_before parent_after child_after synced.
 - cbn [cat sync_instance_ports] in synced. rewrite source in synced.
   destruct (VM.find input child_old) as [cv|] eqn:C; try discriminate.
   destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
   destruct (VM.find input child_before) as [child|] eqn:Child; try discriminate.
   cbn [type_of_val replace_writeable is_passive_value] in synced.
   destruct ((Gtyp ground == Gtyp ground) && (type_of_val cv == Gtyp ground)); try discriminate.
   destruct (repl_val_part (Esubfield (Eid instance) input) (replace_writeable Source) pb cv parent_old) eqn:R; try discriminate.
   rewrite (sync_instance_child_output _ _ _ _ _ frames _ _ _ _ synced).
   apply VM.Lemmas.find_add_eq. reflexivity.
 - destruct port; cbn [cat sync_instance_ports] in synced;
   repeat match type of synced with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   | context [if ?x then _ else _] => destruct x eqn:?
   end; try discriminate; eapply IH; exact synced.
Qed.
Print Assumptions sync_instance_input_value.

From ArithmeticCommon Require Import InstanceFoldFacts.
Lemma sync_circuit_child_input modules instances snapshot final instance parent module_id prefix suffix body input ground bits
 (instance_found : SVM.find (instance :: parent) instances = Some module_id)
 (module_found : find_module modules module_id = Some
   (FInmod module_id (prefix ++ Finput input (Gtyp ground) :: suffix) body))
 (suffix_frames : all (child_port_frames input) suffix = true)
 (source : forall parent_env, SVM.find parent snapshot = Some parent_env ->
   eval_href (Esubfield (Eid instance) input) parent_env parent_env = Some (Gval ground bits))
 (parent_frames : forall p mi child grandparent,
   SVM.find p instances = Some mi -> p = child :: grandparent ->
   instance :: parent = grandparent -> child != input)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_lookup (instance :: parent) input final = Some (Gval ground bits).
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 eapply (fold_establishes_at_key _ _ instances (sync_step modules snapshot) snapshot
   (instance :: parent) (fun states => circuit_lookup (instance :: parent) input states = Some (Gval ground bits)))
   with (job := module_id); [| | |exact ran|exact instance_found].
 - intros p mi. reflexivity.
 - intros mi states result found Step.
   rewrite instance_found in found. inversion found; subst mi.
   unfold sync_step in Step. rewrite module_found in Step.
   destruct (SVM.find parent snapshot) as [po|] eqn:Po; try discriminate.
   destruct (SVM.find (instance :: parent) snapshot) as [co|] eqn:Co; try discriminate.
   destruct (SVM.find parent states) as [pn|] eqn:Pn; try discriminate.
   destruct (SVM.find (instance :: parent) states) as [cn|] eqn:Cn; try discriminate.
   destruct (sync_instance_ports instance (prefix ++ Finput input (Gtyp ground) :: suffix) po co pn cn)
     as [[p c]|] eqn:Sync; try discriminate.
   inversion Step; subst result.
   unfold circuit_lookup. rewrite SVM.Lemmas.find_add_eq; [|reflexivity].
   eapply sync_instance_input_value; [exact suffix_frames|apply source; reflexivity|exact Sync].
 - intros p mi states result found different Known Step.
   rewrite -Known. eapply sync_step_preserves_lookup; [| |exact Step].
   + intros child grandparent id ports stmts Path Module Query.
     exfalso. apply different. symmetry. exact Query.
   + intros child grandparent Path Query. eapply parent_frames; eassumption.
Qed.
Print Assumptions sync_circuit_child_input.
