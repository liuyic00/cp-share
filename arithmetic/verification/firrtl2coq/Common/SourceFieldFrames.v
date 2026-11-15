From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts BundleFacts HierarchyFacts PortFieldFacts InstanceFoldFacts.

Lemma bundle_replace_identity field fn before after
 (identity : forall value, fn value = Some value)
 (replaced : bundle_replace field fn before = Some after) : after = before.
Proof.
 revert after replaced. induction before as [|id flip value rest IH]; intros after replaced; [discriminate|].
 cbn [bundle_replace] in replaced. destruct (field == id).
 - rewrite identity in replaced. inversion replaced; reflexivity.
 - destruct (bundle_replace field fn rest) as [next|] eqn:Next; inversion replaced; subst after.
   f_equal. eapply IH. reflexivity.
Qed.
Lemma repl_field_source_preserves instance field watched old value env result
 (passive : is_passive_value value = true)
 (replaced : repl_val_part (Esubfield (Eid instance) field) (replace_writeable Source) old value env = Some result) :
 value_field watched result = value_field watched old.
Proof.
 change (match convert_to_bundle_value old with
 | Some bundle => option_map Bval (bundle_replace field (fun prior => replace_writeable Source prior value) bundle)
 | None => None end = Some result) in replaced.
 unfold value_field. destruct (convert_to_bundle_value old) as [bundle|] eqn:B; try discriminate.
 destruct (bundle_replace field (fun prior => replace_writeable Source prior value) bundle) as [next|] eqn:Next; inversion replaced; subst result.
 cbn [convert_to_bundle_value].
 have Same : next = bundle by (eapply bundle_replace_identity; [intros; apply replace_source_passive; exact passive|exact Next]).
 rewrite Same. reflexivity.
Qed.
Definition parent_port_frames field (port : @hfport VarOrder.T) :=
 match port with Finput _ (Gtyp _) => true | Foutput id _ => id != field | _ => false end.

Lemma sync_instance_parent_input_preserved instance ports parent_old child_old watched
 (frames : all (parent_port_frames watched) ports = true) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance ports parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 interface_field instance watched parent_after = interface_field instance watched parent_before.
Proof.
 induction ports as [|port ports IH]; intros parent_before child_before parent_after child_after synced.
 - inversion synced; reflexivity.
 - move/andP: frames => [head_frame tail_frame].
   destruct port as [id ty|id ty].
   + destruct ty; cbn [parent_port_frames] in head_frame; try discriminate.
     cbn [sync_instance_ports] in synced.
     destruct (eval_href (Esubfield (Eid instance) id) parent_old parent_old) as [pv|] eqn:P; try discriminate.
     destruct (VM.find id child_old) as [cv|] eqn:C; try discriminate.
     destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
     destruct (VM.find id child_before) as [child|] eqn:Child; try discriminate.
     destruct ((type_of_val pv == Gtyp f) && (type_of_val cv == Gtyp f)) eqn:Types; try discriminate.
     move/andP: Types => [_ /eqP CT].
     destruct (repl_val_part (Esubfield (Eid instance) id) (replace_writeable Source) pb cv parent_old) as [next|] eqn:R; try discriminate.
     destruct (replace_writeable Sink child pv) as [next_child|] eqn:RC; try discriminate.
     rewrite (IH tail_frame _ _ _ _ synced).
     unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity]. rewrite B.
     eapply repl_field_source_preserves; [eapply ground_value_passive; exact CT|exact R].
   + cbn [parent_port_frames] in head_frame.
     cbn [sync_instance_ports] in synced;
     repeat match type of synced with
     | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
     | context [if ?x then _ else _] => destruct x eqn:?
     end; try discriminate.
     rewrite (IH tail_frame _ _ _ _ synced).
     unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
     match goal with H : VM.find instance parent_before = Some _ |- _ => rewrite H end.
     eapply repl_field_other; [exact (different_id _ _ head_frame)|eassumption].
Qed.
Print Assumptions sync_instance_parent_input_preserved.

Lemma two_instance_updates_preserve_interface query instance field states path parent child_before parent_before child_after parent_after
 (child_found : SVM.find path states = Some child_before)
 (parent_found : SVM.find parent states = Some parent_before)
 (child_preserved : query = path -> interface_field instance field child_after = interface_field instance field child_before)
 (parent_preserved : query = parent -> interface_field instance field parent_after = interface_field instance field parent_before) :
 circuit_interface query instance field (SVM.add path child_after (SVM.add parent parent_after states)) =
 circuit_interface query instance field states.
Proof.
 unfold circuit_interface, circuit_lookup.
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

Lemma sync_step_preserves_interface modules snapshot query instance field path module_id states final
 (child_frames : forall child parent id ports body,
   path = child :: parent -> find_module modules module_id = Some (FInmod id ports body) ->
   query = path -> all (child_port_frames instance) ports = true)
 (parent_frames : forall child parent id ports body,
   path = child :: parent -> find_module modules module_id = Some (FInmod id ports body) ->
   query = parent -> child = instance -> all (parent_port_frames field) ports = true)
 (ran : sync_step modules snapshot path module_id (Some states) = Some final) :
 circuit_interface query instance field final = circuit_interface query instance field states.
Proof.
 destruct path as [|child parent]; [inversion ran; reflexivity|].
 unfold sync_step in ran.
 destruct (find_module modules module_id) as [m|] eqn:Module; try discriminate.
 destruct m as [id ports body|]; try discriminate.
 destruct (SVM.find parent snapshot) as [po|] eqn:Po; try discriminate.
 destruct (SVM.find (child :: parent) snapshot) as [co|] eqn:Co; try discriminate.
 destruct (SVM.find parent states) as [pn|] eqn:Pn; try discriminate.
 destruct (SVM.find (child :: parent) states) as [cn|] eqn:Cn; try discriminate.
 destruct (sync_instance_ports child ports po co pn cn) as [[p c]|] eqn:Sync; try discriminate.
 inversion ran; subst final.
 eapply two_instance_updates_preserve_interface; [exact Cn|exact Pn| |].
 - intros Q. unfold interface_field.
   have Frame : all (child_port_frames instance) ports = true.
   { eapply child_frames; eassumption || reflexivity. }
   rewrite (sync_instance_child_output child ports po co instance Frame pn cn p c Sync). reflexivity.
 - intros Q. destruct (child == instance) eqn:Same.
   + move/eqP: Same => Same. subst child.
     eapply sync_instance_parent_input_preserved; [|exact Sync].
     eapply parent_frames; eassumption || reflexivity.
   + unfold interface_field.
     have Different : child != instance by rewrite Same.
     rewrite (sync_instance_parent_private child ports po co instance Different _ _ _ _ Sync). reflexivity.
Qed.

Lemma sync_circuit_preserves_interface modules instances snapshot final query instance field
 (child_frames : forall path module_id child parent id ports body,
   SVM.find path instances = Some module_id -> path = child :: parent ->
   find_module modules module_id = Some (FInmod id ports body) ->
   query = path -> all (child_port_frames instance) ports = true)
 (parent_frames : forall path module_id child parent id ports body,
   SVM.find path instances = Some module_id -> path = child :: parent ->
   find_module modules module_id = Some (FInmod id ports body) ->
   query = parent -> child = instance -> all (parent_port_frames field) ports = true)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_interface query instance field final = circuit_interface query instance field snapshot.
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 have Invariant : forall result,
   SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some result ->
   circuit_interface query instance field result = circuit_interface query instance field snapshot.
 { apply (SVM.Lemmas.P.fold_rec
     (P := fun _ acc => forall result, acc = Some result ->
       circuit_interface query instance field result = circuit_interface query instance field snapshot)).
   - intros done empty result same. inversion same; reflexivity.
   - intros path module_id acc done next member fresh added IH result Step.
     destruct acc as [states|]; [|discriminate].
     have Original := IH states (Logic.eq_refl _).
     rewrite -Original.
     eapply sync_step_preserves_interface; [| |exact Step].
     + intros child parent id ports body Path Module Query.
       eapply child_frames; [apply SVM.Lemmas.find_mapsto_iff; exact member|exact Path|exact Module|exact Query].
     + intros child parent id ports body Path Module Query Same.
       eapply parent_frames; [apply SVM.Lemmas.find_mapsto_iff; exact member|exact Path|exact Module|exact Query|exact Same]. }
 exact (Invariant final ran).
Qed.
Print Assumptions sync_circuit_preserves_interface.
