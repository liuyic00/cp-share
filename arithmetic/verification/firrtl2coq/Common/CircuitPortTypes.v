From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames HierarchyFacts InstanceFoldFacts PortFieldFacts FieldTypePreservation.

Lemma sync_instance_input_type instance prefix suffix parent_old child_old input ground
 (frames : all (child_port_frames input) suffix = true) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance (prefix ++ Finput input (Gtyp ground) :: suffix)
   parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 exists value, VM.find input child_after = Some value /\ type_of_val value = Gtyp ground.
Proof.
 induction prefix as [|port prefix IH]; intros parent_before child_before parent_after child_after synced.
 - cbn [cat sync_instance_ports] in synced.
   destruct (eval_href (Esubfield (Eid instance) input) parent_old parent_old) as [pv|] eqn:P; try discriminate.
   destruct (VM.find input child_old) as [cv|] eqn:C; try discriminate.
   destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
   destruct (VM.find input child_before) as [child|] eqn:Child; try discriminate.
   destruct ((type_of_val pv == Gtyp ground) && (type_of_val cv == Gtyp ground)) eqn:Types; try discriminate.
   move/andP: Types => [/eqP PT CT].
   rewrite (replace_sink_passive child pv (ground_value_passive _ _ PT)) in synced.
   destruct (repl_val_part (Esubfield (Eid instance) input) (replace_writeable Source) pb cv parent_old) eqn:R; try discriminate.
   exists pv. split; [|exact PT].
   rewrite (sync_instance_child_output _ _ _ _ _ frames _ _ _ _ synced).
   apply VM.Lemmas.find_add_eq. reflexivity.
 - destruct port; cbn [cat sync_instance_ports] in synced;
   repeat match type of synced with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   | context [if ?x then _ else _] => destruct x eqn:?
   end; try discriminate; eapply IH; exact synced.
Qed.

Lemma sync_instance_output_type instance prefix suffix parent_old child_old output ground
 (frames : all (fun port => port_identifier port != output) suffix = true) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance (prefix ++ Foutput output (Gtyp ground) :: suffix)
   parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 exists value, interface_field instance output parent_after = Some value /\ type_of_val value = Gtyp ground.
Proof.
 induction prefix as [|port prefix IH]; intros parent_before child_before parent_after child_after synced.
 - cbn [cat sync_instance_ports] in synced.
   destruct (eval_href (Esubfield (Eid instance) output) parent_old parent_old) as [pv|] eqn:P; try discriminate.
   destruct (VM.find output child_old) as [cv|] eqn:C; try discriminate.
   destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
   destruct (VM.find output child_before) as [child|] eqn:Child; try discriminate.
   destruct ((type_of_val pv == Gtyp ground) && (type_of_val cv == Gtyp ground)) eqn:Types; try discriminate.
   move/andP: Types => [_ /eqP CT].
   destruct (repl_val_part (Esubfield (Eid instance) output) (replace_writeable Sink) pb cv parent_old) as [next|] eqn:R; try discriminate.
   destruct (replace_writeable Source child pv) as [next_child|] eqn:RC; try discriminate.
   exists cv. split; [|exact CT].
   rewrite (sync_instance_parent_field_preserved _ _ _ _ _ frames _ _ _ _ synced).
   unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
   eapply repl_field_sink_passive; [eapply ground_value_passive; exact CT|exact R].
 - destruct port; cbn [cat sync_instance_ports] in synced;
   repeat match type of synced with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   | context [if ?x then _ else _] => destruct x eqn:?
   end; try discriminate; eapply IH; exact synced.
Qed.

Definition circuit_value_ground path id ground states :=
 exists value, circuit_lookup path id states = Some value /\ type_of_val value = Gtyp ground.
Definition circuit_interface_ground path instance field ground states :=
 exists value, circuit_interface path instance field states = Some value /\ type_of_val value = Gtyp ground.

Lemma sync_circuit_child_input_type modules instances snapshot final instance parent module_id prefix suffix body input ground
 (instance_found : SVM.find (instance :: parent) instances = Some module_id)
 (module_found : find_module modules module_id = Some
   (FInmod module_id (prefix ++ Finput input (Gtyp ground) :: suffix) body))
 (suffix_frames : all (child_port_frames input) suffix = true)
 (parent_frames : forall p mi child grandparent,
   SVM.find p instances = Some mi -> p = child :: grandparent ->
   instance :: parent = grandparent -> child != input)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_value_ground (instance :: parent) input ground final.
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 eapply (fold_establishes_at_key _ _ instances (sync_step modules snapshot) snapshot
   (instance :: parent) (circuit_value_ground (instance :: parent) input ground))
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
   unfold circuit_value_ground, circuit_lookup. rewrite SVM.Lemmas.find_add_eq; [|reflexivity].
   eapply sync_instance_input_type; [exact suffix_frames|exact Sync].
 - intros p mi states result found different Known Step.
   unfold circuit_value_ground in *. destruct Known as [value [Known Typed]].
   exists value. split; [|exact Typed]. rewrite -Known.
   eapply sync_step_preserves_lookup; [| |exact Step].
   + intros child grandparent id ports stmts Path Module Query.
     exfalso. apply different. symmetry. exact Query.
   + intros child grandparent Path Query. eapply parent_frames; eassumption.
Qed.
Print Assumptions sync_circuit_child_input_type.

Lemma sync_circuit_parent_output_type modules instances snapshot final instance parent module_id prefix suffix body output ground
 (instance_found : SVM.find (instance :: parent) instances = Some module_id)
 (module_found : find_module modules module_id = Some
   (FInmod module_id (prefix ++ Foutput output (Gtyp ground) :: suffix) body))
 (suffix_frames : all (fun port => port_identifier port != output) suffix = true)
 (child_frames : forall p mi child grandparent id ports stmts,
   SVM.find p instances = Some mi -> p = child :: grandparent ->
   find_module modules mi = Some (FInmod id ports stmts) ->
   parent = p -> all (child_port_frames instance) ports = true)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_interface_ground parent instance output ground final.
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 eapply (fold_establishes_at_key _ _ instances (sync_step modules snapshot) snapshot
   (instance :: parent) (circuit_interface_ground parent instance output ground))
   with (job := module_id); [| | |exact ran|exact instance_found].
 - intros p mi. reflexivity.
 - intros mi states result found Step.
   rewrite instance_found in found. inversion found; subst mi.
   unfold sync_step in Step. rewrite module_found in Step.
   destruct (SVM.find parent snapshot) as [po|] eqn:Po; try discriminate.
   destruct (SVM.find (instance :: parent) snapshot) as [co|] eqn:Co; try discriminate.
   destruct (SVM.find parent states) as [pn|] eqn:Pn; try discriminate.
   destruct (SVM.find (instance :: parent) states) as [cn|] eqn:Cn; try discriminate.
   destruct (sync_instance_ports instance (prefix ++ Foutput output (Gtyp ground) :: suffix) po co pn cn)
     as [[p c]|] eqn:Sync; try discriminate.
   inversion Step; subst result.
   unfold circuit_interface_ground, circuit_interface, circuit_lookup.
   rewrite SVM.Lemmas.find_add_neq; [|apply parent_path_distinct].
   rewrite SVM.Lemmas.find_add_eq; [|reflexivity].
   change (exists value, interface_field instance output p = Some value /\ type_of_val value = Gtyp ground).
   eapply sync_instance_output_type; [exact suffix_frames|exact Sync].
 - intros p mi states result found different Known Step.
   unfold circuit_interface_ground in *. destruct Known as [value [Known Typed]].
   exists value. split; [|exact Typed].
   unfold circuit_interface in *. rewrite -Known.
   have Preserved : circuit_lookup parent instance result = circuit_lookup parent instance states.
   { eapply sync_step_preserves_lookup; [| |exact Step].
     - intros child grandparent id ports stmts Path Module Query.
       eapply child_frames; eassumption.
     - intros child grandparent Path Query. apply/negP. move/eqP=> Same.
       apply different. subst p grandparent child. reflexivity. }
   rewrite Preserved. reflexivity.
Qed.
Print Assumptions sync_circuit_parent_output_type.
