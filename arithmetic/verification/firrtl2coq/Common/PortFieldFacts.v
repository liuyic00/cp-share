From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts HierarchyFacts BundleFacts.

Definition interface_field instance field env :=
 match VM.find instance env with Some bundle => value_field field bundle | None => None end.
Lemma interface_field_eval instance field old env :
 eval_href (Esubfield (Eid instance) field) old env = interface_field instance field env.
Proof. reflexivity. Qed.

Lemma sync_instance_parent_field_preserved instance ports parent_old child_old watched
 (frames : all (fun port => port_identifier port != watched) ports = true) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance ports parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 interface_field instance watched parent_after = interface_field instance watched parent_before.
Proof.
 induction ports as [|port ports IH]; intros parent_before child_before parent_after child_after synced.
 - inversion synced; reflexivity.
 - move/andP: frames => [head_frame tail_frame].
   destruct port; cbn [port_identifier] in head_frame;
   cbn [sync_instance_ports] in synced;
   repeat match type of synced with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   | context [if ?x then _ else _] => destruct x eqn:?
   end; try discriminate;
   rewrite (IH tail_frame _ _ _ _ synced);
   unfold interface_field;
   rewrite VM.Lemmas.find_add_eq; try reflexivity;
   match goal with H : VM.find instance parent_before = Some _ |- _ => rewrite H end;
   eapply repl_field_other; try exact (different_id _ _ head_frame); eassumption.
Qed.

Lemma sync_instance_output_value instance prefix suffix parent_old child_old output ground bits
 (frames : all (fun port => port_identifier port != output) suffix = true)
 (source : VM.find output child_old = Some (Gval ground bits)) :
 forall parent_before child_before parent_after child_after,
 sync_instance_ports instance (prefix ++ Foutput output (Gtyp ground) :: suffix)
   parent_old child_old parent_before child_before = Some (parent_after,child_after) ->
 interface_field instance output parent_after = Some (Gval ground bits).
Proof.
 induction prefix as [|port prefix IH]; intros parent_before child_before parent_after child_after synced.
 - cbn [cat sync_instance_ports] in synced.
   destruct (eval_href (Esubfield (Eid instance) output) parent_old parent_old) as [pv|] eqn:P; try discriminate.
   rewrite source in synced.
   destruct (VM.find instance parent_before) as [pb|] eqn:B; try discriminate.
   destruct (VM.find output child_before) as [child|] eqn:Child; try discriminate.
   destruct ((type_of_val pv == Gtyp ground) && (type_of_val (Gval ground bits) == Gtyp ground)); try discriminate.
   destruct (repl_val_part (Esubfield (Eid instance) output) (replace_writeable Sink) pb (Gval ground bits) parent_old) as [next|] eqn:R; try discriminate.
   destruct (replace_writeable Source child pv) as [cv|] eqn:C; try discriminate.
   rewrite (sync_instance_parent_field_preserved _ _ _ _ _ frames _ _ _ _ synced).
   unfold interface_field. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
   eapply repl_field_sink_constant. exact R.
 - destruct port; cbn [cat sync_instance_ports] in synced;
   repeat match type of synced with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   | context [if ?x then _ else _] => destruct x eqn:?
   end; try discriminate; eapply IH; exact synced.
Qed.
Print Assumptions sync_instance_output_value.

From Coq Require Import Lia.
From ArithmeticCommon Require Import InstanceFoldFacts.
Definition circuit_interface parent instance field states :=
 match circuit_lookup parent instance states with Some bundle => value_field field bundle | None => None end.

Lemma parent_path_distinct instance (parent : SVM.key) : ~ parent == instance :: parent.
Proof.
 move/eqP=> E. have Size := f_equal (@size VarOrder.T) E.
 cbn [size] in Size. lia.
Qed.

Lemma sync_circuit_parent_output modules instances snapshot final instance parent module_id prefix suffix body output ground bits
 (instance_found : SVM.find (instance :: parent) instances = Some module_id)
 (module_found : find_module modules module_id = Some
   (FInmod module_id (prefix ++ Foutput output (Gtyp ground) :: suffix) body))
 (suffix_frames : all (fun port => port_identifier port != output) suffix = true)
 (source : forall child_env, SVM.find (instance :: parent) snapshot = Some child_env ->
   VM.find output child_env = Some (Gval ground bits))
 (child_frames : forall p mi child grandparent id ports stmts,
   SVM.find p instances = Some mi -> p = child :: grandparent ->
   find_module modules mi = Some (FInmod id ports stmts) ->
   parent = p -> all (child_port_frames instance) ports = true)
 (ran : sync_circuit_ports modules instances snapshot = Some final) :
 circuit_interface parent instance output final = Some (Gval ground bits).
Proof.
 change (SVM.fold (sync_step modules snapshot) instances (Some snapshot) = Some final) in ran.
 eapply (fold_establishes_at_key _ _ instances (sync_step modules snapshot) snapshot
   (instance :: parent) (fun states => circuit_interface parent instance output states = Some (Gval ground bits)))
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
   unfold circuit_interface, circuit_lookup.
   rewrite SVM.Lemmas.find_add_neq; [|apply parent_path_distinct].
   rewrite SVM.Lemmas.find_add_eq; [|reflexivity].
   change (interface_field instance output p = Some (Gval ground bits)).
   eapply sync_instance_output_value; [exact suffix_frames|apply source; reflexivity|exact Sync].
 - intros p mi states result found different Known Step.
   unfold circuit_interface in *. rewrite -Known.
   have Preserved : circuit_lookup parent instance result = circuit_lookup parent instance states.
   { eapply sync_step_preserves_lookup; [| |exact Step].
     - intros child grandparent id ports stmts Path Module Query.
       eapply child_frames; eassumption.
     - intros child grandparent Path Query. apply/negP. move/eqP=> Same.
       apply different. subst p grandparent child. reflexivity. }
   rewrite Preserved. reflexivity.
Qed.
Print Assumptions sync_circuit_parent_output.
