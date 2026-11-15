From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts SourceFieldFrames.
Definition instance_check {Job:Type} (test:SVM.key -> Job -> bool) (jobs:SVM.t Job) :=
 SVM.fold (fun path job prior => test path job && prior) jobs true.
Lemma instance_check_sound (Job:Type) (test:SVM.key -> Job -> bool) jobs :
 instance_check test jobs = true -> forall path job,
 SVM.find path jobs = Some job -> test path job = true.
Proof.
 unfold instance_check.
 apply (SVM.Lemmas.P.fold_rec (P:=fun done result => result=true -> forall path job, SVM.find path done=Some job -> test path job=true)).
 - intros done empty H path job found. exfalso. apply (empty path job). apply SVM.Lemmas.find_mapsto_iff. exact found.
 - intros path job acc done next member fresh added IH checked query value found.
   move/andP: checked=>[head tail].
   unfold SVM.Lemmas.P.Add in added. rewrite (added query) in found.
   destruct (query == path) eqn:E.
   + rewrite SVM.Lemmas.find_add_eq in found; [|exact E]. inversion found;subst value.
     move/eqP: E=>E;subst query. exact head.
   + rewrite SVM.Lemmas.find_add_neq in found; [|by rewrite E].
     exact (IH tail query value found).
Qed.
Definition node_sync_entry modules query watched path module_id :=
 match path with
 | [::] => true
 | child::parent =>
   (match find_module modules module_id with
    | Some (FInmod _ ports _) => if query == path then all (child_port_frames watched) ports else true
    | _ => false end) && (if query == parent then child != watched else true)
 end.
Definition node_sync_check modules instances query watched := instance_check (node_sync_entry modules query watched) instances.
Lemma node_sync_check_child modules instances query watched
 (checked:node_sync_check modules instances query watched=true) :
 forall path module_id child parent id ports body,
 SVM.find path instances=Some module_id -> path=child::parent ->
 find_module modules module_id=Some(FInmod id ports body) ->
 query=path -> all(child_port_frames watched)ports=true.
Proof.
 intros path module_id child parent id ports body found path_eq body_eq query_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold node_sync_entry in H. subst path query. rewrite body_eq eqxx in H.
 by move/andP:H=>[H _].
Qed.
Lemma node_sync_check_parent modules instances query watched
 (checked:node_sync_check modules instances query watched=true) :
 forall path module_id child parent,
 SVM.find path instances=Some module_id -> path=child::parent ->
 query=parent -> child != watched.
Proof.
 intros path module_id child parent found path_eq query_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold node_sync_entry in H. subst path query. rewrite eqxx in H.
 by move/andP:H=>[_ H].
Qed.
Definition field_sync_entry modules query instance field path module_id :=
 match path with
 | [::] => true
 | child::parent => match find_module modules module_id with
   | Some (FInmod _ ports _) =>
     (if query == path then all (child_port_frames instance) ports else true) &&
     (if (query == parent) && (child == instance) then all (parent_port_frames field) ports else true)
   | _ => false end
 end.
Definition field_sync_check modules instances query instance field := instance_check (field_sync_entry modules query instance field) instances.
Lemma field_sync_check_child modules instances query instance field
 (checked:field_sync_check modules instances query instance field=true) :
 forall path module_id child parent id ports body,
 SVM.find path instances=Some module_id -> path=child::parent ->
 find_module modules module_id=Some(FInmod id ports body) ->
 query=path -> all(child_port_frames instance)ports=true.
Proof.
 intros path module_id child parent id ports body found path_eq body_eq query_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold field_sync_entry in H. subst path query. rewrite body_eq eqxx in H.
 by move/andP:H=>[H _].
Qed.
Lemma field_sync_check_parent modules instances query instance field
 (checked:field_sync_check modules instances query instance field=true) :
 forall path module_id child parent id ports body,
 SVM.find path instances=Some module_id -> path=child::parent ->
 find_module modules module_id=Some(FInmod id ports body) ->
 query=parent -> child = instance -> all(parent_port_frames field)ports=true.
Proof.
 intros path module_id child parent id ports body found path_eq body_eq query_eq child_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold field_sync_entry in H. subst path query child. rewrite body_eq !eqxx in H.
 by move/andP:H=>[_ H].
Qed.
Print Assumptions field_sync_check_parent.
Definition parent_only_entry (query:SVM.key) (watched:VarOrder.T) (path:SVM.key) (_:VarOrder.T) :=
 match path with [::]=>true | child::parent => if query == parent then child != watched else true end.
Definition parent_only_check instances query watched := instance_check (parent_only_entry query watched) instances.
Lemma parent_only_check_sound instances query watched
 (checked:parent_only_check instances query watched=true) :
 forall path module_id child parent,
 SVM.find path instances=Some module_id -> path=child::parent -> query=parent -> child != watched.
Proof.
 intros path module_id child parent found path_eq query_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold parent_only_entry in H. subst path query. by rewrite eqxx in H.
Qed.
Definition child_only_entry modules (query:SVM.key) watched (path:SVM.key) module_id :=
 match path with [::]=>true | _::_ =>
 match find_module modules module_id with Some(FInmod _ ports _) => if query == path then all(child_port_frames watched)ports else true | _=>false end end.
Definition child_only_check modules instances query watched := instance_check (child_only_entry modules query watched) instances.
Lemma child_only_check_sound modules instances query watched
 (checked:child_only_check modules instances query watched=true) :
 forall path module_id child parent id ports body,
 SVM.find path instances=Some module_id -> path=child::parent ->
 find_module modules module_id=Some(FInmod id ports body) -> query=path -> all(child_port_frames watched)ports=true.
Proof.
 intros path module_id child parent id ports body found path_eq body_eq query_eq.
 have H:=instance_check_sound _ _ _ checked path module_id found.
 unfold child_only_entry in H. subst path query. by rewrite body_eq eqxx in H.
Qed.
