From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts.
Definition initial_statement_frames watched (stmt : @hfstmt VarOrder.T) :=
 match stmt with
 | Swire id _ | Sreg id _ | Snode id _ | Sinst id _ => id != watched
 | Sskip | Sfcnct _ _ | Sinvalid _ => true
 | _ => false end.
Fixpoint initial_sequence_frames watched (stmts : @hfstmt_seq VarOrder.T) :=
 match stmts with Qnil => true
 | Qcons stmt rest => initial_statement_frames watched stmt && initial_sequence_frames watched rest end.
Lemma initial_sequence_preserves modules previous watched stmts :
 forall before after, initial_sequence_frames watched stmts = true ->
 statements_initial_map_with_memory modules stmts previous before = Some after ->
 VM.find watched after = VM.find watched before.
Proof.
 induction stmts as [|stmt rest IH]; intros before after frames ran.
 - inversion ran; subst; reflexivity.
 - move/andP: frames => [head tail].
   destruct stmt as [|id typ|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
    cbn [initial_statement_frames] in head; try discriminate;
    cbn [statements_initial_map_with_memory] in ran;
    try (eapply IH; eassumption).
   all: repeat match type of ran with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   end; try discriminate.
   all: rewrite (IH _ _ tail ran); apply find_add_other; exact head.
Qed.
Definition initial_one modules previous before stmt :=
 statements_initial_map_with_memory modules (Qcons stmt (@Qnil VarOrder.T)) previous before.
Lemma initial_flat_decompose modules previous before stmt rest
 (flat : flat_statement stmt = true) :
 statements_initial_map_with_memory modules (Qcons stmt rest) previous before =
 match initial_one modules previous before stmt with
 | Some middle => statements_initial_map_with_memory modules rest previous middle
 | None => None end.
Proof.
 destruct stmt; try discriminate flat;
 cbn [initial_one statements_initial_map_with_memory];
 repeat match goal with
 | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
 end; reflexivity.
Qed.
Inductive initial_register_certificate watched : @hfstmt_seq VarOrder.T -> Prop :=
| initial_register_here : forall reg rest,
 initial_sequence_frames watched rest = true ->
 initial_register_certificate watched (Qcons (Sreg watched reg) rest)
| initial_register_later : forall stmt rest,
 flat_statement stmt = true -> initial_register_certificate watched rest ->
 initial_register_certificate watched (Qcons stmt rest).
Lemma initial_register_value modules old watched value stmts
 (known : VM.find watched old = Some value)
 (certificate : initial_register_certificate watched stmts) :
 forall before after,
 statements_initial_map_with_memory modules stmts (Some old) before = Some after ->
 VM.find watched after = Some value.
Proof.
 induction certificate as [reg rest framed|stmt rest flat cert IH]; intros before after ran.
 - cbn [statements_initial_map_with_memory] in ran. rewrite known in ran.
   rewrite (initial_sequence_preserves _ _ _ _ _ _ framed ran).
   apply VM.Lemmas.find_add_eq. reflexivity.
 - rewrite (initial_flat_decompose _ _ _ _ _ flat) in ran.
   destruct (initial_one modules (Some old) before stmt) eqn:One; try discriminate.
   eapply IH; exact ran.
Qed.
Print Assumptions initial_register_value.
Fixpoint checked_initial_register watched (stmts : @hfstmt_seq VarOrder.T) : bool :=
 match stmts with
 | Qnil => false
 | Qcons (Sreg id reg) rest => if watched == id then initial_sequence_frames watched rest else checked_initial_register watched rest
 | Qcons stmt rest => flat_statement stmt && checked_initial_register watched rest
 end.
Lemma checked_initial_register_sound watched stmts :
 checked_initial_register watched stmts = true -> initial_register_certificate watched stmts.
Proof.
 induction stmts as [|stmt rest IH]; [discriminate|].
 destruct stmt as [|id typ|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
 cbn [checked_initial_register];
 try (move/andP=> [flat checked]; apply initial_register_later; [exact flat|exact (IH checked)]).
 destruct (watched == id) eqn:Same.
 - move/eqP: Same => Same. subst id. intro framed. apply initial_register_here. exact framed.
 - intro checked. apply initial_register_later; [reflexivity|exact (IH checked)].
Qed.
Lemma single_module_initial_local modules top ports stmts previous external states
 (instances : find_circuit_instances modules top = Some (SVM.add [::] top (SVM.empty VarOrder.T)))
 (module_found : find_module modules top = Some (FInmod top ports stmts))
 (ran : circuit_initial_map_with_memory modules top previous external = Some states) :
 exists declared env,
 statements_initial_map_with_memory modules stmts
   (match previous with Some maps => SVM.find [::] maps | None => None end)
   (ports_initial_map ports) = Some declared /\
 update_external_ports declared external ports = Some env /\
 SVM.find [::] states = Some env.
Proof.
 unfold circuit_initial_map_with_memory in ran. rewrite instances SVM.fold_1 in ran.
 have elements : SVM.elements (SVM.add [::] top (SVM.empty VarOrder.T)) = [:: ([::],top)] by reflexivity.
 rewrite elements in ran. cbn [List.fold_left fst snd] in ran.
 unfold module_initial_map_with_memory in ran. rewrite !module_found in ran.
 cbn beta iota zeta in ran.
 destruct (statements_initial_map_with_memory modules stmts
   (match previous with Some maps => SVM.find [::] maps | None => None end)
   (ports_initial_map ports)) as [declared|] eqn:Declared; try discriminate.
 change (match update_external_ports declared external ports with
 | Some env => Some (SVM.add [::] env (SVM.add [::] declared (SVM.empty (VM.t hvalue))))
 | None => None end = Some states) in ran.
 destruct (update_external_ports declared external ports) as [env|] eqn:External; try discriminate.
 inversion ran; subst states. exists declared,env. split; [reflexivity|]. split; [exact External|].
 apply SVM.Lemmas.find_add_eq. reflexivity.
Qed.
