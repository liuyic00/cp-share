From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts.

Inductive register_commit_certificate (watched : VarOrder.T) (reg : @hfreg VarOrder.T) : @hfstmt_seq VarOrder.T -> Prop :=
| register_commit_here : forall rest,
 registers_frame watched rest = true ->
 register_commit_certificate watched reg (Qcons (Sreg watched reg) rest)
| register_commit_later : forall stmt rest,
 registers_frame watched (Qcons stmt (@Qnil VarOrder.T)) = true ->
 register_commit_certificate watched reg rest ->
 register_commit_certificate watched reg (Qcons stmt rest).

Lemma finish_register_target eval old watched reg stmts old_value proposed next
 (certificate : register_commit_certificate watched reg stmts)
 (old_found : VM.find watched old = Some old_value)
 (next_value : register_next_value eval reg proposed = Some next) :
 forall before after,
 VM.find watched before = Some proposed ->
 finish_registers eval old true before stmts = Some after ->
 VM.find watched after = Some next.
Proof.
 induction certificate as [rest framed|stmt rest framed certificate IH]; intros before after Proposed Finished.
 - cbn [finish_registers] in Finished. rewrite old_found Proposed next_value in Finished.
   rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ framed Finished).
   apply VM.Lemmas.find_add_eq. reflexivity.
 - destruct stmt as [|id ty|id r|id mem|id mi|id expr|lhs rhs|ref|cond yes no];
   cbn [registers_frame] in framed; try discriminate;
   cbn [finish_registers] in Finished; try (eapply IH; eassumption).
   move/andP: framed => [different _].
   destruct (VM.find id old) as [prior|] eqn:Old; try discriminate.
   destruct (VM.find id before) as [proposal|] eqn:Proposal; try discriminate.
   destruct (register_next_value eval r proposal) as [result|] eqn:Result; try discriminate.
   eapply IH; [|exact Finished]. rewrite find_add_other; [exact Proposed|exact different].
Qed.

Lemma commit_pass_register_value invalid old before after stmts watched reg old_value proposed next
 (certificate : register_commit_certificate watched reg stmts)
 (old_found : VM.find watched old = Some old_value)
 (next_value : register_next_value (fun e => eval_hfexpr_with_memory empty_memory_map e old old) reg proposed = Some next)
 (proposed_value : forall state,
   value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old true before stmts = Some state ->
   VM.find watched state = Some proposed)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before stmts = Some after) :
 VM.find watched after = Some next.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old true before stmts) as [state|] eqn:Statements; try discriminate.
 eapply finish_register_target; [exact certificate|exact old_found|exact next_value| |exact ran].
 apply proposed_value. reflexivity.
Qed.
Print Assumptions commit_pass_register_value.
Lemma unidirectional_eid_target mm set_regs old before after target expr ground value result
 (target_type : eval_type_of_ref (@Eid VarOrder.T target) before = Some (Gtyp ground))
 (evaluated : eval_hfexpr_with_memory mm expr old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some result)
 (ran : unidirectional_connect_with_memory mm set_regs (@Eid VarOrder.T target) expr old before = Some after) :
 VM.find target after = Some result.
Proof.
 unfold unidirectional_connect_with_memory, unidirectional_connect_bundle in ran.
 cbn [HiF.base_ref] in ran.
 destruct (VM.find target before) as [previous|]; try discriminate.
 rewrite target_type evaluated adapted in ran.
 cbn [repl_val_part option_map] in ran. inversion ran; subst after.
 apply VM.Lemmas.find_add_eq. reflexivity.
Qed.

Fixpoint register_commit_check watched (stmts : @hfstmt_seq VarOrder.T) : option (@hfreg VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Sreg id reg) rest =>
   if id == watched then if registers_frame watched rest then Some reg else None
   else register_commit_check watched rest
 | Qcons (Swhen _ _ _) _ => None
 | Qcons _ rest => register_commit_check watched rest
 end.
Lemma register_commit_check_sound watched stmts reg
 (checked : register_commit_check watched stmts = Some reg) :
 register_commit_certificate watched reg stmts.
Proof.
 revert reg checked. induction stmts as [|stmt rest IH]; intros reg checked; [discriminate|].
 destruct stmt as [|id ty|id r|id mem|id mi|id expr|lhs rhs|ref|cond yes no];
 cbn [register_commit_check] in checked; try discriminate;
 try (apply register_commit_later; [reflexivity|apply IH; exact checked]).
 destruct (id == watched) eqn:Same.
 - destruct (registers_frame watched rest) eqn:Framed; inversion checked; subst r.
   move/eqP: Same => Same. subst id. apply register_commit_here. exact Framed.
 - apply register_commit_later.
   + cbn [registers_frame]. rewrite Same. reflexivity.
   + apply IH. exact checked.
Qed.
Print Assumptions register_commit_check_sound.
