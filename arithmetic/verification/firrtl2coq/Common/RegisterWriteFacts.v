From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames RegisterCommitFacts.
Inductive register_write_certificate watched writer : @hfstmt_seq VarOrder.T -> Prop :=
| register_write_here : forall reg rest,
 framed_write_certificate watched writer rest ->
 register_write_certificate watched writer (Qcons (Sreg watched reg) rest)
| register_write_later : forall stmt rest,
 flat_statement stmt = true -> register_write_certificate watched writer rest ->
 register_write_certificate watched writer (Qcons stmt rest).
Lemma register_write_value invalid scope old set_regs watched writer ground previous result_ground bits stmts
 (certificate : register_write_certificate watched writer stmts)
 (known_old : VM.find watched old = Some previous)
 (old_type : type_of_val previous = Gtyp ground)
 (writes : forall position before after,
   VM.find watched before = Some previous ->
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   VM.find watched after = Some (Gval result_ground bits)) :
 forall position before after,
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 VM.find watched after = Some (Gval result_ground bits).
Proof.
 induction certificate as [reg rest framed|stmt rest flat cert IH]; intros position before after ran.
 - cbn [value_iter_statements_with_memory_policy] in ran. rewrite known_old in ran.
   eapply framed_write_value; [exact framed|exact old_type|exact writes| |exact ran].
   apply VM.Lemmas.find_add_eq. reflexivity.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; exact ran.
Qed.
Fixpoint registers_inert eval (stmts : @hfstmt_seq VarOrder.T) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons (Sreg _ reg) rest => (forall proposed, register_next_value eval reg proposed = Some proposed) /\ registers_inert eval rest
 | Qcons (Swhen _ _ _) _ => False
 | Qcons _ rest => registers_inert eval rest end.
Lemma finish_inert_preserves eval old stmts (inert : registers_inert eval stmts) :
 forall before after, finish_registers eval old true before stmts = Some after ->
 forall watched, VM.find watched after = VM.find watched before.
Proof.
 induction stmts as [|stmt rest IH]; intros before after ran watched.
 - inversion ran; subst; reflexivity.
 - destruct stmt as [|id typ|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
   cbn [registers_inert] in inert; try contradiction;
   cbn [finish_registers] in ran; try (eapply IH; eassumption).
   destruct inert as [head tail].
   destruct (VM.find id old) as [previous|] eqn:Old; try discriminate.
   destruct (VM.find id before) as [proposed|] eqn:Before; try discriminate.
   rewrite (head proposed) in ran. rewrite (IH tail _ _ ran watched).
   destruct (N.eq_dec watched id) as [same|different].
   + subst watched. rewrite VM.Lemmas.find_add_eq; [symmetry; exact Before|reflexivity].
   + apply VM.Lemmas.find_add_neq. move/eqP=> E. exact (different E).
Qed.
Lemma pass_register_write_value invalid old before after stmts watched writer ground previous result_ground bits
 (certificate : register_write_certificate watched writer stmts)
 (known_old : VM.find watched old = Some previous)
 (old_type : type_of_val previous = Gtyp ground)
 (inert : registers_inert (fun expr => eval_hfexpr_with_memory empty_memory_map expr old old) stmts)
 (writes : forall position initial final,
   VM.find watched initial = Some previous ->
   one_statement invalid [::] position empty_memory_map old true initial writer = Some final ->
   VM.find watched final = Some (Gval result_ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before stmts = Some after) :
 VM.find watched after = Some (Gval result_ground bits).
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old true before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite (finish_inert_preserves _ _ _ inert _ _ ran watched).
 eapply register_write_value; eassumption.
Qed.
Print Assumptions pass_register_write_value.
Definition flat_writer_target (stmt : @hfstmt VarOrder.T) : option (VarOrder.T * @hfexpr VarOrder.T) :=
 match stmt with Sfcnct (Eid id) expr => Some (id,expr) | _ => None end.
Lemma flat_writer_target_shape stmt id expr : flat_writer_target stmt = Some (id,expr) -> stmt = Sfcnct (Eid id) expr.
Proof. destruct stmt; try discriminate. destruct h; try discriminate. intro E; inversion E; reflexivity. Qed.
Fixpoint checked_framed_writer watched (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons stmt rest => match flat_writer_target stmt with
   | Some (id,expr) => if watched == id then
       if flat_sequence_frames watched rest then Some expr else None
     else if flat_statement_frames watched stmt then checked_framed_writer watched rest else None
   | None => if flat_statement_frames watched stmt then checked_framed_writer watched rest else None
   end
 end.
Lemma checked_framed_writer_sound watched stmts expr :
 checked_framed_writer watched stmts = Some expr ->
 framed_write_certificate watched (Sfcnct (Eid watched) expr) stmts.
Proof.
 induction stmts as [|stmt rest IH]; [discriminate|].
 cbn [checked_framed_writer].
 destruct (flat_writer_target stmt) as [[id rhs]|] eqn:Target.
 - destruct (watched == id) eqn:Same.
   + move/eqP: Same => Same. subst id.
     have shape := flat_writer_target_shape stmt watched rhs Target. subst stmt.
     destruct (flat_sequence_frames watched rest) eqn:Frame; try discriminate.
     intro E; inversion E; subst expr. apply framed_write_here; [reflexivity|exact Frame].
   + destruct (flat_statement_frames watched stmt) eqn:Frame; try discriminate.
     intro E; apply framed_write_later; [exact Frame|exact (IH E)].
 - destruct (flat_statement_frames watched stmt) eqn:Frame; try discriminate.
   intro E; apply framed_write_later; [exact Frame|exact (IH E)].
Qed.
Fixpoint checked_register_writer watched (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Sreg id _) rest => if watched == id then checked_framed_writer watched rest else checked_register_writer watched rest
 | Qcons stmt rest => if flat_statement stmt then checked_register_writer watched rest else None
 end.
Lemma checked_register_writer_sound watched stmts expr :
 checked_register_writer watched stmts = Some expr ->
 register_write_certificate watched (Sfcnct (Eid watched) expr) stmts.
Proof.
 induction stmts as [|stmt rest IH]; [discriminate|].
 destruct stmt as [|id typ|id reg|id mem|id module_id|id rhs|lhs rhs|ref|cond yes no];
 cbn [checked_register_writer];
 try (match goal with |- (if ?test then _ else _) = _ -> _ =>
       destruct test eqn:Flat; try discriminate; intro E;
       apply register_write_later; [exact Flat|exact (IH E)] end);
 try discriminate;
 try (intro E; apply register_write_later; [reflexivity|exact (IH E)]).
 destruct (watched == id) eqn:Same.
 - move/eqP: Same => Same. subst id. intro E. apply register_write_here.
   exact (checked_framed_writer_sound watched rest expr E).
 - intro E. apply register_write_later; [reflexivity|exact (IH E)].
Qed.
