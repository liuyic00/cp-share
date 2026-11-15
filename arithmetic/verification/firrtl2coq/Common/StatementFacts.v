From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Lemma replace_source_passive old value (passive : is_passive_value value = true) :
  replace_writeable Source old value = Some old.
Proof. destruct value; cbn [replace_writeable] in *; rewrite ?passive; reflexivity. Qed.

Lemma adapt_ground_passive value ground result
  (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some result) :
  is_passive_value result = true.
Proof.
  destruct value; destruct ground; simpl in adapted; try discriminate;
    repeat match type of adapted with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    | context [if ?x then _ else _] => destruct x eqn:?
    end; inversion adapted; reflexivity.
Qed.

Lemma unidirectional_connect_preserves_other mm set_regs old before after lhs rhs watched
  (different : watched <> HiF.base_ref lhs)
  (connected : unidirectional_connect_with_memory mm set_regs lhs rhs old before = Some after)
  (scalar_lhs : exists id, lhs = @Eid VarOrder.T id) :
  VM.find watched after = VM.find watched before.
Proof.
  destruct scalar_lhs as [id ->].
  unfold unidirectional_connect_with_memory, unidirectional_connect_bundle in connected.
  simpl in different, connected.
  repeat match type of connected with
  | context [match ?x with _ => _ end] => destruct x eqn:?
  end; try discriminate.
  inversion connected; subst. apply VM.Lemmas.find_add_neq. move/eqP=> same. exact (different same).
Qed.

Lemma bidirectional_eid_source_preserved mm old before after lhs watched ground bits
  (different : watched <> HiF.base_ref lhs)
  (known : VM.find watched before = Some (Gval ground bits))
  (connected : bidirectional_connect_with_memory mm lhs (@Eid VarOrder.T watched)
    old before = Some after) :
  VM.find watched after = Some (Gval ground bits).
Proof.
  unfold bidirectional_connect_with_memory in connected.
  destruct (VM.find (HiF.base_ref lhs) before) as [left_old|] eqn:Lold; try discriminate.
  destruct (eval_type_of_ref lhs before) as [left_type|] eqn:Ltype; try discriminate.
  destruct (eval_href_with_memory mm (@Eid VarOrder.T watched) old old) as [right_value|] eqn:Rvalue; try discriminate.
  destruct (adapt_hvalue_as_type right_value left_type) as [adapted_left|] eqn:Ladapt; try discriminate.
  destruct (repl_val_part lhs (replace_writeable Sink) left_old adapted_left old) as [new_left|] eqn:Lwrite; try discriminate.
  cbn [option_map] in connected.
  have kept : VM.find watched (VM.add (HiF.base_ref lhs) new_left before) = Some (Gval ground bits).
  { rewrite VM.Lemmas.find_add_neq; [exact known|move/eqP=> E; exact (different E)]. }
  cbn [HiF.base_ref eval_type_of_ref] in connected.
  rewrite kept in connected. cbn [option_map type_of_val] in connected.
  destruct (eval_href_with_memory mm lhs old old) as [source|] eqn:Lvalue; try discriminate.
  destruct (adapt_hvalue_as_type source (Gtyp ground)) as [adapted_right|] eqn:Radapt; try discriminate.
  have passive : is_passive_value adapted_right = true by (eapply adapt_ground_passive; exact Radapt).
  cbn [repl_val_part] in connected.
  rewrite (replace_source_passive _ _ passive) in connected.
  cbn [option_map] in connected. inversion connected; subst after.
  apply VM.Lemmas.find_add_eq. exact (eq_refl watched).
Qed.
Print Assumptions bidirectional_eid_source_preserved.

Lemma unidirectional_bundle_preserves_other mm old before after lhs rhs watched
  (different : watched <> HiF.base_ref lhs)
  (connected : unidirectional_connect_bundle mm lhs rhs old before = Some after) :
  VM.find watched after = VM.find watched before.
Proof.
  unfold unidirectional_connect_bundle in connected.
  repeat match type of connected with
  | context [match ?x with _ => _ end] => destruct x eqn:?
  | context [option_map ?f ?x] => destruct x eqn:?; cbn [option_map] in connected
  end; try discriminate.
  simpl in connected. inversion connected; subst.
  apply VM.Lemmas.find_add_neq. move/eqP=> same. exact (different same).
Qed.

Lemma bidirectional_preserves_other mm old before after lhs rhs watched
  (left_different : watched <> HiF.base_ref lhs)
  (right_different : watched <> HiF.base_ref rhs)
  (connected : bidirectional_connect_with_memory mm lhs rhs old before = Some after) :
  VM.find watched after = VM.find watched before.
Proof.
  unfold bidirectional_connect_with_memory in connected.
  destruct (VM.find (HiF.base_ref lhs) before) as [left_old|] eqn:Lold; try discriminate.
  destruct (eval_type_of_ref lhs before) as [left_type|] eqn:Ltype; try discriminate.
  destruct (eval_href_with_memory mm rhs old old) as [right_value|] eqn:Rvalue; try discriminate.
  destruct (adapt_hvalue_as_type right_value left_type) as [adapted_left|] eqn:Ladapt; try discriminate.
  destruct (repl_val_part lhs (replace_writeable Sink) left_old adapted_left old) as [new_left|] eqn:Lwrite; try discriminate.
  cbn [option_map] in connected.
  repeat match type of connected with
  | context [match ?x with _ => _ end] => destruct x eqn:?
  | context [option_map ?f ?x] => destruct x eqn:?; cbn [option_map] in connected
  end; try discriminate.
  inversion connected; subst.
  rewrite VM.Lemmas.find_add_neq; last by move/eqP=> E; exact (right_different E).
  apply VM.Lemmas.find_add_neq. move/eqP=> E. exact (left_different E).
Qed.

Definition flat_ref (r : @href VarOrder.T) : bool :=
  match r with Eid _ | Esubfield (Eid _) _ => true | _ => false end.

Lemma flat_ref_no_memory_writer r (flat : flat_ref r = true) :
  is_memory_writer_ref empty_memory_map r = false.
Proof.
  destruct r as [id|r field|r index|r expr]; try discriminate; [reflexivity|].
  destruct r; try discriminate. reflexivity.
Qed.

Lemma flat_ref_unidirectional mm set_regs lhs rhs old before
  (flat : flat_ref lhs = true) :
  unidirectional_connect_with_memory mm set_regs lhs rhs old before =
  unidirectional_connect_bundle mm lhs rhs old before.
Proof.
  destruct lhs as [id|r field|r index|r expr]; try discriminate; [reflexivity|].
  destruct r; try discriminate. reflexivity.
Qed.

Definition flat_statement_frames (watched : VarOrder.T) (stmt : @hfstmt VarOrder.T) : bool :=
  match stmt with
  | Sskip | Sinst _ _ => true
  | Swire id _ | Sreg id _ | Snode id _ => id != watched
  | Sfcnct lhs rhs =>
      flat_ref lhs && (HiF.base_ref lhs != watched) &&
      match rhs with
      | Eref r => flat_ref r &&
          match r with Eid _ => true | _ => HiF.base_ref r != watched end
      | _ => true
      end
  | _ => false
  end.
Fixpoint flat_sequence_frames (watched : VarOrder.T) (stmts : @hfstmt_seq VarOrder.T) : bool :=
  match stmts with
  | Qnil => true
  | Qcons stmt rest => flat_statement_frames watched stmt && flat_sequence_frames watched rest
  end.

Definition flat_statement (stmt : @hfstmt VarOrder.T) : bool :=
  match stmt with Swhen _ _ _ | Smem _ _ | Sinvalid _ => false | _ => true end.
Definition one_statement invalid scope position mm old set_regs before stmt :=
  value_iter_statements_with_memory_policy invalid scope position mm old set_regs before
    (@Qcons VarOrder.T stmt (@Qnil VarOrder.T)).

Lemma flat_statement_decompose invalid scope position mm old set_regs before stmt rest
  (flat : flat_statement stmt = true) :
  value_iter_statements_with_memory_policy invalid scope position mm old set_regs before
    (@Qcons VarOrder.T stmt rest) =
  match one_statement invalid scope position mm old set_regs before stmt with
  | Some middle => value_iter_statements_with_memory_policy invalid scope (S position)
      mm old set_regs middle rest
  | None => None
  end.
Proof.
  destruct stmt; try discriminate; try reflexivity;
    try (destruct h0; try reflexivity);
    cbn [one_statement value_iter_statements_with_memory_policy];
    repeat match goal with
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
    | |- context [if ?x then _ else _] => destruct x eqn:?
    end; reflexivity.
Qed.

Lemma different_id (a b : VarOrder.T) (different : a != b) : b <> a.
Proof. move/negP: different => H E. apply H. apply/eqP. symmetry. exact E. Qed.
Lemma find_add_other watched id (value : hvalue) (before : VM.t hvalue) (different : id != watched) :
  VM.find watched (VM.add id value before) = VM.find watched before.
Proof. apply VM.Lemmas.find_add_neq. move/eqP=> E. exact (different_id id watched different E). Qed.

Lemma one_statement_nonref invalid scope position old set_regs before after lhs rhs
  (notref : match rhs with Eref _ => false | _ => true end = true)
  (ran : one_statement invalid scope position empty_memory_map old set_regs before
    (Sfcnct lhs rhs) = Some after) :
  unidirectional_connect_with_memory empty_memory_map set_regs lhs rhs old before = Some after.
Proof.
  destruct rhs; try discriminate; cbn [one_statement value_iter_statements_with_memory_policy] in ran;
    repeat match type of ran with
    | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
    end; inversion ran; subst; reflexivity.
Qed.

Lemma one_statement_ref invalid scope position old set_regs before after lhs rhs
  (flat : flat_ref lhs = true)
  (ran : one_statement invalid scope position empty_memory_map old set_regs before
    (Sfcnct lhs (Eref rhs)) = Some after) :
  bidirectional_connect_with_memory empty_memory_map lhs rhs old before = Some after.
Proof.
  cbn [one_statement value_iter_statements_with_memory_policy] in ran.
  rewrite (flat_ref_no_memory_writer lhs flat) in ran.
  destruct (bidirectional_connect_with_memory empty_memory_map lhs rhs old before) eqn:E;
    inversion ran; subst; reflexivity.
Qed.

Lemma one_statement_frames_known invalid scope position old set_regs before after stmt watched ground bits
  (frame : flat_statement_frames watched stmt = true)
  (known : VM.find watched before = Some (Gval ground bits))
  (ran : one_statement invalid scope position empty_memory_map old set_regs before stmt = Some after) :
  VM.find watched after = Some (Gval ground bits).
Proof.
  destruct stmt as [|id t|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
    cbn [flat_statement_frames] in frame; try discriminate.
  - inversion ran; subst; exact known.
  - cbn [one_statement value_iter_statements_with_memory_policy] in ran.
    inversion ran; subst. rewrite (find_add_other _ _ _ _ frame). exact known.
  - cbn [one_statement value_iter_statements_with_memory_policy] in ran.
    destruct (VM.find id old); inversion ran; subst.
    rewrite (find_add_other _ _ _ _ frame). exact known.
  - inversion ran; subst; exact known.
  - cbn [one_statement value_iter_statements_with_memory_policy] in ran.
    destruct (eval_hfexpr_with_memory empty_memory_map expr old old); inversion ran; subst.
    rewrite (find_add_other _ _ _ _ frame). exact known.
  - move/andP: frame => [/andP [flat different] source_frame].
    have left_different : watched <> HiF.base_ref lhs := different_id _ _ different.
    destruct expr as [t constant|cast value|op value|op a b|cond a b|cond value|rhs];
      try (eapply one_statement_nonref in ran; [|reflexivity]);
      try (rewrite (flat_ref_unidirectional _ _ _ _ _ _ flat) in ran;
        rewrite (unidirectional_bundle_preserves_other _ _ _ _ _ _ _ left_different ran); exact known).
    have connection := one_statement_ref _ _ _ _ _ _ _ _ _ flat ran.
    destruct rhs as [source|r field|r index|r value].
    + destruct (N.eq_dec source watched) as [same|different_source].
      * subst source. eapply bidirectional_eid_source_preserved; eassumption.
      * have right_different : watched <> HiF.base_ref (@Eid VarOrder.T source) by (simpl; congruence).
        rewrite (bidirectional_preserves_other empty_memory_map old before after lhs (@Eid VarOrder.T source) watched left_different right_different connection).
        exact known.
    + move/andP: source_frame => [_ different_source].
      rewrite (bidirectional_preserves_other _ _ _ _ _ _ _ left_different (different_id _ _ different_source) connection).
      exact known.
    + discriminate source_frame.
    + discriminate source_frame.
Qed.

Lemma frame_statement_flat watched stmt (framed : flat_statement_frames watched stmt = true) :
  flat_statement stmt = true.
Proof. destruct stmt; try discriminate; reflexivity. Qed.

Lemma flat_sequence_preserves_known invalid scope old set_regs watched ground bits stmts :
  forall position before after,
  flat_sequence_frames watched stmts = true ->
  VM.find watched before = Some (Gval ground bits) ->
  value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
  VM.find watched after = Some (Gval ground bits).
Proof.
  induction stmts as [|stmt rest IH]; intros position before after frame known ran.
  - inversion ran; subst; exact known.
  - move/andP: frame => [head_frame tail_frame].
    rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (frame_statement_flat _ _ head_frame)) in ran.
    destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
    eapply IH; [exact tail_frame| |exact ran].
    eapply one_statement_frames_known; eassumption.
Qed.

(* A finite syntactic certificate locates a node and excludes subsequent writes
   to it. Prefix statements may update any other values; expression reads use
   the interpreter's original old environment. *)
Inductive node_certificate (watched : VarOrder.T) (expr : @hfexpr VarOrder.T) :
  @hfstmt_seq VarOrder.T -> Prop :=
| node_certificate_here : forall rest,
    flat_sequence_frames watched rest = true ->
    node_certificate watched expr (Qcons (Snode watched expr) rest)
| node_certificate_later : forall stmt rest,
    flat_statement stmt = true -> node_certificate watched expr rest ->
    node_certificate watched expr (Qcons stmt rest).

Lemma node_certificate_value invalid scope old set_regs watched expr ground bits stmts
  (certificate : node_certificate watched expr stmts)
  (evaluated : eval_hfexpr_with_memory empty_memory_map expr old old = Some (Gval ground bits)) :
  forall position before after,
  value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
  VM.find watched after = Some (Gval ground bits).
Proof.
  induction certificate as [rest framed|stmt rest flat certificate IH]; intros position before after ran.
  - cbn [value_iter_statements_with_memory_policy] in ran. rewrite evaluated in ran.
    eapply flat_sequence_preserves_known; [exact framed| |exact ran].
    apply VM.Lemmas.find_add_eq. exact (eq_refl watched).
  - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
    destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
    eapply IH. exact ran.
Qed.
Print Assumptions node_certificate_value.

Fixpoint registers_frame (watched : VarOrder.T) (stmts : @hfstmt_seq VarOrder.T) : bool :=
  match stmts with
  | Qnil => true
  | Qcons (Sreg id _) rest => (id != watched) && registers_frame watched rest
  | Qcons (Swhen _ _ _) _ => false
  | Qcons _ rest => registers_frame watched rest
  end.

Lemma finish_registers_preserves_other eval old set_regs watched stmts :
  forall before after,
  registers_frame watched stmts = true ->
  finish_registers eval old set_regs before stmts = Some after ->
  VM.find watched after = VM.find watched before.
Proof.
  induction stmts as [|stmt rest IH]; intros before after frame finished.
  - inversion finished; subst; reflexivity.
  - destruct stmt as [|id t|id reg|id mem|id module_id|id expr|lhs expr|ref|cond yes no];
      cbn [registers_frame] in frame; try discriminate;
      cbn [finish_registers] in finished; try (eapply IH; eassumption).
    move/andP: frame => [different framed].
    destruct (VM.find id old) as [old_value|] eqn:O; try discriminate.
    destruct (VM.find id before) as [proposed|] eqn:P; try discriminate.
    destruct (if set_regs then register_next_value eval reg proposed else Some old_value) as [value|] eqn:V; try discriminate.
    rewrite (IH _ _ framed finished). apply find_add_other. exact different.
Qed.

Lemma stable_node_value invalid env stmts watched expr ground bits
  (certificate : node_certificate watched expr stmts)
  (not_register : registers_frame watched stmts = true)
  (evaluated : eval_hfexpr_with_memory empty_memory_map expr env env = Some (Gval ground bits))
  (fixed : value_iter_with_memory_policy invalid empty_memory_map env false env stmts = Some env) :
  VM.find watched env = Some (Gval ground bits).
Proof.
  unfold value_iter_with_memory_policy in fixed.
  destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map env false env stmts) as [proposed|] eqn:Ran; try discriminate.
  rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register fixed).
  eapply node_certificate_value; eassumption.
Qed.
Print Assumptions stable_node_value.

Lemma pass_node_value invalid old before after stmts watched expr ground bits
  (certificate : node_certificate watched expr stmts)
  (not_register : registers_frame watched stmts = true)
  (evaluated : eval_hfexpr_with_memory empty_memory_map expr old old = Some (Gval ground bits))
  (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
  VM.find watched after = Some (Gval ground bits).
Proof.
  unfold value_iter_with_memory_policy in ran.
  destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
  rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
  eapply node_certificate_value; eassumption.
Qed.
Print Assumptions pass_node_value.
