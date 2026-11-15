From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ConnectionFacts.

Lemma bidirectional_eid_ground_source_preserved mm old before after lhs watched ground value
  (different : watched <> HiF.base_ref lhs)
  (ground_type : type_of_val value = Gtyp ground)
  (known : VM.find watched before = Some value)
  (connected : bidirectional_connect_with_memory mm lhs (@Eid VarOrder.T watched)
    old before = Some after) :
  VM.find watched after = Some value.
Proof.
  unfold bidirectional_connect_with_memory in connected.
  destruct (VM.find (HiF.base_ref lhs) before) as [left_old|] eqn:Lold; try discriminate.
  destruct (eval_type_of_ref lhs before) as [left_type|] eqn:Ltype; try discriminate.
  destruct (eval_href_with_memory mm (@Eid VarOrder.T watched) old old) as [right_value|] eqn:Rvalue; try discriminate.
  destruct (adapt_hvalue_as_type right_value left_type) as [adapted_left|] eqn:Ladapt; try discriminate.
  destruct (repl_val_part lhs (replace_writeable Sink) left_old adapted_left old) as [new_left|] eqn:Lwrite; try discriminate.
  cbn [option_map] in connected.
  have kept : VM.find watched (VM.add (HiF.base_ref lhs) new_left before) = Some value.
  { rewrite VM.Lemmas.find_add_neq; [exact known|move/eqP=> E; exact (different E)]. }
  cbn [HiF.base_ref eval_type_of_ref] in connected.
  rewrite kept in connected. cbn [option_map] in connected. rewrite ground_type in connected.
  destruct (eval_href_with_memory mm lhs old old) as [source|] eqn:Lvalue; try discriminate.
  destruct (adapt_hvalue_as_type source (Gtyp ground)) as [adapted_right|] eqn:Radapt; try discriminate.
  have passive : is_passive_value adapted_right = true by (eapply adapt_ground_passive; exact Radapt).
  cbn [repl_val_part] in connected.
  rewrite (replace_source_passive _ _ passive) in connected.
  cbn [option_map] in connected. inversion connected; subst after.
  apply VM.Lemmas.find_add_eq. exact (eq_refl watched).
Qed.

Lemma one_statement_frames_ground invalid scope position old set_regs before after stmt watched ground value
  (frame : flat_statement_frames watched stmt = true)
  (ground_type : type_of_val value = Gtyp ground)
  (known : VM.find watched before = Some value)
  (ran : one_statement invalid scope position empty_memory_map old set_regs before stmt = Some after) :
  VM.find watched after = Some value.
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
    destruct expr as [t constant|cast body|op body|op a b|cond a b|cond body|rhs];
      try (eapply one_statement_nonref in ran; [|reflexivity]);
      try (rewrite (flat_ref_unidirectional _ _ _ _ _ _ flat) in ran;
        rewrite (unidirectional_bundle_preserves_other _ _ _ _ _ _ _ left_different ran); exact known).
    have connection := one_statement_ref _ _ _ _ _ _ _ _ _ flat ran.
    destruct rhs as [source|r field|r index|r expression].
    + destruct (N.eq_dec source watched) as [same|different_source].
      * subst source. eapply bidirectional_eid_ground_source_preserved; eassumption.
      * have right_different : watched <> HiF.base_ref (@Eid VarOrder.T source) by (simpl; congruence).
        rewrite (bidirectional_preserves_other empty_memory_map old before after lhs (@Eid VarOrder.T source) watched left_different right_different connection).
        exact known.
    + move/andP: source_frame => [_ different_source].
      rewrite (bidirectional_preserves_other _ _ _ _ _ _ _ left_different (different_id _ _ different_source) connection).
      exact known.
    + discriminate source_frame.
    + discriminate source_frame.
Qed.


Lemma flat_sequence_preserves_ground invalid scope old set_regs watched ground value stmts :
  type_of_val value = Gtyp ground ->
  forall position before after,
  flat_sequence_frames watched stmts = true ->
  VM.find watched before = Some value ->
  value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
  VM.find watched after = Some value.
Proof.
  intro ground_type. induction stmts as [|stmt rest IH]; intros position before after frame known ran.
  - inversion ran; subst; exact known.
  - move/andP: frame => [head_frame tail_frame].
    rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (frame_statement_flat _ _ head_frame)) in ran.
    destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
    eapply IH; [exact tail_frame| |exact ran].
    eapply one_statement_frames_ground; eassumption.
Qed.


Inductive framed_write_certificate (watched : VarOrder.T) (writer : @hfstmt VarOrder.T) :
 @hfstmt_seq VarOrder.T -> Prop :=
| framed_write_here : forall rest,
 flat_statement writer = true -> flat_sequence_frames watched rest = true ->
 framed_write_certificate watched writer (Qcons writer rest)
| framed_write_later : forall stmt rest,
 flat_statement_frames watched stmt = true -> framed_write_certificate watched writer rest ->
 framed_write_certificate watched writer (Qcons stmt rest).

Lemma framed_write_value invalid scope old set_regs watched writer ground initial_value result_ground bits stmts
 (certificate : framed_write_certificate watched writer stmts)
 (initial_type : type_of_val initial_value = Gtyp ground)
 (writes : forall position before after,
   VM.find watched before = Some initial_value ->
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   VM.find watched after = Some (Gval result_ground bits)) :
 forall position before after,
 VM.find watched before = Some initial_value ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 VM.find watched after = Some (Gval result_ground bits).
Proof.
 induction certificate as [rest flat framed|stmt rest framed certificate IH]; intros position before after known ran.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before writer) as [middle|] eqn:Head; try discriminate.
   eapply flat_sequence_preserves_known; [exact framed|eapply writes; eassumption|exact ran].
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (frame_statement_flat _ _ framed)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; [|exact ran]. eapply one_statement_frames_ground; eassumption.
Qed.

Lemma pass_framed_write_value invalid old before after stmts watched writer ground initial_value result_ground bits
 (certificate : framed_write_certificate watched writer stmts)
 (not_register : registers_frame watched stmts = true)
 (initial_type : type_of_val initial_value = Gtyp ground)
 (initial_lookup : VM.find watched before = Some initial_value)
 (writes : forall position initial final,
   VM.find watched initial = Some initial_value ->
   one_statement invalid [::] position empty_memory_map old false initial writer = Some final ->
   VM.find watched final = Some (Gval result_ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find watched after = Some (Gval result_ground bits).
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 eapply framed_write_value; eassumption.
Qed.

Lemma pass_preserves_ground invalid old before after stmts watched ground value
 (framed : flat_sequence_frames watched stmts = true)
 (not_register : registers_frame watched stmts = true)
 (ground_type : type_of_val value = Gtyp ground)
 (known : VM.find watched before = Some value)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find watched after = Some value.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 eapply flat_sequence_preserves_ground; eassumption.
Qed.
Print Assumptions pass_framed_write_value.
Print Assumptions pass_preserves_ground.
Fixpoint flat_register_sequence (stmts : @hfstmt_seq VarOrder.T) : bool :=
 match stmts with Qnil => true | Qcons stmt rest => flat_statement stmt && flat_register_sequence rest end.
Lemma finish_flat_preserves_old eval old watched value stmts
 (known_old : VM.find watched old = Some value)
 (flat : flat_register_sequence stmts = true) :
 forall before after, VM.find watched before = Some value ->
 finish_registers eval old false before stmts = Some after ->
 VM.find watched after = Some value.
Proof.
 induction stmts as [|stmt rest IH]; intros before after known ran.
 - inversion ran; subst; exact known.
 - move/andP: flat => [head tail].
   destruct stmt as [|id t|id reg|id mem|id modid|id expr|lhs expr|ref|cond yes no];
     cbn [flat_statement] in head; try discriminate;
     cbn [finish_registers] in ran; try (eapply IH; eassumption).
   destruct (VM.find id old) as [previous|] eqn:Previous; try discriminate.
   destruct (VM.find id before) as [proposed|] eqn:Proposed; try discriminate.
   eapply IH; [exact tail| |exact ran].
   destruct (N.eq_dec watched id) as [same|different].
   + subst id. rewrite known_old in Previous. inversion Previous; subst previous.
     apply VM.Lemmas.find_add_eq. exact (eq_refl watched).
   + rewrite VM.Lemmas.find_add_neq; [exact known|move/eqP=> E; exact (different E)].
Qed.
Inductive flat_register_certificate (watched : VarOrder.T) : @hfstmt_seq VarOrder.T -> Prop :=
| flat_register_here : forall reg rest,
 flat_register_sequence rest = true -> flat_register_certificate watched (Qcons (Sreg watched reg) rest)
| flat_register_later : forall stmt rest,
 flat_statement stmt = true -> flat_register_certificate watched rest ->
 flat_register_certificate watched (Qcons stmt rest).
Lemma finish_flat_register_value eval old watched value stmts
 (known : VM.find watched old = Some value)
 (certificate : flat_register_certificate watched stmts) :
 forall before after, finish_registers eval old false before stmts = Some after ->
 VM.find watched after = Some value.
Proof.
 induction certificate as [reg rest flat|stmt rest flat cert IH]; intros before after ran.
 - cbn [finish_registers] in ran. rewrite known in ran.
   destruct (VM.find watched before); try discriminate.
   eapply finish_flat_preserves_old; [exact known|exact flat| |exact ran].
   apply VM.Lemmas.find_add_eq. exact (eq_refl watched).
 - destruct stmt; cbn [flat_statement] in flat; try discriminate;
     cbn [finish_registers] in ran; try (eapply IH; exact ran).
   repeat match type of ran with
   | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
   end; try discriminate. eapply IH; exact ran.
Qed.
Lemma pass_register_preserved invalid old before after stmts watched value
 (known : VM.find watched old = Some value)
 (certificate : flat_register_certificate watched stmts)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find watched after = Some value.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts); try discriminate.
 eapply finish_flat_register_value; eassumption.
Qed.
Print Assumptions pass_register_preserved.
Lemma adapt_ground_type value ground result
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some result) :
 type_of_val result = Gtyp ground.
Proof.
 destruct value; destruct ground; simpl in adapted; try discriminate;
 repeat match type of adapted with
 | context [match ?x with _ => _ end] => destruct x eqn:?
 | context [if ?x then _ else _] => destruct x eqn:?
 end; inversion adapted; reflexivity.
Qed.
Lemma replace_sink_passive old value (passive : is_passive_value value = true) :
 replace_writeable Sink old value = Some value.
Proof. destruct value; cbn [replace_writeable]; rewrite ?passive; reflexivity. Qed.
Lemma bidirectional_eid_target_ground mm old before after target source ground value result
 (different : source != target)
 (target_type : eval_type_of_ref (@Eid VarOrder.T target) before = Some (Gtyp ground))
 (source_value : eval_href_with_memory mm (@Eid VarOrder.T source) old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some result)
 (ran : bidirectional_connect_with_memory mm (@Eid VarOrder.T target) (@Eid VarOrder.T source) old before = Some after) :
 VM.find target after = Some result /\ type_of_val result = Gtyp ground.
Proof.
 split; [|eapply adapt_ground_type; exact adapted].
 unfold bidirectional_connect_with_memory in ran.
 cbn [HiF.base_ref] in ran.
 destruct (VM.find target before) as [previous|] eqn:Previous; try discriminate.
 rewrite target_type source_value adapted in ran.
 cbn [repl_val_part] in ran.
 rewrite (replace_sink_passive previous result (adapt_ground_passive _ _ _ adapted)) in ran.
 cbn [option_map] in ran.
 repeat match type of ran with
 | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
 | context [option_map ?f ?x] => destruct x eqn:?; cbn [option_map] in ran
 end; try discriminate.
 inversion ran; subst. rewrite (find_add_other _ _ _ _ different).
 apply VM.Lemmas.find_add_eq. exact (eq_refl target).
Qed.

Lemma framed_write_ground_value invalid scope old set_regs watched writer ground initial_value result_ground result_value stmts
 (certificate : framed_write_certificate watched writer stmts)
 (result_type : type_of_val result_value = Gtyp result_ground)
 (initial_type : type_of_val initial_value = Gtyp ground)
 (writes : forall position before after,
   VM.find watched before = Some initial_value ->
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   VM.find watched after = Some result_value) :
 forall position before after,
 VM.find watched before = Some initial_value ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 VM.find watched after = Some result_value.
Proof.
 induction certificate as [rest flat framed|stmt rest framed certificate IH]; intros position before after known ran.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before writer) as [middle|] eqn:Head; try discriminate.
   eapply flat_sequence_preserves_ground; [exact result_type|exact framed|eapply writes; eassumption|exact ran].
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (frame_statement_flat _ _ framed)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; [|exact ran]. eapply one_statement_frames_ground; eassumption.
Qed.

Lemma pass_framed_write_ground_value invalid old before after stmts watched writer ground initial_value result_ground result_value
 (certificate : framed_write_certificate watched writer stmts)
 (not_register : registers_frame watched stmts = true)
 (result_type : type_of_val result_value = Gtyp result_ground)
 (initial_type : type_of_val initial_value = Gtyp ground)
 (initial_lookup : VM.find watched before = Some initial_value)
 (writes : forall position initial final,
   VM.find watched initial = Some initial_value ->
   one_statement invalid [::] position empty_memory_map old false initial writer = Some final ->
   VM.find watched final = Some result_value)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find watched after = Some result_value.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran).
 eapply framed_write_ground_value; eassumption.
Qed.

Lemma framed_write_ground_type invalid scope old set_regs watched writer ground stmts
 (certificate : framed_write_certificate watched writer stmts)
 (writes : forall position before after value,
   VM.find watched before = Some value -> type_of_val value = Gtyp ground ->
   one_statement invalid scope position empty_memory_map old set_regs before writer = Some after ->
   exists result, VM.find watched after = Some result /\ type_of_val result = Gtyp ground) :
 forall position before after value,
 VM.find watched before = Some value -> type_of_val value = Gtyp ground ->
 value_iter_statements_with_memory_policy invalid scope position empty_memory_map old set_regs before stmts = Some after ->
 exists result, VM.find watched after = Some result /\ type_of_val result = Gtyp ground.
Proof.
 induction certificate as [rest flat framed|stmt rest framed certificate IH]; intros position before after value known typed ran.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ flat) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before writer) as [middle|] eqn:Head; try discriminate.
   destruct (writes position before middle value known typed Head) as [result [found result_type]].
   exists result; split; [|exact result_type]. eapply flat_sequence_preserves_ground; eassumption.
 - rewrite (flat_statement_decompose _ _ _ _ _ _ _ _ _ (frame_statement_flat _ _ framed)) in ran.
   destruct (one_statement invalid scope position empty_memory_map old set_regs before stmt) as [middle|] eqn:Head; try discriminate.
   eapply IH; [|exact typed|exact ran]. eapply one_statement_frames_ground; eassumption.
Qed.
Lemma pass_framed_write_ground_type invalid old before after stmts watched writer ground value
 (certificate : framed_write_certificate watched writer stmts)
 (not_register : registers_frame watched stmts = true)
 (initial_type : type_of_val value = Gtyp ground)
 (initial_lookup : VM.find watched before = Some value)
 (writes : forall position initial final value,
   VM.find watched initial = Some value -> type_of_val value = Gtyp ground ->
   one_statement invalid [::] position empty_memory_map old false initial writer = Some final ->
   exists result, VM.find watched final = Some result /\ type_of_val result = Gtyp ground)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 exists result, VM.find watched after = Some result /\ type_of_val result = Gtyp ground.
Proof.
 unfold value_iter_with_memory_policy in ran.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 empty_memory_map old false before stmts) as [proposed|] eqn:Statements; try discriminate.
 destruct (framed_write_ground_type invalid [::] old false watched writer ground stmts certificate writes 0 before proposed value initial_lookup initial_type Statements) as [result [found typed]].
 exists result; split; [|exact typed].
 rewrite (finish_registers_preserves_other _ _ _ _ _ _ _ not_register ran). exact found.
Qed.
Print Assumptions pass_framed_write_ground_type.
Lemma bidirectional_eid_preserves_target_type mm old before after target source ground
 (different : source != target)
 (target_type : eval_type_of_ref (@Eid VarOrder.T target) before = Some (Gtyp ground))
 (ran : bidirectional_connect_with_memory mm (@Eid VarOrder.T target) (@Eid VarOrder.T source) old before = Some after) :
 exists result, VM.find target after = Some result /\ type_of_val result = Gtyp ground.
Proof.
 pose proof ran as run_original.
 unfold bidirectional_connect_with_memory in ran.
 cbn [HiF.base_ref] in ran.
 destruct (VM.find target before) as [previous|]; try discriminate.
 rewrite target_type in ran.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T source) old old) as [value|] eqn:Source; try discriminate.
 destruct (adapt_hvalue_as_type value (Gtyp ground)) as [result|] eqn:Adapt; try discriminate.
 exists result. eapply bidirectional_eid_target_ground; eassumption.
Qed.
Print Assumptions bidirectional_eid_preserves_target_type.
