From Coq Require Import Arith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import ScalarEvaluation ScalarExtensionality StatementFacts.

Definition rank_agrees (rank : VarOrder.T -> nat) (target : VM.t hvalue)
 (n : nat) (env : VM.t hvalue) : Prop :=
 forall id, (rank id <= n)%coq_nat -> VM.find id env = VM.find id target.

Lemma ranked_scalar_evaluation rank target n old expr
 (agree : rank_agrees rank target n old)
 (pure : scalar_exprb expr)
 (dependencies : forall id, List.In id (scalar_refs expr) -> (rank id <= n)%coq_nat) :
 eval_hfexpr_with_memory empty_memory_map expr old old = eval_hfexpr expr target target.
Proof.
 rewrite (scalar_eval_empty_memory expr old old pure).
 apply scalar_eval_extensional; [exact pure|].
 intros id occurs. apply agree. exact (dependencies id occurs).
Qed.

Lemma ranked_pass_node invalid rank target n old before after stmts id expr ground bits
 (agree : rank_agrees rank target n old)
 (pure : scalar_exprb expr)
 (dependencies : forall dep, List.In dep (scalar_refs expr) -> (rank dep < rank id)%coq_nat)
 (rank_bound : (rank id <= S n)%coq_nat)
 (certificate : node_certificate id expr stmts)
 (not_register : registers_frame id stmts = true)
 (evaluated : eval_hfexpr expr target target = Some (Gval ground bits))
 (target_value : VM.find id target = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find id after = VM.find id target.
Proof.
 rewrite target_value. eapply pass_node_value; [exact certificate|exact not_register| |exact ran].
 rewrite (ranked_scalar_evaluation rank target n old expr agree pure); [exact evaluated|].
 intros dep occurs. specialize (dependencies dep occurs). lia.
Qed.

(* This certificate is a local single-pass obligation. It permits both nodes
   and output connects; each is proved from its real interpreter statement. *)
Lemma rank_pass_progress rank target n old after
 (old_agrees : rank_agrees rank target n old)
 (leaves : forall id, rank id = O -> VM.find id after = VM.find id old)
 (nodes : forall id, (Nat.lt O (rank id) /\ Nat.le (rank id) (S n)) ->
    VM.find id after = VM.find id target) :
 rank_agrees rank target (S n) after.
Proof.
 intros id bound. destruct (rank id) eqn:R.
 - rewrite (leaves id R). apply old_agrees. rewrite R. lia.
 - apply nodes. split; lia.
Qed.

(* No fixed point or successful result is assumed. A concrete interpreter trace
   supplies the local progress facts above at every successful step. *)
Lemma rank_trace_convergence rank target (trace : nat -> VM.t hvalue)
 (initial : rank_agrees rank target O (trace O))
 (step : forall n, rank_agrees rank target n (trace n) ->
    rank_agrees rank target (S n) (trace (S n))) :
 forall n, rank_agrees rank target n (trace n).
Proof. intro n. induction n; [exact initial|apply step; exact IHn]. Qed.

Lemma rank_agrees_complete rank target n env
 (agree : rank_agrees rank target n env)
 (bounded : forall id, (rank id <= n)%coq_nat) :
 forall id, VM.find id env = VM.find id target.
Proof. intro id. apply agree. apply bounded. Qed.
Print Assumptions ranked_pass_node.
Print Assumptions rank_trace_convergence.

Lemma formal_iterations_rank_progress modules top inputs
 (P : nat -> SVM.t (VM.t hvalue) -> Prop)
 (step : forall n before after, P n before ->
   circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
     modules top before false = Some after -> P (S n) after) :
 forall count offset before after, P offset before ->
 circuit_formal_iterations modules top inputs count before = Some after ->
 P (Nat.add count offset) after.
Proof.
 induction count as [|count IH]; intros offset before after holds ran.
 - inversion ran; subst. exact holds.
 - cbn [circuit_formal_iterations] in ran.
   destruct (circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
     modules top before false) as [middle|] eqn:one; try discriminate.
   have next : P (S offset) middle by (eapply step; eassumption).
   have final := IH (S offset) middle after next ran.
   rewrite Nat.add_succ_r in final. exact final.
Qed.
Print Assumptions formal_iterations_rank_progress.

Definition rank_agrees_on (domain : VarOrder.T -> Prop) (rank : VarOrder.T -> nat)
 (target : VM.t hvalue) (n : nat) (env : VM.t hvalue) : Prop :=
 forall id, domain id -> Nat.le (rank id) n -> VM.find id env = VM.find id target.
Lemma ranked_scalar_evaluation_on domain rank target n old expr
 (agree : rank_agrees_on domain rank target n old)
 (pure : scalar_exprb expr)
 (dependencies : forall id, List.In id (scalar_refs expr) -> domain id /\ Nat.le (rank id) n) :
 eval_hfexpr_with_memory empty_memory_map expr old old = eval_hfexpr expr target target.
Proof.
 rewrite (scalar_eval_empty_memory expr old old pure).
 apply scalar_eval_extensional; [exact pure|].
 intros id occurs. destruct (dependencies id occurs) as [inside bound].
 exact (agree id inside bound).
Qed.
Lemma ranked_pass_node_on invalid domain rank target n old before after stmts id expr ground bits
 (agree : rank_agrees_on domain rank target n old)
 (pure : scalar_exprb expr)
 (dependencies : forall dep, List.In dep (scalar_refs expr) -> domain dep /\ Nat.lt (rank dep) (rank id))
 (rank_bound : Nat.le (rank id) (S n))
 (certificate : node_certificate id expr stmts)
 (not_register : registers_frame id stmts = true)
 (evaluated : eval_hfexpr expr target target = Some (Gval ground bits))
 (target_value : VM.find id target = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find id after = VM.find id target.
Proof.
 rewrite target_value. eapply pass_node_value; [exact certificate|exact not_register| |exact ran].
 rewrite (ranked_scalar_evaluation_on domain rank target n old expr agree pure); [exact evaluated|].
 intros dep occurs. destruct (dependencies dep occurs) as [inside smaller]. split; [exact inside|lia].
Qed.
Lemma rank_pass_progress_on domain rank target n old after
 (old_agrees : rank_agrees_on domain rank target n old)
 (leaves : forall id, domain id -> rank id = O -> VM.find id after = VM.find id old)
 (nodes : forall id, domain id -> (Nat.lt O (rank id) /\ Nat.le (rank id) (S n)) ->
    VM.find id after = VM.find id target) :
 rank_agrees_on domain rank target (S n) after.
Proof.
 intros id inside bound. destruct (rank id) eqn:R.
 - rewrite (leaves id inside R). apply old_agrees; [exact inside|rewrite R; lia].
 - apply nodes; [exact inside|split; lia].
Qed.
