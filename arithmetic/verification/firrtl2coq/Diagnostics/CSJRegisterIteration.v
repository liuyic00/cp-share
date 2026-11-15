From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Local Open Scope N_scope.

(* Regression witness against upstream 58759b5, not a hardware correctness proof.
   A combinational settling pass (set_regs=false) must preserve registers. *)
Definition initial : VM.t hvalue :=
  VM.add 0 (Gval (Fuint 1) [:: false]) (VM.empty hvalue).
Definition statements : @hfstmt_seq VarOrder.T :=
  @Qcons VarOrder.T (@Sreg VarOrder.T 0
    (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@NRst VarOrder.T)))
    (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 0)
      (@Econst VarOrder.T (Fuint 1) [:: true])) (@Qnil VarOrder.T)).
Example settling_pass_preserves_register :
  match value_iter_with_memory empty_memory_map initial false initial statements with
  | Some state => VM.find 0 state | None => None end
  = Some (Gval (Fuint 1) [:: false]).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions settling_pass_preserves_register.

Definition clock_expr : @hfexpr VarOrder.T := @Eref VarOrder.T (@Eid VarOrder.T 2).
Definition one : @hfexpr VarOrder.T := @Econst VarOrder.T (Fuint 1) [:: true].
Definition pipeline_reset : @rst VarOrder.T :=
  @Rst VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3))
    (@Econst VarOrder.T (Fuint 1) [:: false]).
Definition pipeline_stmts : @hfstmt_seq VarOrder.T :=
  @Qcons VarOrder.T (@Sreg VarOrder.T 0
    (@mk_freg VarOrder.T (Gtyp (Fuint 1)) clock_expr pipeline_reset))
  (@Qcons VarOrder.T (@Sreg VarOrder.T 1
    (@mk_freg VarOrder.T (Gtyp (Fuint 1)) clock_expr pipeline_reset))
  (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 0) one)
  (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1)
    (@Eref VarOrder.T (@Eid VarOrder.T 0))) (@Qnil VarOrder.T)))).
Definition pipeline_modules := [:: @FInmod VarOrder.T 0
  [:: @Finput VarOrder.T 2 (Gtyp Fclock);
     @Finput VarOrder.T 3 (Gtyp (Fuint 1))] pipeline_stmts].
Definition pipeline_inputs (_ : nat) :=
  VM.add 3 (Gval (Fuint 1) [:: false])
    (VM.add 2 (Gval Fclock [:: true]) (VM.empty hvalue)).
Definition pipeline_formal_inputs (n : nat) : formal_inputs :=
  {| formal_external_inputs := pipeline_inputs n;
     formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition read_pair (states : option (SVM.t (VM.t hvalue))) :=
  match states with
  | Some states => match SVM.find [::] states with
    | Some state => (VM.find 0 state, VM.find 1 state)
    | None => (None, None) end
  | None => (None, None) end.
Definition bit (b : bool) := Some (Gval (Fuint 1) [:: b]).
Definition concrete_pair (k : nat) :=
  read_pair (circuit_run_from_reset pipeline_modules 0 pipeline_inputs k).
Definition formal_pair (k : nat) :=
  read_pair (circuit_formal_run_from_reset pipeline_modules 0
    (fun _ _ _ => 0) pipeline_formal_inputs k).
Example concrete_pipeline :
  (concrete_pair 0, concrete_pair 1, concrete_pair 2) =
  ((bit false, bit false), (bit true, bit false), (bit true, bit true)).
Proof. vm_compute. reflexivity. Qed.
Example formal_pipeline :
  (formal_pair 0, formal_pair 1, formal_pair 2) =
  ((bit false, bit false), (bit true, bit false), (bit true, bit true)).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions concrete_pipeline.
Print Assumptions formal_pipeline.
