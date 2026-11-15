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
Example settling_pass_updates_register :
  match value_iter_with_memory empty_memory_map initial false initial statements with
  | Some state => VM.find 0 state
  | None => None
  end = Some (Gval (Fuint 1) [:: true]).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions settling_pass_updates_register.

(* The two-register pipeline must still have r1=0 after its first edge.
   Upstream instead propagates the constant across both registers in one run step. *)
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
  [:: @Finput VarOrder.T 2 (Gtyp Fclock)] pipeline_stmts].
Definition pipeline_inputs (_ : nat) :=
  VM.add 3 (Gval (Fuint 1) [:: false])
    (VM.add 2 (Gval Fclock [:: true]) (VM.empty hvalue)).
Definition read_pipeline_second (k : nat) :=
  match circuit_run_from_reset pipeline_modules 0 pipeline_inputs k with
  | Some states => match SVM.find [::] states with
    | Some state => VM.find 1 state | None => None end
  | None => None end.
Example reset_pipeline_second_is_zero :
  read_pipeline_second 0 = Some (Gval (Fuint 1) [:: false]).
Proof. vm_compute. reflexivity. Qed.
Example one_step_collapses_pipeline :
  read_pipeline_second 1 = Some (Gval (Fuint 1) [:: true]).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions one_step_collapses_pipeline.
