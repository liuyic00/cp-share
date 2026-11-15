From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Definition multiplier_instances : SVM.t VarOrder.T := Eval vm_compute in
 match find_circuit_instances generated_modules generated_top with
 | Some instances => instances | None => SVM.empty VarOrder.T end.
Lemma multiplier_instances_correct : find_circuit_instances generated_modules generated_top = Some multiplier_instances.
Proof. vm_compute. reflexivity. Qed.
Definition multiplier_ports mid :=
 match find_module generated_modules mid with Some (FInmod _ ps _) => ps | _ => [::] end.
