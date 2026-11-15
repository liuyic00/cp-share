From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Definition scalar_type t := match t with
 | Gtyp (Fuint w) => (0%nat,w) | Gtyp (Fsint w) => (1%nat,w)
 | Gtyp Fclock => (2%nat,1%nat) | _ => (9%nat,0%nat) end.
Definition module_widths id :=
 match module_initial_map_with_memory generated_modules [::] id None (SVM.empty _) with
 | Some states => match SVM.find [::] states with
 | Some env => map (fun '(id,v) => (id,scalar_type (type_of_val v))) (VM.elements env)
 | None => [::] end | None => [::] end.
Eval vm_compute in module_widths 3.
