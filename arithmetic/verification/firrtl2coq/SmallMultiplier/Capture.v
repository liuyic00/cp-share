From Coq Require Import ZArith btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Definition capture_inputs (a b : bits) : formal_inputs :=
 {| formal_external_inputs := VM.add 0 (Gval Fclock [::true])
  (VM.add 1 (Gval (Fuint 1) [::false])
  (VM.add 2 (Gval (Fuint 8) a)
  (VM.add 3 (Gval (Fuint 8) b)
  (VM.add 4 (Gval (Fuint 1) [::true])
  (VM.add 5 (Gval (Fuint 1) [::false]) (VM.empty _))))));
 formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition observe_cycle previous inputs :=
 match circuit_initial_map_with_memory generated_modules generated_top
   (Some previous) (formal_external_inputs inputs),
   circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count with
 | Some initial, Some n => circuit_formal_iterations generated_modules generated_top inputs n initial
 | _, _ => None end.
Definition captured_predicate a b :=
 match circuit_formal_cycle generated_modules generated_top None (capture_inputs a b) with
 | Some previous => match observe_cycle previous (capture_inputs a b) with
   | Some states => match SVM.find [::] states with
     | Some env => match VM.find 412 env with
       | Some (Gval (Fuint 1) [:: answer]) => answer | _ => false end
     | None => false end
   | None => false end
 | None => false end.
Example captured_one_one : captured_predicate (from_N 8 1) (from_N 8 1) = true.
Proof. Time vm_compute. reflexivity. Time Qed.
