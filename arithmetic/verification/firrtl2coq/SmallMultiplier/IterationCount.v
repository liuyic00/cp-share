From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Definition iteration_bound :=
 circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count.
Eval vm_compute in iteration_bound.
Lemma iteration_bound_above_dependency_rank :
 match iteration_bound with Some n => is_true (56 <= n) | None => False end.
Proof. vm_compute. reflexivity. Qed.
