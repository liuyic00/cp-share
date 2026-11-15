From Coq Require Import Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.

(* Facts about the original interpreter, not an alternative circuit semantics. *)
Lemma formal_iterations_add modules top inputs n m states :
  circuit_formal_iterations modules top inputs (n + m)%coq_nat states =
  match circuit_formal_iterations modules top inputs n states with
  | Some middle => circuit_formal_iterations modules top inputs m middle
  | None => None
  end.
Proof.
  revert states. induction n as [|n IH]; intro states; simpl; [reflexivity|].
  destruct (circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
    modules top states false) as [next|]; [apply IH|reflexivity].
Qed.

Lemma formal_iterations_fixed modules top inputs states
  (fixed : circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
    modules top states false = Some states) n :
  circuit_formal_iterations modules top inputs n states = Some states.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [circuit_formal_iterations]. rewrite fixed. exact IH.
Qed.

Lemma formal_iterations_stable_suffix modules top inputs initial stable n count
  (reached : circuit_formal_iterations modules top inputs n initial = Some stable)
  (fixed : circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
    modules top stable false = Some stable)
  (bound : (n <= count)%coq_nat) :
  circuit_formal_iterations modules top inputs count initial = Some stable.
Proof.
  assert (E : Nat.add n (Nat.sub count n) = count).
  { rewrite Nat.add_comm. apply Nat.sub_add. exact bound. }
  rewrite <- E.
  rewrite formal_iterations_add reached. apply formal_iterations_fixed. exact fixed.
Qed.

Lemma formal_cycle_from_stable modules top previous inputs initial stable count n
  (initialized : circuit_initial_map_with_memory modules top previous
    (formal_external_inputs inputs) = Some initial)
  (iterations : circuit_iter_count_with_memory modules top Gtyp_connect_count = Some count)
  (reached : circuit_formal_iterations modules top inputs n initial = Some stable)
  (fixed : circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
    modules top stable false = Some stable)
  (bound : (n <= count)%coq_nat) :
  circuit_formal_cycle modules top previous inputs =
  circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
    modules top stable true.
Proof.
  unfold circuit_formal_cycle. rewrite initialized iterations.
  rewrite (formal_iterations_stable_suffix modules top inputs initial stable n count reached fixed bound).
  reflexivity.
Qed.

Print Assumptions formal_cycle_from_stable.
