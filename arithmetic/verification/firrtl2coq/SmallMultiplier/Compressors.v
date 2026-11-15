From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.

(* The definitions below execute the original generated module ASTs. No
   replacement truth-table model or combinational equations are assumed. *)
Definition input_bit (b : bool) := Gval (Fuint 1) [:: b].
Definition c22_inputs (a b reset : bool) : formal_inputs :=
 {| formal_external_inputs := VM.add 0 (Gval Fclock [:: true])
      (VM.add 1 (input_bit reset) (VM.add 2 (input_bit a)
       (VM.add 3 (input_bit b) (VM.empty hvalue))));
    formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition c32_inputs (a b c reset : bool) : formal_inputs :=
 {| formal_external_inputs := VM.add 4 (input_bit c)
      (formal_external_inputs (c22_inputs a b reset));
    formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition c53_inputs (a b c d e reset : bool) : formal_inputs :=
 {| formal_external_inputs := VM.add 6 (input_bit e) (VM.add 5 (input_bit d)
      (formal_external_inputs (c32_inputs a b c reset)));
    formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition compressor_node top inputs id :=
 match circuit_formal_cycle generated_modules top None inputs with
 | Some states => match SVM.find [::] states with
   | Some env => VM.find id env | None => None end
 | None => None end.

Theorem c22_assert_predicate a b reset :
 compressor_node 0 (c22_inputs a b reset) 15 = Some (input_bit true).
Proof. Time destruct a,b,reset; vm_compute; reflexivity. Time Qed.
Theorem c32_assert_predicate a b c reset :
 compressor_node 1 (c32_inputs a b c reset) 19 = Some (input_bit true).
Proof. Time destruct a,b,c,reset; vm_compute; reflexivity. Time Qed.
Theorem c53_assert_predicate a b c d e reset :
 compressor_node 2 (c53_inputs a b c d e reset) 34 = Some (input_bit true).
Proof. Time destruct a,b,c,d,e,reset; vm_compute; reflexivity. Time Qed.
Print Assumptions c22_assert_predicate.
Print Assumptions c32_assert_predicate.
Print Assumptions c53_assert_predicate.

Definition compressor_outputs top inputs ids :=
 match circuit_formal_cycle generated_modules top None inputs with
 | Some states => match SVM.find [::] states with
   | Some env => Some (map (fun id => VM.find id env) ids) | None => None end
 | None => None end.
Definition known_bits bs := Some (map (fun b => Some (input_bit b)) bs).
Definition fa_sum a b c := xorb (xorb a b) c.
Definition fa_carry a b c := orb (andb a b) (andb (xorb a b) c).
Theorem c22_outputs a b reset :
 compressor_outputs 0 (c22_inputs a b reset) [::4;5] = known_bits [::xorb a b;andb a b].
Proof. destruct a,b,reset; vm_compute; reflexivity. Qed.
Theorem c32_outputs a b c reset :
 compressor_outputs 1 (c32_inputs a b c reset) [::5;6] = known_bits [::fa_sum a b c;fa_carry a b c].
Proof. destruct a,b,c,reset; vm_compute; reflexivity. Qed.
Theorem c53_outputs a b c d e reset :
 compressor_outputs 2 (c53_inputs a b c d e reset) [::7;8;9] =
 known_bits [::fa_sum (fa_sum a b c) d e;fa_carry a b c;fa_carry (fa_sum a b c) d e].
Proof. destruct a,b,c,d,e,reset; vm_compute; reflexivity. Qed.
Print Assumptions c53_outputs.
