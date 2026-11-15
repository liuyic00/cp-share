From Coq Require Import ZArith Lia Bool.
From SmallMultiplier Require Import Booth8 Compression8 CaptureWiring8.
Open Scope Z_scope.

Lemma weighted_registers_ext r s (H : forall n, r n = s n) :
 weighted_registers r = weighted_registers s.
Proof. unfold weighted_registers. repeat rewrite H. reflexivity. Qed.

(* These lemmas consume next-register equations obtained from the interpreter;
   they do not introduce a replacement step function or assume any assertion. *)
Theorem product_invariant_step
 (r rnext : nat -> Z) expected expectednext
 (valid validnext reset enable : bool)
 b a0 a1 a2 a3 a4 a5 a6 a7
 (Hb : 0 <= b < 256)
 (columns : forall n, rnext n = if enable then
    booth_registers b a0 a1 a2 a3 a4 a5 a6 a7 n else r n)
 (expected_update : expectednext = if enable then
    (signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 * signed8 b) mod 65536 else expected)
 (valid_update : validnext = andb (negb reset) (orb enable valid))
 (invariant : valid = true -> weighted_registers r mod 65536 = expected) :
 validnext = true -> weighted_registers rnext mod 65536 = expectednext.
Proof.
 intros Hvalid. destruct reset; [rewrite valid_update in Hvalid; discriminate|].
 destruct enable.
 - rewrite expected_update. rewrite (weighted_registers_ext rnext
     (booth_registers b a0 a1 a2 a3 a4 a5 a6 a7) columns).
   rewrite capture_weight_product by exact Hb.
   rewrite Z.add_mod by lia. rewrite Z.mod_same by lia.
   rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
 - rewrite expected_update. rewrite (weighted_registers_ext rnext r columns).
   apply invariant. rewrite valid_update in Hvalid. exact Hvalid.
Qed.

Theorem holding_assertion_step
 (r rnext : nat -> Z) previousnext output outputnext
 (holdnext reset valid enable : bool)
 (columns_hold : enable = false -> forall n, rnext n = r n)
 (current_output : output = weighted_registers r mod 65536)
 (next_output : outputnext = weighted_registers rnext mod 65536)
 (previous_update : previousnext = output)
 (hold_update : holdnext = andb (negb reset) (andb valid (negb enable))) :
 holdnext = true -> outputnext = previousnext.
Proof.
 intros Hhold. destruct enable; [rewrite hold_update, andb_false_r, andb_false_r in Hhold; discriminate|].
 rewrite previous_update,current_output,next_output.
 rewrite (weighted_registers_ext rnext r (columns_hold eq_refl)). reflexivity.
Qed.
Print Assumptions product_invariant_step.
Print Assumptions holding_assertion_step.
