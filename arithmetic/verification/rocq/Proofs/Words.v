From Coq Require Import ZArith Lia.
Open Scope Z_scope.
Definition word (w x : Z) := x mod 2^w.
Lemma word_bound w x (h : 0 <= w) : 0 <= word w x < 2^w.
Proof. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
Lemma word_idem w x (h : 0 <= w) : word w (word w x) = word w x.
Proof. unfold word; apply Z.mod_mod. apply Z.pow_nonzero; lia. Qed.
Lemma word_small w x (h : 0 <= x < 2^w) : word w x = x.
Proof. apply Z.mod_small; exact h. Qed.
Lemma word_widen w v x (hw : 0 <= w) (hv : w <= v) :
  word v (word w x) = word w x.
Proof.
  apply word_small. pose proof (word_bound w x hw).
  assert (2^w <= 2^v) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma bit_cases x : word 1 x = 0 \/ word 1 x = 1.
Proof. pose proof (word_bound 1 x ltac:(lia)); cbn in H; lia. Qed.

Ltac positive_literal p :=
  lazymatch p with xH => idtac | xO ?q => positive_literal q | xI ?q => positive_literal q end.
Ltac integer_literal z :=
  lazymatch z with Z0 => idtac | Zpos ?p => positive_literal p | Zneg ?p => positive_literal p end.
(* Evaluate only closed arithmetic; keep symbolic word operations intact. *)
Ltac word_constants :=
  repeat match goal with
  | |- context[?f ?a ?b] =>
    first [constr_eq f Z.eqb | constr_eq f Z.ltb | constr_eq f Z.leb |
           constr_eq f Z.land | constr_eq f Z.lor | constr_eq f Z.lxor |
           constr_eq f Z.add | constr_eq f Z.mul | constr_eq f Z.shiftl |
           constr_eq f Z.shiftr | constr_eq f Z.sub | constr_eq f word];
    integer_literal a; integer_literal b;
    let v := eval vm_compute in (f a b) in change (f a b) with v
  end.
