From Stdlib Require Import ZArith Lia Zmod.Bits.
Open Scope Z_scope.

(* Numeric views for proving properties of native bitvector circuits.
   These are proved library-operation facts, not model assumptions. *)
Module Unsigned.
Lemma add w (a b : bits w) :
  Zmod.unsigned (Zmod.add a b) =
    (Zmod.unsigned a + Zmod.unsigned b) mod 2^w.
Proof. apply bits.unsigned_add. Qed.
Lemma sub w (a b : bits w) :
  Zmod.unsigned (Zmod.sub a b) =
    (Zmod.unsigned a - Zmod.unsigned b) mod 2^w.
Proof. apply bits.unsigned_sub. Qed.
Lemma mul w (a b : bits w) :
  Zmod.unsigned (Zmod.mul a b) =
    (Zmod.unsigned a * Zmod.unsigned b) mod 2^w.
Proof. apply bits.unsigned_mul. Qed.
Lemma and_mod w (a b : bits w) :
  Zmod.unsigned (Zmod.and a b) =
    Z.land (Zmod.unsigned a) (Zmod.unsigned b) mod 2^w.
Proof.
  rewrite <- (bits.mod_to_Z (Zmod.and a b)) at 1.
  rewrite bits.unsigned_and; reflexivity.
Qed.
Lemma or_mod w (a b : bits w) :
  Zmod.unsigned (Zmod.or a b) =
    Z.lor (Zmod.unsigned a) (Zmod.unsigned b) mod 2^w.
Proof.
  rewrite <- (bits.mod_to_Z (Zmod.or a b)) at 1.
  rewrite bits.unsigned_or; reflexivity.
Qed.
Lemma xor_mod w (a b : bits w) :
  Zmod.unsigned (Zmod.xor a b) =
    Z.lxor (Zmod.unsigned a) (Zmod.unsigned b) mod 2^w.
Proof.
  rewrite <- (bits.mod_to_Z (Zmod.xor a b)) at 1.
  rewrite bits.unsigned_xor; reflexivity.
Qed.
Lemma slice start pastend w (a : bits w) (range : 0<=start<=pastend) :
  Zmod.unsigned (Zmod.slice start pastend a) =
    Z.shiftr (Zmod.unsigned a) start mod 2^(pastend-start).
Proof.
  rewrite bits.unsigned_slice by exact range.
  rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.
Lemma app_add n m (a : bits n) (b : bits m) (hn : 0<=n) (hm : 0<=m) :
 Zmod.unsigned (Zmod.app a b) = Zmod.unsigned a + Zmod.unsigned b * 2^n.
Proof.
 rewrite bits.unsigned_app by assumption.
 assert (H : Z.land (Zmod.unsigned a) (Z.shiftl (Zmod.unsigned b) n) = 0).
 { apply Z.bits_inj'; intros k hk.
   rewrite Z.land_spec, Z.bits_0.
   destruct (Z_lt_ge_dec k n).
   - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
   - destruct (Z.eq_dec (Zmod.unsigned a) 0) as [ha|ha].
     + rewrite ha, Z.bits_0; reflexivity.
     + rewrite Z.bits_above_log2; [reflexivity| |].
       * pose proof (bits.unsigned_range a hn); lia.
       * assert (Z.log2 (Zmod.unsigned a) < n).
         { apply Z.log2_lt_pow2; pose proof (bits.unsigned_range a hn); lia. }
         lia.
 }
 rewrite <- Z.lxor_lor by exact H.
 rewrite <- Z.add_nocarry_lxor by exact H.
 rewrite Z.shiftl_mul_pow2 by assumption; reflexivity.
Qed.
End Unsigned.
Print Assumptions Unsigned.and_mod.
Print Assumptions Unsigned.slice.
Print Assumptions Unsigned.app_add.
