From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Open Scope Z_scope.

(* Integer views of the existing NBits operations; no circuit is replaced. *)
Definition modulus (width : nat) := 2 ^ Z.of_nat width.
Definition normalize (width : nat) (z : Z) := z mod modulus width.
Definition encode (width : nat) (z : Z) := from_Zpos width (normalize width z).

Lemma modulus_positive width : 0 < modulus width.
Proof. unfold modulus. apply Z.pow_pos_nonneg; lia. Qed.
Lemma normalize_range width z : 0 <= normalize width z < modulus width.
Proof. apply Z.mod_pos_bound. apply modulus_positive. Qed.
Lemma decode_encode width z : to_Zpos (encode width z) = normalize width z.
Proof.
  unfold encode. rewrite to_Zpos_from_Zpos; last by apply (proj1 (normalize_range width z)).
  unfold normalize, modulus. apply Z.mod_mod. pose proof (modulus_positive width). unfold modulus in H. lia.
Qed.
Lemma encode_size width z : size (encode width z) = width.
Proof. unfold encode. apply size_from_Zpos. Qed.
Lemma unsigned_normalized width bits (sized : size bits = width) :
  normalize width (to_Zpos bits) = to_Zpos bits.
Proof.
  apply Z.mod_small. split; [apply to_Zpos_ge0|].
  unfold modulus. rewrite <- sized. apply to_Zpos_bounded.
Qed.
Lemma unsigned_add width a b (sa : size a = width) (sb : size b = width) :
  to_Zpos (addB a b) = normalize width (to_Zpos a + to_Zpos b).
Proof. rewrite to_Zpos_addB'; [by rewrite /normalize /modulus sa|by rewrite sa sb]. Qed.
Lemma unsigned_sub width a b (sa : size a = width) (sb : size b = width) :
  to_Zpos (subB a b) = normalize width (to_Zpos a - to_Zpos b).
Proof. rewrite to_Zpos_subB'; [by rewrite /normalize /modulus sa|by rewrite sa sb]. Qed.
Lemma unsigned_mul width a b (sa : size a = width) :
  to_Zpos (mulB a b) = normalize width (to_Zpos a * to_Zpos b).
Proof. rewrite to_Zpos_mulB'. by rewrite /normalize /modulus sa. Qed.
Lemma unsigned_low width bits : to_Zpos (low width bits) = normalize width (to_Zpos bits).
Proof. symmetry. apply to_Zpos_mod_pow2. Qed.
Lemma unsigned_cat lo hi :
  to_Zpos (lo ++ hi) = to_Zpos lo + to_Zpos hi * modulus (size lo).
Proof. apply to_Zpos_cat. Qed.
Lemma unsigned_lt a b : ltB a b = (to_Zpos a <? to_Zpos b).
Proof. apply to_Zpos_ltB_eqn. Qed.
Lemma unsigned_le a b (sized : size a = size b) : leB a b = (to_Zpos a <=? to_Zpos b).
Proof. apply to_Zpos_leB_eqn. exact sized. Qed.

Print Assumptions decode_encode.
Print Assumptions unsigned_add.

Lemma unsigned_testbit bits index :
  Z.testbit (to_Zpos bits) (Z.of_nat index) = nth false bits index.
Proof.
  revert index. induction bits as [|bit rest IH]; intro index.
  - rewrite /to_Zpos /= Z.testbit_0_l. destruct index; reflexivity.
  - change (Z.testbit (Z.b2z bit + to_Zpos rest * 2) (Z.of_nat index) = nth false (bit :: rest) index).
    replace (Z.b2z bit + to_Zpos rest * 2) with (2 * to_Zpos rest + Z.b2z bit) by ring.
    destruct index as [|index].
    + apply Z.testbit_0_r.
    + rewrite Nat2Z.inj_succ Z.testbit_succ_r; [apply IH|apply Nat2Z.is_nonneg].
Qed.

Lemma nth_lift0_equal (f : bool -> bool -> bool) a b index
  (zero : f false false = false) (sized : size a = size b) :
  nth false (lift0 f a b) index = f (nth false a index) (nth false b index).
Proof.
  revert b index sized. induction a as [|x xs IH]; intros b index sized;
    destruct b as [|y ys]; try discriminate.
  - destruct index; simpl; symmetry; exact zero.
  - rewrite /lift0 lift_cons. destruct index as [|index]; [reflexivity|].
    change (nth false (lift0 f xs ys) index = f (nth false xs index) (nth false ys index)).
    apply IH. injection sized; trivial.
Qed.

Lemma unsigned_lift0 (f : bool -> bool -> bool) (g : Z -> Z -> Z)
  (zero : f false false = false)
  (spec : forall a b i, Z.testbit (g a b) i = f (Z.testbit a i) (Z.testbit b i))
  a b (sized : size a = size b) :
  to_Zpos (lift0 f a b) = g (to_Zpos a) (to_Zpos b).
Proof.
  apply Z.bits_inj'. intros index nonnegative.
  rewrite spec.
  replace index with (Z.of_nat (Z.to_nat index)) by (apply Z2Nat.id; exact nonnegative).
  rewrite !unsigned_testbit. apply nth_lift0_equal; assumption.
Qed.
Lemma unsigned_and a b (sized : size a = size b) :
  to_Zpos (andB a b) = Z.land (to_Zpos a) (to_Zpos b).
Proof. apply unsigned_lift0; [reflexivity|exact Z.land_spec|exact sized]. Qed.
Lemma unsigned_or a b (sized : size a = size b) :
  to_Zpos (orB a b) = Z.lor (to_Zpos a) (to_Zpos b).
Proof. apply unsigned_lift0; [reflexivity|exact Z.lor_spec|exact sized]. Qed.
Lemma unsigned_xor a b (sized : size a = size b) :
  to_Zpos (xorB a b) = Z.lxor (to_Zpos a) (to_Zpos b).
Proof. apply unsigned_lift0; [reflexivity|exact Z.lxor_spec|exact sized]. Qed.
Print Assumptions unsigned_and.

Lemma unsigned_take count bits :
  to_Zpos (take count bits) = normalize count (to_Zpos bits).
Proof.
  rewrite <- unsigned_low. rewrite /low to_Zpos_cat to_Zpos_zeros.
  ring.
Qed.
Lemma unsigned_zero_extend count bits : to_Zpos (zext count bits) = to_Zpos bits.
Proof. apply to_Zpos_zext. Qed.
Lemma unsigned_shift_left count bits :
  to_Zpos (zeros count ++ bits) = Z.shiftl (to_Zpos bits) (Z.of_nat count).
Proof.
  rewrite to_Zpos_cat to_Zpos_zeros size_zeros Z.add_0_l.
  symmetry. apply Z.shiftl_mul_pow2. apply Nat2Z.is_nonneg.
Qed.
Lemma unsigned_shift_right count bits :
  to_Zpos (shrB count bits) = Z.shiftr (to_Zpos bits) (Z.of_nat count).
Proof.
  rewrite to_Zpos_shrB. symmetry. apply Z.shiftr_div_pow2. apply Nat2Z.is_nonneg.
Qed.
Print Assumptions unsigned_take.

Lemma unsigned_from_N width value :
  to_Zpos (from_N width value) = normalize width (Z.of_N value).
Proof.
  rewrite to_Zpos_N to_N_from_N N2Z.inj_mod N2Z.inj_pow.
  by rewrite /normalize /modulus nat_N_Z.
Qed.
Lemma unsigned_from_N_add width a b :
  to_Zpos (from_N width (N.add (to_N a) (to_N b))) = normalize width (to_Zpos a + to_Zpos b).
Proof. rewrite unsigned_from_N N2Z.inj_add -!to_Zpos_N. reflexivity. Qed.
Lemma unsigned_from_N_mul width a b :
  to_Zpos (from_N width (N.mul (to_N a) (to_N b))) = normalize width (to_Zpos a * to_Zpos b).
Proof. rewrite unsigned_from_N N2Z.inj_mul -!to_Zpos_N. reflexivity. Qed.
Print Assumptions unsigned_from_N.

Lemma nth_from_Zpos width value index :
  nth false (from_Zpos width value) index =
  if Nat.ltb index width then Z.testbit value (Z.of_nat index) else false.
Proof.
  revert value index. induction width as [|width IH]; intros value index.
  - destruct index; reflexivity.
  - destruct index as [|index].
    + change (Z.odd value = Z.testbit value 0). symmetry. apply Z.bit0_odd.
    + change (nth false (from_Zpos width (Z.div2 value)) index =
        if Nat.ltb index width then Z.testbit value (Z.of_nat (S index)) else false).
      rewrite IH. destruct (Nat.ltb index width); [|reflexivity].
      rewrite Nat2Z.inj_succ Z.div2_div Z.div2_bits; [reflexivity|apply Nat2Z.is_nonneg].
Qed.

Lemma nth_from_Zneg width value index :
  nth false (from_Zneg width value) index =
  if Nat.ltb index width then negb (Z.testbit value (Z.of_nat index)) else false.
Proof.
  revert value index. induction width as [|width IH]; intros value index.
  - destruct index; reflexivity.
  - destruct index as [|index].
    + change (Z.even value = negb (Z.testbit value 0)). rewrite Z.bit0_odd Z.negb_odd. reflexivity.
    + change (nth false (from_Zneg width (Z.div2 value)) index =
        if Nat.ltb index width then negb (Z.testbit value (Z.of_nat (S index))) else false).
      rewrite IH. destruct (Nat.ltb index width); [|reflexivity].
      rewrite Nat2Z.inj_succ Z.div2_div Z.div2_bits; [reflexivity|apply Nat2Z.is_nonneg].
Qed.

Lemma nat_Z_ltb a b : Nat.ltb a b = (Z.of_nat a <? Z.of_nat b).
Proof.
  destruct (Nat.ltb a b) eqn:E.
  - apply Nat.ltb_lt in E. symmetry. apply Z.ltb_lt. lia.
  - apply Nat.ltb_ge in E. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma unsigned_from_Zpos_all width value :
  to_Zpos (from_Zpos width value) = normalize width value.
Proof.
  apply Z.bits_inj'. intros index nonnegative.
  replace index with (Z.of_nat (Z.to_nat index)) by (apply Z2Nat.id; exact nonnegative).
  rewrite unsigned_testbit nth_from_Zpos /normalize /modulus Z.testbit_mod_pow2; last apply Nat2Z.is_nonneg.
  rewrite nat_Z_ltb. destruct (Z.of_nat (Z.to_nat index) <? Z.of_nat width); reflexivity.
Qed.
Lemma unsigned_from_Zneg width value :
  to_Zpos (from_Zneg width value) = normalize width (Z.lnot value).
Proof.
  apply Z.bits_inj'. intros index nonnegative.
  replace index with (Z.of_nat (Z.to_nat index)) by (apply Z2Nat.id; exact nonnegative).
  rewrite unsigned_testbit nth_from_Zneg /normalize /modulus Z.testbit_mod_pow2; last apply Nat2Z.is_nonneg.
  rewrite Z.lnot_spec; last apply Nat2Z.is_nonneg.
  rewrite nat_Z_ltb. destruct (Z.of_nat (Z.to_nat index) <? Z.of_nat width); reflexivity.
Qed.
Lemma unsigned_from_Z width value :
  to_Zpos (from_Z width value) = normalize width value.
Proof.
  destruct value as [|value|value].
  - rewrite /from_Z to_Zpos_zeros /normalize Z.mod_0_l; [reflexivity|pose proof (modulus_positive width); lia].
  - apply unsigned_from_Zpos_all.
  - rewrite /from_Z unsigned_from_Zneg.
    change (normalize width (Z.pred (- Z.pred (Z.pos value))) = normalize width (Z.neg value)).
    f_equal. lia.
Qed.
Print Assumptions unsigned_from_Z.

Lemma unsigned_drop count bits :
  to_Zpos (drop count bits) = Z.shiftr (to_Zpos bits) (Z.of_nat count).
Proof.
  apply Z.bits_inj'. intros index nonnegative.
  rewrite Z.shiftr_spec; last exact nonnegative.
  replace index with (Z.of_nat (Z.to_nat index)) by (apply Z2Nat.id; exact nonnegative).
  rewrite -Nat2Z.inj_add !unsigned_testbit nth_drop.
  rewrite addnC. reflexivity.
Qed.
Print Assumptions unsigned_drop.
