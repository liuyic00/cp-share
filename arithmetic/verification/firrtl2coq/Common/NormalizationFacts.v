From Coq Require Import ZArith Znumtheory Lia.
From ArithmeticCommon Require Import BitvectorFacts.
Open Scope Z_scope.
Lemma modulus_divides outer inner (widths : (outer <= inner)%nat) :
 (modulus outer | modulus inner).
Proof.
 exists (modulus (inner - outer)).
 unfold modulus. rewrite <- Z.pow_add_r; [|lia|lia].
 f_equal. rewrite <- Nat2Z.inj_add. f_equal. lia.
Qed.
Lemma normalize_nested outer inner z (widths : (outer <= inner)%nat) :
 normalize outer (normalize inner z) = normalize outer z.
Proof.
 unfold normalize. symmetry. apply Zmod_div_mod; try apply modulus_positive. apply modulus_divides. exact widths.
Qed.
Print Assumptions normalize_nested.

Lemma normalize_add_congr width a a' b b'
 (left : normalize width a = normalize width a')
 (right : normalize width b = normalize width b') :
 normalize width (a+b) = normalize width (a'+b').
Proof.
 unfold normalize in *. assert (NZ : modulus width <> 0) by (pose proof (modulus_positive width); lia).
 rewrite (Z.add_mod a b _ NZ), (Z.add_mod a' b' _ NZ), left, right. reflexivity.
Qed.
Lemma normalize_sub_congr width a a' b b'
 (left : normalize width a = normalize width a')
 (right : normalize width b = normalize width b') :
 normalize width (a-b) = normalize width (a'-b').
Proof.
 unfold normalize in *. rewrite (Zminus_mod a b), (Zminus_mod a' b'), left, right. reflexivity.
Qed.
Lemma normalize_mul_congr width a a' b b'
 (left : normalize width a = normalize width a')
 (right : normalize width b = normalize width b') :
 normalize width (a*b) = normalize width (a'*b').
Proof.
 unfold normalize in *. assert (NZ : modulus width <> 0) by (pose proof (modulus_positive width); lia).
 rewrite (Z.mul_mod a b _ NZ), (Z.mul_mod a' b' _ NZ), left, right. reflexivity.
Qed.
Lemma normalize_add_nested outer inner a b (widths : (outer <= inner)%nat) :
 normalize outer (normalize inner a + b) = normalize outer (a+b).
Proof. apply normalize_add_congr; [apply normalize_nested; exact widths|reflexivity]. Qed.
Lemma normalize_sub_nested outer inner a b (widths : (outer <= inner)%nat) :
 normalize outer (normalize inner a - b) = normalize outer (a-b).
Proof. apply normalize_sub_congr; [apply normalize_nested; exact widths|reflexivity]. Qed.
Lemma normalize_mul_nested outer inner a b (widths : (outer <= inner)%nat) :
 normalize outer (normalize inner a * b) = normalize outer (a*b).
Proof. apply normalize_mul_congr; [apply normalize_nested; exact widths|reflexivity]. Qed.
Print Assumptions normalize_mul_nested.

Lemma normalize_shiftr_nested outer inner shift z
 (widths : (outer + shift <= inner)%nat) :
 normalize outer (Z.shiftr (normalize inner z) (Z.of_nat shift)) =
 normalize outer (Z.shiftr z (Z.of_nat shift)).
Proof.
 apply Z.bits_inj'. intros index nonnegative.
 unfold normalize, modulus.
 rewrite !Z.testbit_mod_pow2 by lia.
 destruct (index <? Z.of_nat outer) eqn:Inside; [|reflexivity].
 rewrite !Z.shiftr_spec by lia.
 rewrite Z.testbit_mod_pow2 by lia.
 assert (Bound : (index + Z.of_nat shift <? Z.of_nat inner) = true).
 { apply Z.ltb_lt. apply Z.ltb_lt in Inside. lia. }
 rewrite Bound. reflexivity.
Qed.
Print Assumptions normalize_shiftr_nested.
