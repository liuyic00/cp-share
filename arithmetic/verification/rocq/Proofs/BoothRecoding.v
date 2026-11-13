From Coq Require Import ZArith Lia List Bool Ring.
From Proofs Require Import Words.
Import ListNotations.
Open Scope Z_scope.

Module BoothRecoding.
Definition Pair := (bool * bool)%type.
Definition bit (b : bool) : Z := if b then 1 else 0.
Definition digit (previous : bool) (p : Pair) : Z :=
  bit previous + bit (fst p) - 2 * bit (snd p).
Fixpoint unsigned (ps : list Pair) : Z :=
  match ps with [] => 0 | p::rest => bit (fst p) + 2 * bit (snd p) + 4 * unsigned rest end.
Fixpoint top (previous : bool) (ps : list Pair) : bool :=
  match ps with [] => previous | p::rest => top (snd p) rest end.
Fixpoint recoded (previous : bool) (ps : list Pair) : Z :=
  match ps with [] => 0 | p::rest => digit previous p + 4 * recoded (snd p) rest end.

Theorem recoded_eq (ps : list Pair) (previous : bool) :
  recoded previous ps = unsigned ps + bit previous -
    4^(Z.of_nat (length ps)) * bit (top previous ps).
Proof.
  revert previous; induction ps as [|p ps IH]; intros previous.
  - change (0 = 0 + bit previous - 1 * bit previous); ring.
  - cbn [recoded unsigned top length]; rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    unfold digit; ring.
Qed.
Definition signed (ps : list Pair) : Z :=
  unsigned ps - 4^(Z.of_nat (length ps)) * bit (top false ps).
Theorem recoded_signed ps : recoded false ps = signed ps.
Proof. rewrite recoded_eq; unfold signed; cbn [bit]; ring. Qed.
Fixpoint partialProducts (b : Z) (previous : bool) (ps : list Pair) : Z :=
  match ps with [] => 0 | p::rest => digit previous p * b + 4 * partialProducts b (snd p) rest end.
Theorem partialProducts_eq b previous ps :
  partialProducts b previous ps = recoded previous ps * b.
Proof. revert previous; induction ps; intros; cbn [partialProducts recoded]; [ring|rewrite IHps; ring]. Qed.
Theorem signed_product b ps : partialProducts b false ps = signed ps * b.
Proof. rewrite partialProducts_eq, recoded_signed; reflexivity. Qed.
Theorem digit_table previous even odd :
  digit previous (even,odd) =
    if odd then (if even then (if previous then 0 else -1)
                 else (if previous then -1 else -2))
    else (if even then (if previous then 2 else 1)
          else (if previous then 1 else 0)).
Proof. destruct previous, even, odd; reflexivity. Qed.
Theorem sign_extend ps previous :
  recoded previous (ps ++ [(top previous ps,top previous ps)]) = recoded previous ps.
Proof.
  revert previous; induction ps as [|p ps IH]; intros previous.
  - destruct previous; reflexivity.
  - cbn [app recoded top]; rewrite IH; reflexivity.
Qed.

(* The same 66-bit ones-complement selector/correction used by Lean. *)
Definition row (b window : Z) : Z :=
  let b := word 66 b in let w := word 3 window in
  word 66 (if (Z.eqb w 1 || Z.eqb w 2)%bool then b
    else if Z.eqb w 3 then Z.shiftl b 1
    else if Z.eqb w 4 then Z.shiftl (Z.lnot b) 1
    else if (Z.eqb w 5 || Z.eqb w 6)%bool then Z.lnot b else 0).
Definition correction (window : Z) : Z :=
  let w := word 3 window in
  if Z.eqb w 4 then 2 else if (Z.eqb w 5 || Z.eqb w 6)%bool then 1 else 0.

Lemma word_add_l w x y (hw : 0 <= w) :
  word w (word w x + y) = word w (x + y).
Proof. unfold word; apply Z.add_mod_idemp_l. apply Z.pow_nonzero; lia. Qed.

Theorem corrected_row_digit b (previous even odd : bool) :
  let window := bit previous + 2 * bit even + 4 * bit odd in
  word 66 (row b window + correction window) =
  word 66 (word 66 b * digit previous (even,odd)).
Proof.
  destruct previous, even, odd;
  unfold digit, bit; cbn [fst snd];
  unfold row, correction; cbn zeta;
  word_constants; cbn beta iota zeta delta [orb]; word_constants;
  try rewrite word_add_l by lia;
  try rewrite Z.shiftl_mul_pow2 by lia;
  word_constants;
  try rewrite Z.mul_0_r; try rewrite Z.mul_1_r;
  try reflexivity;
  apply f_equal;
  pose proof (Z.add_lnot_diag (word 66 b)); lia.
Qed.

Print Assumptions signed_product.
Print Assumptions corrected_row_digit.
End BoothRecoding.
