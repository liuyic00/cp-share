From Coq Require Import ZArith Lia List Bool Ring.
Import ListNotations.
Open Scope Z_scope.

(* Mathematical invariant of the four Booth rows of the 8-bit instance.
   This is a lemma library, not a replacement for the generated circuit AST. *)
Definition bit (b : bool) : Z := if b then 1 else 0.
Definition word9 x := x mod 512.
Definition signed8 x := if x <? 128 then x else x-256.
Definition signed9 x := if x <? 256 then x else x-512.
Definition digit w :=
 match w with 1|2 => 1 | 3 => 2 | 4 => -2 | 5|6 => -1 | _ => 0 end.
Definition correction w := match w with 4 => 2 | 5|6 => 1 | _ => 0 end.
Definition selected b w :=
 let p := word9 (signed8 b) in
 match w with
 | 1|2 => p | 3 => word9 (2*p)
 | 4 => word9 (2*(511-p)) | 5|6 => 511-p | _ => 0 end.
Definition row_correct b w :=
 Z.eqb (signed9 (selected b w) + correction w) (digit w * signed8 b).

Lemma row_table :
 forallb (fun b => forallb (fun w => row_correct (Z.of_nat b) (Z.of_nat w))
   (seq 0 8)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem selected_correct b w (Hb : 0 <= b < 256) (Hw : 0 <= w < 8) :
 signed9 (selected b w) + correction w = digit w * signed8 b.
Proof.
 pose proof row_table as H.
 apply forallb_forall with (x:=Z.to_nat b) in H.
 - apply forallb_forall with (x:=Z.to_nat w) in H.
   + unfold row_correct in H. rewrite !Z2Nat.id in H by lia. now apply Z.eqb_eq.
   + apply in_seq. lia.
 - apply in_seq. lia.
Qed.

Definition window previous even odd := bit previous + 2*bit even + 4*bit odd.
Lemma digit_window previous even odd :
 digit (window previous even odd) = bit previous + bit even - 2*bit odd.
Proof. destruct previous,even,odd; reflexivity. Qed.
Lemma window_bound previous even odd : 0 <= window previous even odd < 8.
Proof. destruct previous,even,odd; unfold window,bit; lia. Qed.
Definition unsigned8 a0 a1 a2 a3 a4 a5 a6 a7 :=
 bit a0 + 2*bit a1 + 4*bit a2 + 8*bit a3 +
 16*bit a4 + 32*bit a5 + 64*bit a6 + 128*bit a7.
Definition signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 :=
 unsigned8 a0 a1 a2 a3 a4 a5 a6 a7 - 256*bit a7.
Lemma recoding8 a0 a1 a2 a3 a4 a5 a6 a7 :
 digit (window false a0 a1) + 4*digit (window a1 a2 a3) +
 16*digit (window a3 a4 a5) + 64*digit (window a5 a6 a7) =
 signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7.
Proof. rewrite !digit_window. unfold signed_bits8,unsigned8. cbn [bit]. ring. Qed.

(* The constants and weights are exactly the four source Cat expressions.
   Using the signed row value removes the explicit sign-bit duplication. *)
Definition packed0 r := 2048 + signed9 r.
Definition packed_middle r previous := 6144 + 4*signed9 r + correction previous.
Definition packed_last r previous := 2048 + 4*signed9 r + correction previous.
Definition column_sum b w0 w1 w2 w3 :=
 packed0 (selected b w0) +
 packed_middle (selected b w1) w0 +
 4*packed_middle (selected b w2) w1 +
 16*packed_last (selected b w3) w2 + 64*correction w3.
Theorem column_sum_product b a0 a1 a2 a3 a4 a5 a6 a7
 (Hb : 0 <= b < 256) :
 column_sum b (window false a0 a1) (window a1 a2 a3)
   (window a3 a4 a5) (window a5 a6 a7) =
 65536 + signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 * signed8 b.
Proof.
 pose proof (selected_correct b (window false a0 a1) Hb (window_bound false a0 a1)) as H0.
 pose proof (selected_correct b (window a1 a2 a3) Hb (window_bound a1 a2 a3)) as H1.
 pose proof (selected_correct b (window a3 a4 a5) Hb (window_bound a3 a4 a5)) as H2.
 pose proof (selected_correct b (window a5 a6 a7) Hb (window_bound a5 a6 a7)) as H3.
 rewrite <- recoding8. unfold column_sum,packed0,packed_middle,packed_last. nia.
Qed.
Theorem column_sum_product_mod b a0 a1 a2 a3 a4 a5 a6 a7
 (Hb : 0 <= b < 256) :
 column_sum b (window false a0 a1) (window a1 a2 a3)
   (window a3 a4 a5) (window a5 a6 a7) mod 65536 =
 (signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 * signed8 b) mod 65536.
Proof. rewrite column_sum_product by exact Hb.
 rewrite Z.add_mod by lia. rewrite Z.mod_same by lia.
 rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.
Print Assumptions column_sum_product_mod.

Lemma selected_range_table :
 forallb (fun b => forallb (fun w =>
   Z.leb 0 (selected (Z.of_nat b) (Z.of_nat w)) &&
   Z.ltb (selected (Z.of_nat b) (Z.of_nat w)) 512)
   (seq 0 8)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma selected_range b w (Hb : 0 <= b < 256) (Hw : 0 <= w < 8) :
 0 <= selected b w < 512.
Proof.
 pose proof selected_range_table as H.
 apply forallb_forall with (x:=Z.to_nat b) in H; [|apply in_seq; lia].
 apply forallb_forall with (x:=Z.to_nat w) in H; [|apply in_seq; lia].
 rewrite !Z2Nat.id in H by lia. apply andb_true_iff in H.
 destruct H as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
Qed.
Lemma signed9_range r (H : 0 <= r < 512) : -256 <= signed9 r < 256.
Proof. unfold signed9. destruct (r <? 256) eqn:E;
 [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia. Qed.
Lemma correction_window_range p e o : 0 <= correction (window p e o) < 4.
Proof. destruct p,e,o; vm_compute; intuition discriminate. Qed.
Lemma packed0_range r (H : 0 <= r < 512) : 0 <= packed0 r < 4096.
Proof. pose proof (signed9_range r H); unfold packed0; lia. Qed.
Lemma packed_middle_range r p e o (H : 0 <= r < 512) :
 0 <= packed_middle r (window p e o) < 8192.
Proof. pose proof (signed9_range r H); pose proof (correction_window_range p e o).
 unfold packed_middle; lia. Qed.
Lemma packed_last_range r p e o (H : 0 <= r < 512) :
 0 <= packed_last r (window p e o) < 4096.
Proof. pose proof (signed9_range r H); pose proof (correction_window_range p e o).
 unfold packed_last; lia. Qed.
Definition sign9_bit r := r / 256.
Lemma signed9_bit_identity r (H : 0 <= r < 512) : signed9 r = r - 512 * sign9_bit r.
Proof.
 unfold signed9,sign9_bit. destruct (r <? 256) eqn:E.
 - apply Z.ltb_lt in E. rewrite Z.div_small by lia. lia.
 - apply Z.ltb_ge in E. replace (r/256) with 1 by (apply Z.div_unique with (r:=r-256); [left;lia|ring]). lia.
Qed.
Lemma packed0_cat r (H : 0 <= r < 512) :
 (1-sign9_bit r)*2048 + sign9_bit r*1024 + sign9_bit r*512 + r = packed0 r.
Proof. unfold packed0. rewrite signed9_bit_identity by exact H. ring. Qed.
Lemma packed_middle_cat r p (H : 0 <= r < 512) :
 4096 + (1-sign9_bit r)*2048 + r*4 + correction p = packed_middle r p.
Proof. unfold packed_middle. rewrite signed9_bit_identity by exact H. ring. Qed.
Lemma packed_last_cat r p (H : 0 <= r < 512) :
 (1-sign9_bit r)*2048 + r*4 + correction p = packed_last r p.
Proof. unfold packed_last. rewrite signed9_bit_identity by exact H. ring. Qed.
