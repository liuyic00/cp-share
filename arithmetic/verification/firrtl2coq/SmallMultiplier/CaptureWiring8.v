From Coq Require Import ZArith Lia Ring.
From SmallMultiplier Require Import Booth8 Packing8 Compression8.
Open Scope Z_scope.
(* Actual register order from Low FIRRTL: each captured bit has the same
   packed-row source and index as the corresponding r / r_i connect. *)
Definition captured_register (p0 p1 p2 p3 corr : Z) (n : nat) :=
 match n with
 | 0%nat => extract_bit p0 0%nat
 | 1%nat => extract_bit p1 0%nat
 | 2%nat => extract_bit p0 1%nat
 | 3%nat => extract_bit p1 1%nat
 | 4%nat => extract_bit p0 2%nat
 | 5%nat => extract_bit p1 2%nat
 | 6%nat => extract_bit p2 0%nat
 | 7%nat => extract_bit p0 3%nat
 | 8%nat => extract_bit p1 3%nat
 | 9%nat => extract_bit p2 1%nat
 | 10%nat => extract_bit p0 4%nat
 | 11%nat => extract_bit p1 4%nat
 | 12%nat => extract_bit p2 2%nat
 | 13%nat => extract_bit p3 0%nat
 | 14%nat => extract_bit p0 5%nat
 | 15%nat => extract_bit p1 5%nat
 | 16%nat => extract_bit p2 3%nat
 | 17%nat => extract_bit p3 1%nat
 | 18%nat => extract_bit p0 6%nat
 | 19%nat => extract_bit p1 6%nat
 | 20%nat => extract_bit p2 4%nat
 | 21%nat => extract_bit p3 2%nat
 | 22%nat => extract_bit corr 0%nat
 | 23%nat => extract_bit p0 7%nat
 | 24%nat => extract_bit p1 7%nat
 | 25%nat => extract_bit p2 5%nat
 | 26%nat => extract_bit p3 3%nat
 | 27%nat => extract_bit corr 1%nat
 | 28%nat => extract_bit p0 8%nat
 | 29%nat => extract_bit p1 8%nat
 | 30%nat => extract_bit p2 6%nat
 | 31%nat => extract_bit p3 4%nat
 | 32%nat => extract_bit p0 9%nat
 | 33%nat => extract_bit p1 9%nat
 | 34%nat => extract_bit p2 7%nat
 | 35%nat => extract_bit p3 5%nat
 | 36%nat => extract_bit p0 10%nat
 | 37%nat => extract_bit p1 10%nat
 | 38%nat => extract_bit p2 8%nat
 | 39%nat => extract_bit p3 6%nat
 | 40%nat => extract_bit p0 11%nat
 | 41%nat => extract_bit p1 11%nat
 | 42%nat => extract_bit p2 9%nat
 | 43%nat => extract_bit p3 7%nat
 | 44%nat => extract_bit p1 12%nat
 | 45%nat => extract_bit p2 10%nat
 | 46%nat => extract_bit p3 8%nat
 | 47%nat => extract_bit p2 11%nat
 | 48%nat => extract_bit p3 9%nat
 | 49%nat => extract_bit p2 12%nat
 | 50%nat => extract_bit p3 10%nat
 | 51%nat => extract_bit p3 11%nat
 | _ => 0 end.
Lemma captured_weight p0 p1 p2 p3 corr :
 weighted_registers (captured_register p0 p1 p2 p3 corr) =
 packed_bits 12 p0 + packed_bits 13 p1 + 4*packed_bits 13 p2 +
 16*packed_bits 12 p3 + 64*packed_bits 2 corr.
Proof. unfold weighted_registers,captured_register. cbn [packed_bits].
 change (2^Z.of_nat 0) with 1.
 change (2^Z.of_nat 1) with 2.
 change (2^Z.of_nat 2) with 4.
 change (2^Z.of_nat 3) with 8.
 change (2^Z.of_nat 4) with 16.
 change (2^Z.of_nat 5) with 32.
 change (2^Z.of_nat 6) with 64.
 change (2^Z.of_nat 7) with 128.
 change (2^Z.of_nat 8) with 256.
 change (2^Z.of_nat 9) with 512.
 change (2^Z.of_nat 10) with 1024.
 change (2^Z.of_nat 11) with 2048.
 change (2^Z.of_nat 12) with 4096.
 ring. Qed.
Lemma captured_weight_exact p0 p1 p2 p3 corr
 (H0 : 0 <= p0 < 4096) (H1 : 0 <= p1 < 8192)
 (H2 : 0 <= p2 < 8192) (H3 : 0 <= p3 < 4096) (HC : 0 <= corr < 4) :
 weighted_registers (captured_register p0 p1 p2 p3 corr) =
 p0 + p1 + 4*p2 + 16*p3 + 64*corr.
Proof.
 rewrite captured_weight.
 rewrite (packed_bits_exact 12 p0 H0), (packed_bits_exact 13 p1 H1),
   (packed_bits_exact 13 p2 H2), (packed_bits_exact 12 p3 H3),
   (packed_bits_exact 2 corr HC). reflexivity.
Qed.
Definition booth_registers b a0 a1 a2 a3 a4 a5 a6 a7 :=
 let w0 := window false a0 a1 in let w1 := window a1 a2 a3 in
 let w2 := window a3 a4 a5 in let w3 := window a5 a6 a7 in
 captured_register (packed0 (selected b w0))
   (packed_middle (selected b w1) w0)
   (packed_middle (selected b w2) w1)
   (packed_last (selected b w3) w2) (correction w3).
Theorem capture_weight_product b a0 a1 a2 a3 a4 a5 a6 a7
 (Hb : 0 <= b < 256) :
 weighted_registers (booth_registers b a0 a1 a2 a3 a4 a5 a6 a7) =
 65536 + signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 * signed8 b.
Proof.
 unfold booth_registers. rewrite captured_weight_exact.
 - apply column_sum_product. exact Hb.
 - apply packed0_range. apply selected_range; [exact Hb|apply window_bound].
 - apply packed_middle_range. apply selected_range; [exact Hb|apply window_bound].
 - apply packed_middle_range. apply selected_range; [exact Hb|apply window_bound].
 - apply packed_last_range. apply selected_range; [exact Hb|apply window_bound].
 - apply correction_window_range.
Qed.
Theorem captured_tree_product b a0 a1 a2 a3 a4 a5 a6 a7 o
 (Hb : 0 <= b < 256)
 (HC : compressor_contracts (booth_registers b a0 a1 a2 a3 a4 a5 a6 a7) o) :
 output_rows o mod 65536 =
 (signed_bits8 a0 a1 a2 a3 a4 a5 a6 a7 * signed8 b) mod 65536.
Proof.
 rewrite (compression_mod _ _ HC), capture_weight_product by exact Hb.
 rewrite Z.add_mod by lia. rewrite Z.mod_same by lia.
 rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.
Print Assumptions captured_tree_product.
