From Coq Require Import ZArith NArith List Bool Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Stable Booth8 Congruence Memo.
From SmallMultiplier Require Export FrontTable.
Local Open Scope N_scope.
Opaque front_correct front_sum memo_front.
Theorem front_correct_bounded (a b : N) : N.lt a 256 -> N.lt b 256 ->
 front_correct a b = true.
Proof.
 intros Ha Hb.
 Time assert (Ia : List.In (N.to_nat a) (List.seq 0 256)) by (apply List.in_seq; lia).
 Time assert (Ib : List.In (N.to_nat b) (List.seq 0 256)) by (apply List.in_seq; lia).
 Time pose proof front_table_checked as H.
 Time unfold front_table in H.
 Time pose proof (proj1 (List.forallb_forall _ _) H (N.to_nat a) Ia) as Hrow.
 Time pose proof (proj1 (List.forallb_forall _ _) Hrow (N.to_nat b) Ib) as Hcell.
 Time now rewrite !N2Nat.id in Hcell.
Qed.
Print Assumptions front_correct_bounded.
Transparent front_correct front_sum.
Definition ast_front_sum v : Z :=
 (to_Zpos (word_71 v) + to_Zpos (word_107 v) + 4*to_Zpos (word_144 v) +
 16*to_Zpos (word_180 v) +64*to_Zpos (word_198 v))%Z.
Lemma front_sum_is_ast a b : front_sum a b = ast_front_sum (front_inputs a b).
Proof. unfold front_sum. rewrite memo_front_correct. reflexivity. Qed.
Theorem ast_front_product v (a b:N)
 (Ha : v 0 2 = from_N 8 a) (Hb : v 0 3 = from_N 8 b)
 (Habound : N.lt a 256) (Hbbound : N.lt b 256) :
 Z.modulo (ast_front_sum v) 65536 =
 Z.modulo (Z.mul (signed8 (Z.of_N a)) (signed8 (Z.of_N b))) 65536.
Proof.
 Time pose proof (front_correct_bounded a b Habound Hbbound) as H.
 unfold front_correct in H. apply Z.eqb_eq in H.
 rewrite front_sum_is_ast in H.
 assert (Hav : v 0 2 = front_inputs a b 0 2) by exact Ha.
 assert (Hbv : v 0 3 = front_inputs a b 0 3) by exact Hb.
 unfold ast_front_sum in *.
 rewrite (word_71_inputs v (front_inputs a b) Hav Hbv).
 rewrite (word_107_inputs v (front_inputs a b) Hav Hbv).
 rewrite (word_144_inputs v (front_inputs a b) Hav Hbv).
 rewrite (word_180_inputs v (front_inputs a b) Hav Hbv).
 rewrite (word_198_inputs v (front_inputs a b) Hav Hbv).
 exact H.
Qed.
Print Assumptions ast_front_product.
