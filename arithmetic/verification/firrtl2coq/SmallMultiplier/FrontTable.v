From Coq Require Import ZArith NArith List Bool Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Stable Booth8 Congruence Memo.
Local Open Scope N_scope.
Definition front_inputs (a b : N) : leaf_values := fun scope id =>
 if scope == 0 then if id == 2 then from_N 8 a else if id == 3 then from_N 8 b else [::] else [::].
Definition front_sum a b : Z :=
 let '(p0,p1,p2,p3,c) := memo_front (front_inputs a b) in
 (to_Zpos p0 + to_Zpos p1 + 4*to_Zpos p2 + 16*to_Zpos p3 +64*to_Zpos c)%Z.
Definition front_correct a b := Z.eqb ((front_sum a b) mod 65536)
 ((signed8 (Z.of_N a) * signed8 (Z.of_N b)) mod 65536).
Transparent word_2 word_3.
Time Eval vm_compute in front_correct 1 1.
Time Eval vm_compute in List.forallb (fun b=>front_correct 1 (N.of_nat b)) (List.seq 0 256).
Definition front_table := List.forallb (fun a=> List.forallb
 (fun b=>front_correct (N.of_nat a) (N.of_nat b)) (List.seq 0 256)) (List.seq 0 256).
Theorem front_table_checked : front_table = true.
Proof. Time vm_compute. reflexivity. Time Qed.
