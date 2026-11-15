From Coq Require Import ZArith Lia.
Open Scope Z_scope.
(* Exact scalar wiring of ArrayMulDataModule8, generated from the retained Low FIRRTL.
   The interpreter-to-contract bridge is a separate obligation. *)
Definition compressor_contracts (r : nat -> Z) (o : nat -> nat -> Z) : Prop :=
  ((r 0%nat) + (r 1%nat) = 1*(o 0%nat 0%nat) + 2*(o 0%nat 1%nat)) /\
  ((r 2%nat) + (r 3%nat) = 1*(o 1%nat 0%nat) + 2*(o 1%nat 1%nat)) /\
  ((r 4%nat) + (r 5%nat) + (r 6%nat) = 1*(o 2%nat 0%nat) + 2*(o 2%nat 1%nat)) /\
  ((r 7%nat) + (r 8%nat) + (r 9%nat) = 1*(o 3%nat 0%nat) + 2*(o 3%nat 1%nat)) /\
  ((r 10%nat) + (r 11%nat) + (r 12%nat) + (r 13%nat) + (0) = 1*(o 4%nat 0%nat) + 2*(o 4%nat 1%nat) + 2*(o 4%nat 2%nat)) /\
  ((r 14%nat) + (r 15%nat) + (r 16%nat) + (r 17%nat) + (o 4%nat 1%nat) = 1*(o 5%nat 0%nat) + 2*(o 5%nat 1%nat) + 2*(o 5%nat 2%nat)) /\
  ((r 18%nat) + (r 19%nat) + (r 20%nat) + (r 21%nat) + (o 5%nat 1%nat) = 1*(o 6%nat 0%nat) + 2*(o 6%nat 1%nat) + 2*(o 6%nat 2%nat)) /\
  ((r 23%nat) + (r 24%nat) + (r 25%nat) + (r 26%nat) + (o 6%nat 1%nat) = 1*(o 7%nat 0%nat) + 2*(o 7%nat 1%nat) + 2*(o 7%nat 2%nat)) /\
  ((r 28%nat) + (r 29%nat) + (r 30%nat) + (r 31%nat) + (o 7%nat 1%nat) = 1*(o 8%nat 0%nat) + 2*(o 8%nat 1%nat) + 2*(o 8%nat 2%nat)) /\
  ((r 32%nat) + (r 33%nat) + (r 34%nat) + (r 35%nat) + (o 8%nat 1%nat) = 1*(o 9%nat 0%nat) + 2*(o 9%nat 1%nat) + 2*(o 9%nat 2%nat)) /\
  ((r 36%nat) + (r 37%nat) + (r 38%nat) + (r 39%nat) + (o 9%nat 1%nat) = 1*(o 10%nat 0%nat) + 2*(o 10%nat 1%nat) + 2*(o 10%nat 2%nat)) /\
  ((r 40%nat) + (r 41%nat) + (r 42%nat) + (r 43%nat) + (o 10%nat 1%nat) = 1*(o 11%nat 0%nat) + 2*(o 11%nat 1%nat) + 2*(o 11%nat 2%nat)) /\
  ((r 44%nat) + (r 45%nat) + (r 46%nat) = 1*(o 12%nat 0%nat) + 2*(o 12%nat 1%nat)) /\
  ((r 47%nat) + (r 48%nat) = 1*(o 13%nat 0%nat) + 2*(o 13%nat 1%nat)) /\
  ((r 49%nat) + (r 50%nat) = 1*(o 14%nat 0%nat) + 2*(o 14%nat 1%nat)) /\
  ((o 1%nat 0%nat) + (o 0%nat 1%nat) = 1*(o 15%nat 0%nat) + 2*(o 15%nat 1%nat)) /\
  ((o 2%nat 0%nat) + (o 1%nat 1%nat) = 1*(o 16%nat 0%nat) + 2*(o 16%nat 1%nat)) /\
  ((o 3%nat 0%nat) + (o 2%nat 1%nat) = 1*(o 17%nat 0%nat) + 2*(o 17%nat 1%nat)) /\
  ((o 4%nat 0%nat) + (o 3%nat 1%nat) = 1*(o 18%nat 0%nat) + 2*(o 18%nat 1%nat)) /\
  ((o 5%nat 0%nat) + (o 4%nat 2%nat) = 1*(o 19%nat 0%nat) + 2*(o 19%nat 1%nat)) /\
  ((o 6%nat 0%nat) + (r 22%nat) + (o 5%nat 2%nat) = 1*(o 20%nat 0%nat) + 2*(o 20%nat 1%nat)) /\
  ((o 7%nat 0%nat) + (r 27%nat) + (o 6%nat 2%nat) = 1*(o 21%nat 0%nat) + 2*(o 21%nat 1%nat)) /\
  ((o 8%nat 0%nat) + (o 7%nat 2%nat) = 1*(o 22%nat 0%nat) + 2*(o 22%nat 1%nat)) /\
  ((o 9%nat 0%nat) + (o 8%nat 2%nat) = 1*(o 23%nat 0%nat) + 2*(o 23%nat 1%nat)) /\
  ((o 10%nat 0%nat) + (o 9%nat 2%nat) = 1*(o 24%nat 0%nat) + 2*(o 24%nat 1%nat)) /\
  ((o 11%nat 0%nat) + (o 10%nat 2%nat) = 1*(o 25%nat 0%nat) + 2*(o 25%nat 1%nat)) /\
  ((o 12%nat 0%nat) + (o 11%nat 1%nat) + (o 11%nat 2%nat) = 1*(o 26%nat 0%nat) + 2*(o 26%nat 1%nat)) /\
  ((o 13%nat 0%nat) + (o 12%nat 1%nat) = 1*(o 27%nat 0%nat) + 2*(o 27%nat 1%nat)) /\
  ((o 14%nat 0%nat) + (o 13%nat 1%nat) = 1*(o 28%nat 0%nat) + 2*(o 28%nat 1%nat)) /\
  ((r 51%nat) + (o 14%nat 1%nat) = 1*(o 29%nat 0%nat) + 2*(o 29%nat 1%nat)).
Definition weighted_registers (r : nat -> Z) := 1*(r 0%nat) + 1*(r 1%nat) + 2*(r 2%nat) + 2*(r 3%nat) + 4*(r 4%nat) + 4*(r 5%nat) + 4*(r 6%nat) + 8*(r 7%nat) + 8*(r 8%nat) + 8*(r 9%nat) + 16*(r 10%nat) + 16*(r 11%nat) + 16*(r 12%nat) + 16*(r 13%nat) + 32*(r 14%nat) + 32*(r 15%nat) + 32*(r 16%nat) + 32*(r 17%nat) + 64*(r 18%nat) + 64*(r 19%nat) + 64*(r 20%nat) + 64*(r 21%nat) + 64*(r 22%nat) + 128*(r 23%nat) + 128*(r 24%nat) + 128*(r 25%nat) + 128*(r 26%nat) + 128*(r 27%nat) + 256*(r 28%nat) + 256*(r 29%nat) + 256*(r 30%nat) + 256*(r 31%nat) + 512*(r 32%nat) + 512*(r 33%nat) + 512*(r 34%nat) + 512*(r 35%nat) + 1024*(r 36%nat) + 1024*(r 37%nat) + 1024*(r 38%nat) + 1024*(r 39%nat) + 2048*(r 40%nat) + 2048*(r 41%nat) + 2048*(r 42%nat) + 2048*(r 43%nat) + 4096*(r 44%nat) + 4096*(r 45%nat) + 4096*(r 46%nat) + 8192*(r 47%nat) + 8192*(r 48%nat) + 16384*(r 49%nat) + 16384*(r 50%nat) + 32768*(r 51%nat).
Definition output_rows (o : nat -> nat -> Z) := 1*(o 0%nat 0%nat) + 2*(o 15%nat 0%nat) + 4*(o 16%nat 0%nat) + 8*(o 17%nat 0%nat) + 16*(o 18%nat 0%nat) + 32*(o 19%nat 0%nat) + 64*(o 20%nat 0%nat) + 128*(o 21%nat 0%nat) + 256*(o 22%nat 0%nat) + 512*(o 23%nat 0%nat) + 1024*(o 24%nat 0%nat) + 2048*(o 25%nat 0%nat) + 4096*(o 26%nat 0%nat) + 8192*(o 27%nat 0%nat) + 16384*(o 28%nat 0%nat) + 32768*(o 29%nat 0%nat) + 4*(o 15%nat 1%nat) + 8*(o 16%nat 1%nat) + 16*(o 17%nat 1%nat) + 32*(o 18%nat 1%nat) + 64*(o 19%nat 1%nat) + 128*(o 20%nat 1%nat) + 256*(o 21%nat 1%nat) + 512*(o 22%nat 1%nat) + 1024*(o 23%nat 1%nat) + 2048*(o 24%nat 1%nat) + 4096*(o 25%nat 1%nat) + 8192*(o 26%nat 1%nat) + 16384*(o 27%nat 1%nat) + 32768*(o 28%nat 1%nat).
Definition overflow_carries (o : nat -> nat -> Z) := 1*(o 29%nat 1%nat).
Theorem compression_conserves r o (H : compressor_contracts r o) :
 weighted_registers r = output_rows o + 65536 * overflow_carries o.
Proof.
 unfold compressor_contracts in H. repeat match type of H with _ /\ _ => destruct H as [? H] end.
 unfold weighted_registers,output_rows,overflow_carries. lia.
Qed.
Theorem compression_mod r o (H : compressor_contracts r o) :
 output_rows o mod 65536 = weighted_registers r mod 65536.
Proof.
 rewrite (compression_conserves r o H).
 rewrite Z.add_mod, Z.mul_mod by lia.
 rewrite Z.mod_same, Z.mul_0_l, Z.mod_0_l, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Print Assumptions compression_mod.
