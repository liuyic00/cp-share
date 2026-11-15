From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
From SmallMultiplier Require Import Compressors.
Local Open Scope N_scope.
Definition bit_weight (b:bool) : Z := if b then 1%Z else 0%Z.
Definition output_weight (weights:list Z) (values:option (list (option hvalue))) : option Z :=
 match values with Some vs =>
  List.fold_right (fun p rest => match p,rest with
  | (w,Some (Gval _ bs)),Some total => Some (w * to_Zpos bs + total)%Z
  | _,_=>None end) (Some 0%Z) (List.combine weights vs)
 | None=>None end.
Lemma c22_weight a b reset :
 output_weight [::1%Z;2%Z] (compressor_outputs 0 (c22_inputs a b reset) [::4;5]) =
 Some (bit_weight a + bit_weight b)%Z.
Proof. rewrite c22_outputs. destruct a,b; reflexivity. Qed.
Lemma c32_weight a b c reset :
 output_weight [::1%Z;2%Z] (compressor_outputs 1 (c32_inputs a b c reset) [::5;6]) =
 Some (bit_weight a + bit_weight b + bit_weight c)%Z.
Proof. rewrite c32_outputs. destruct a,b,c; reflexivity. Qed.
Lemma c53_weight a b c d e reset :
 output_weight [::1%Z;2%Z;2%Z] (compressor_outputs 2 (c53_inputs a b c d e reset) [::7;8;9]) =
 Some (bit_weight a + bit_weight b + bit_weight c + bit_weight d + bit_weight e)%Z.
Proof. rewrite c53_outputs. destruct a,b,c,d,e; reflexivity. Qed.
Print Assumptions c53_weight.
