From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model Stable StableFront FrontCheck Booth8.
Local Open Scope N_scope.
Transparent word_2 word_3.
Theorem stable_front_product invalid env a b
 (Ha : VM.find 2 env = Some (Gval (Fuint 8) (from_N 8 a)))
 (Hb : VM.find 3 env = Some (Gval (Fuint 8) (from_N 8 b)))
 (Habound : N.lt a 256) (Hbbound : N.lt b 256)
 (fixed : value_iter_with_memory_policy invalid empty_memory_map env false env generated_module_3_stmts_0 = Some env) :
 exists p0 p1 p2 p3 c,
 VM.find 71 env = Some (Gval (Fuint 12) p0) /\
 VM.find 107 env = Some (Gval (Fuint 13) p1) /\
 VM.find 144 env = Some (Gval (Fuint 13) p2) /\
 VM.find 180 env = Some (Gval (Fuint 12) p3) /\
 VM.find 198 env = Some (Gval (Fuint 2) c) /\
 Z.modulo (to_Zpos p0 + to_Zpos p1 +4*to_Zpos p2+16*to_Zpos p3+64*to_Zpos c) 65536 =
 Z.modulo (Z.mul (signed8 (Z.of_N a)) (signed8 (Z.of_N b))) 65536.
Proof.
 exists (word_71 (front_inputs a b)), (word_107 (front_inputs a b)),
 (word_144 (front_inputs a b)), (word_180 (front_inputs a b)), (word_198 (front_inputs a b)).
 repeat split.
 - exact (stable_word_71 (front_inputs a b) env invalid fixed Ha Hb).
 - exact (stable_word_107 (front_inputs a b) env invalid fixed Ha Hb).
 - exact (stable_word_144 (front_inputs a b) env invalid fixed Ha Hb).
 - exact (stable_word_180 (front_inputs a b) env invalid fixed Ha Hb).
 - exact (stable_word_198 (front_inputs a b) env invalid fixed Ha).
 - exact (ast_front_product (front_inputs a b) a b (Logic.eq_refl _) (Logic.eq_refl _) Habound Hbbound).
Qed.
Print Assumptions stable_front_product.
