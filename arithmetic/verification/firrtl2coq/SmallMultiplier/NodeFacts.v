From Coq Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Fixpoint node_expression (id : VarOrder.T) (stmts : hfstmt_seq VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Snode n e) rest => if n == id then Some e else node_expression id rest
 | Qcons _ rest => node_expression id rest end.
Definition top_node id := node_expression id generated_module_3_stmts_0.
Definition ref (id : VarOrder.T) : hfexpr VarOrder.T := Eref (Eid id).
Lemma sum_node_certificate : top_node 402 = Some (Eprim_binop Badd (ref 387) (ref 401)).
Proof. vm_compute. reflexivity. Qed.
Lemma truncate_node_certificate : top_node 403 = Some (Eprim_unop (Utail 1) (ref 402)).
Proof. vm_compute. reflexivity. Qed.
Lemma product_assert_certificate : top_node 412 = Some (Eprim_binop (Bcomp Beq) (ref 6) (ref 408)).
Proof. vm_compute. reflexivity. Qed.
Definition eval_top_node id env :=
 match top_node id with
 | Some e => eval_hfexpr_with_memory empty_memory_map e env env
 | None => None end.
Lemma final_add_eval env s c
 (Hs : VM.find 387 env = Some (Gval (Fuint 16) s))
 (Hc : VM.find 401 env = Some (Gval (Fuint 16) c)) :
 eval_top_node 402 env = Some (Gval (Fuint 17) (from_N 17 (to_N s + to_N c))).
Proof.
 unfold eval_top_node. rewrite sum_node_certificate.
 cbn [eval_hfexpr_with_memory eval_href_with_memory ref]. rewrite Hs Hc. reflexivity.
Qed.
Lemma final_truncate_eval env bs
 (H : VM.find 402 env = Some (Gval (Fuint 17) bs)) :
 eval_top_node 403 env = Some (Gval (Fuint 16) (take 16 bs)).
Proof.
 unfold eval_top_node. rewrite truncate_node_certificate.
 cbn [eval_hfexpr_with_memory eval_href_with_memory ref]. rewrite H. reflexivity.
Qed.
Lemma product_assert_eval env actual expected
 (Ha : VM.find 6 env = Some (Gval (Fuint 16) actual))
 (He : VM.find 408 env = Some (Gval (Fuint 16) expected))
 (Hvalue : to_N actual = to_N expected) :
 eval_top_node 412 env = Some (Gval (Fuint 1) [::true]).
Proof.
 unfold eval_top_node. rewrite product_assert_certificate.
 cbn [eval_hfexpr_with_memory eval_href_with_memory ref]. rewrite Ha He.
 change (Some (Gval (Fuint 1) [::to_N actual == to_N expected]) = Some (Gval (Fuint 1) [::true])).
 rewrite Hvalue eq_refl. reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma unsigned_from_N width value :
 to_Zpos (from_N width value) = Z.of_N value mod 2^Z.of_nat width.
Proof. rewrite to_Zpos_N to_N_from_N N2Z.inj_mod N2Z.inj_pow nat_N_Z. reflexivity. Qed.
Lemma final_add_value s c :
 to_Zpos (take 16 (from_N 17 (to_N s + to_N c))) =
 (to_Zpos s + to_Zpos c) mod 65536.
Proof.
 assert (Hlow : take 16 (from_N 17 (to_N s + to_N c)) = low 16 (from_N 17 (to_N s + to_N c))).
 { unfold low. rewrite size_from_N. reflexivity. }
 rewrite Hlow -to_Zpos_mod_pow2 unsigned_from_N N2Z.inj_add -!to_Zpos_N.
 change (((to_Zpos s + to_Zpos c) mod 131072) mod 65536 = (to_Zpos s + to_Zpos c) mod 65536).
 symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|exists 2; reflexivity].
Qed.
Print Assumptions final_add_value.
