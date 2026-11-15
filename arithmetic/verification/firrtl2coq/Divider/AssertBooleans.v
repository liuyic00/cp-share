From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticFIRRTL Require Import Radix2Divider.
From Divider Require Import Model Stable Frames Representation Typing AssertTransfer.
Local Open Scope N_scope.
Lemma one_bit_as_bool (bits : seq bool) (sized : size bits = 1%nat) : exists bit, bits = [::bit].
Proof. destruct bits as [|bit tail]; [discriminate|]. destruct tail; [exists bit; reflexivity|discriminate]. Qed.
Lemma generated_reference_truth env id bits
 (found : VM.find id env = Some (Gval (Fuint 1) bits)) (sized : size bits = 1%nat) :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T id)) env <-> to_Zpos bits = 1%Z.
Proof.
 destruct (one_bit_as_bool bits sized) as [bit E]. subst bits.
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href]. rewrite found.
 destruct bit; vm_compute; split; intro H; try discriminate; reflexivity.
Qed.
Lemma assertion_0_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 421)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_421 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_421_value _)|apply encoded_word_421_size]. Qed.
Lemma assertion_0_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 423))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_18 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_423 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_8_size s i ghost)) as [bit8 E8].
 destruct (one_bit_as_bool _ (encoded_word_18_size s i ghost)) as [bit18 E18].
 destruct (one_bit_as_bool _ (encoded_word_423_size s i ghost)) as [bit423 E423].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_8_value _) (target_18_value _) (target_423_value _).
 rewrite E8 E18 E423.
 destruct bit8, bit18, bit423; vm_compute; intuition discriminate.
Qed.
Lemma assertion_1_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 426)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_426 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_426_value _)|apply encoded_word_426_size]. Qed.
Lemma assertion_1_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eref VarOrder.T (@Eid VarOrder.T 18))) (@Eref VarOrder.T (@Eid VarOrder.T 428))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_18 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_428 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_8_size s i ghost)) as [bit8 E8].
 destruct (one_bit_as_bool _ (encoded_word_18_size s i ghost)) as [bit18 E18].
 destruct (one_bit_as_bool _ (encoded_word_428_size s i ghost)) as [bit428 E428].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_8_value _) (target_18_value _) (target_428_value _).
 rewrite E8 E18 E428.
 destruct bit8, bit18, bit428; vm_compute; intuition discriminate.
Qed.
Lemma assertion_2_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 430)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_430 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_430_value _)|apply encoded_word_430_size]. Qed.
Lemma assertion_2_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 432))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_18 (encoded_leaves s i ghost)) = 0%Z /\
 to_Zpos (word_432 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_8_size s i ghost)) as [bit8 E8].
 destruct (one_bit_as_bool _ (encoded_word_18_size s i ghost)) as [bit18 E18].
 destruct (one_bit_as_bool _ (encoded_word_432_size s i ghost)) as [bit432 E432].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_8_value _) (target_18_value _) (target_432_value _).
 rewrite E8 E18 E432.
 destruct bit8, bit18, bit432; vm_compute; intuition discriminate.
Qed.
Lemma assertion_3_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 437)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_437 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_437_value _)|apply encoded_word_437_size]. Qed.
Lemma assertion_3_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 439))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_18 (encoded_leaves s i ghost)) = 0%Z /\
 to_Zpos (word_439 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_8_size s i ghost)) as [bit8 E8].
 destruct (one_bit_as_bool _ (encoded_word_18_size s i ghost)) as [bit18 E18].
 destruct (one_bit_as_bool _ (encoded_word_439_size s i ghost)) as [bit439 E439].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_8_value _) (target_18_value _) (target_439_value _).
 rewrite E8 E18 E439.
 destruct bit8, bit18, bit439; vm_compute; intuition discriminate.
Qed.
Lemma assertion_4_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 441)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_441 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_441_value _)|apply encoded_word_441_size]. Qed.
Lemma assertion_4_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8))) (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]))) (@Eref VarOrder.T (@Eid VarOrder.T 443))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_18 (encoded_leaves s i ghost)) = 0%Z /\
 to_Zpos (word_443 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_8_size s i ghost)) as [bit8 E8].
 destruct (one_bit_as_bool _ (encoded_word_18_size s i ghost)) as [bit18 E18].
 destruct (one_bit_as_bool _ (encoded_word_443_size s i ghost)) as [bit443 E443].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_8_value _) (target_18_value _) (target_443_value _).
 rewrite E8 E18 E443.
 destruct bit8, bit18, bit443; vm_compute; intuition discriminate.
Qed.
Lemma assertion_5_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 449)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_449 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_449_value _)|apply encoded_word_449_size]. Qed.
Lemma assertion_5_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 448))) (@Eref VarOrder.T (@Eid VarOrder.T 451))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_445 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_448 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_451 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_445_size s i ghost)) as [bit445 E445].
 destruct (one_bit_as_bool _ (encoded_word_448_size s i ghost)) as [bit448 E448].
 destruct (one_bit_as_bool _ (encoded_word_451_size s i ghost)) as [bit451 E451].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_445_value _) (target_448_value _) (target_451_value _).
 rewrite E445 E448 E451.
 destruct bit445, bit448, bit451; vm_compute; intuition discriminate.
Qed.
Lemma assertion_6_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 454)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_454 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_454_value _)|apply encoded_word_454_size]. Qed.
Lemma assertion_6_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 453))) (@Eref VarOrder.T (@Eid VarOrder.T 456))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_445 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_453 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_456 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_445_size s i ghost)) as [bit445 E445].
 destruct (one_bit_as_bool _ (encoded_word_453_size s i ghost)) as [bit453 E453].
 destruct (one_bit_as_bool _ (encoded_word_456_size s i ghost)) as [bit456 E456].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_445_value _) (target_453_value _) (target_456_value _).
 rewrite E445 E453 E456.
 destruct bit445, bit453, bit456; vm_compute; intuition discriminate.
Qed.
Lemma assertion_7_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 461)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_461 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_461_value _)|apply encoded_word_461_size]. Qed.
Lemma assertion_7_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 463))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_445 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_458 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_463 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_445_size s i ghost)) as [bit445 E445].
 destruct (one_bit_as_bool _ (encoded_word_458_size s i ghost)) as [bit458 E458].
 destruct (one_bit_as_bool _ (encoded_word_463_size s i ghost)) as [bit463 E463].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_445_value _) (target_458_value _) (target_463_value _).
 rewrite E445 E458 E463.
 destruct bit445, bit458, bit463; vm_compute; intuition discriminate.
Qed.
Lemma assertion_8_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 469)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_469 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_469_value _)|apply encoded_word_469_size]. Qed.
Lemma assertion_8_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 445))) (@Eref VarOrder.T (@Eid VarOrder.T 458))) (@Eref VarOrder.T (@Eid VarOrder.T 471))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_445 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_458 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_471 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_445_size s i ghost)) as [bit445 E445].
 destruct (one_bit_as_bool _ (encoded_word_458_size s i ghost)) as [bit458 E458].
 destruct (one_bit_as_bool _ (encoded_word_471_size s i ghost)) as [bit471 E471].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_445_value _) (target_458_value _) (target_471_value _).
 rewrite E445 E458 E471.
 destruct bit445, bit458, bit471; vm_compute; intuition discriminate.
Qed.
Lemma assertion_9_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 8)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_8 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_8_value _)|apply encoded_word_8_size]. Qed.
Lemma assertion_9_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 478))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_475 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_478 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_475_size s i ghost)) as [bit475 E475].
 destruct (one_bit_as_bool _ (encoded_word_478_size s i ghost)) as [bit478 E478].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_475_value _) (target_478_value _).
 rewrite E475 E478.
 destruct bit475, bit478; vm_compute; intuition discriminate.
Qed.
Lemma assertion_10_predicate_integer s i ghost :
 Tool.generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 480)) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_480 (encoded_leaves s i ghost)) = 1%Z.
Proof. eapply generated_reference_truth; [exact (target_480_value _)|apply encoded_word_480_size]. Qed.
Lemma assertion_10_guard_integers s i ghost :
 Tool.generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 475))) (@Eref VarOrder.T (@Eid VarOrder.T 482))) (@Econst VarOrder.T (Fuint 1) [::true])) (stable_env (encoded_leaves s i ghost)) <->
 to_Zpos (word_475 (encoded_leaves s i ghost)) = 1%Z /\
 to_Zpos (word_482 (encoded_leaves s i ghost)) = 1%Z.
Proof.
 destruct (one_bit_as_bool _ (encoded_word_475_size s i ghost)) as [bit475 E475].
 destruct (one_bit_as_bool _ (encoded_word_482_size s i ghost)) as [bit482 E482].
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href].
 rewrite (target_475_value _) (target_482_value _).
 rewrite E475 E482.
 destruct bit475, bit482; vm_compute; intuition discriminate.
Qed.
Print Assumptions assertion_10_guard_integers.
