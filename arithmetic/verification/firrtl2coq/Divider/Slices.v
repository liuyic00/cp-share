From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation.
Local Open Scope N_scope.
Lemma slice_drop_take count start (xs : bits) :
 drop start (take count xs) = take (count - start) (drop start xs).
Proof.
 revert count start. induction xs as [|b xs IH]; intros [|count] [|start]; cbn; try reflexivity.
 - by rewrite take0.
 - apply IH.
Qed.
Lemma slice_take_take first second (xs : bits) :
 take first (take second xs) = take (minn first second) xs.
Proof.
 revert first second. induction xs as [|b xs IH]; intros [|first] [|second]; cbn; try reflexivity.
 rewrite minnSS. cbn. rewrite IH. reflexivity.
Qed.

Transparent word_21.
Lemma slice_21 v : word_21 v = take 65 (drop 64 (v 20)).
Proof.
 unfold word_21, closed_21, expr_21, word_of_eval.
 change (drop 64 (take 129 (word_20 v)) = take 65 (drop 64 (v 20))).
 Transparent word_20.
 unfold word_20.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_21.
Opaque word_20.
Lemma slice_21_reference s i ghost : to_Zpos (word_21 (encoded_leaves s i ghost)) = Reference.v33 s i.
Proof. rewrite slice_21 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v33, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_22.
Lemma slice_22 v : word_22 v = take 64 (drop 0 (v 20)).
Proof.
 unfold word_22, closed_22, expr_22, word_of_eval.
 change (drop 0 (take 64 (word_20 v)) = take 64 (drop 0 (v 20))).
 Transparent word_20.
 unfold word_20.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_22.
Opaque word_20.
Lemma slice_22_reference s i ghost : to_Zpos (word_22 (encoded_leaves s i ghost)) = Reference.v40 s i.
Proof. rewrite slice_22 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v40, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_23.
Lemma slice_23 v : word_23 v = take 1 (drop 63 (v 4)).
Proof.
 unfold word_23, closed_23, expr_23, word_of_eval.
 change (drop 63 (take 64 (word_4 v)) = take 1 (drop 63 (v 4))).
 Transparent word_4.
 unfold word_4.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_23.
Opaque word_4.
Lemma slice_23_reference s i ghost : to_Zpos (word_23 (encoded_leaves s i ghost)) = Reference.v45 s i.
Proof. rewrite slice_23 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v45, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_28.
Lemma slice_28 v : word_28 v = take 1 (drop 63 (v 5)).
Proof.
 unfold word_28, closed_28, expr_28, word_of_eval.
 change (drop 63 (take 64 (word_5 v)) = take 1 (drop 63 (v 5))).
 Transparent word_5.
 unfold word_5.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_28.
Opaque word_5.
Lemma slice_28_reference s i ghost : to_Zpos (word_28 (encoded_leaves s i ghost)) = Reference.v48 s i.
Proof. rewrite slice_28 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v48, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_53.
Lemma slice_53 v : word_53 v = take 32 (drop 32 (v 40)).
Proof.
 unfold word_53, closed_53, expr_53, word_of_eval.
 change (drop 32 (take 64 (word_40 v)) = take 32 (drop 32 (v 40))).
 Transparent word_40.
 unfold word_40.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_53.
Opaque word_40.
Lemma slice_53_reference s i ghost : to_Zpos (word_53 (encoded_leaves s i ghost)) = Reference.v63 s i.
Proof. rewrite slice_53 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v63, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_54.
Lemma slice_54 v : word_54 v = take 32 (drop 0 (v 40)).
Proof.
 unfold word_54, closed_54, expr_54, word_of_eval.
 change (drop 0 (take 32 (word_40 v)) = take 32 (drop 0 (v 40))).
 Transparent word_40.
 unfold word_40.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_54.
Opaque word_40.
Transparent word_56.
Lemma slice_56 v : word_56 v = take 16 (drop 48 (v 40)).
Proof.
 unfold word_56, closed_56, expr_56, word_of_eval.
 change (drop 16 (take 32 (word_53 v)) = take 16 (drop 48 (v 40))).
 rewrite slice_53.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_56.
Lemma slice_56_reference s i ghost : to_Zpos (word_56 (encoded_leaves s i ghost)) = Reference.v66 s i.
Proof. rewrite slice_56 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v66, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_57.
Lemma slice_57 v : word_57 v = take 16 (drop 32 (v 40)).
Proof.
 unfold word_57, closed_57, expr_57, word_of_eval.
 change (drop 0 (take 16 (word_53 v)) = take 16 (drop 32 (v 40))).
 rewrite slice_53.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_57.
Transparent word_59.
Lemma slice_59 v : word_59 v = take 8 (drop 56 (v 40)).
Proof.
 unfold word_59, closed_59, expr_59, word_of_eval.
 change (drop 8 (take 16 (word_56 v)) = take 8 (drop 56 (v 40))).
 rewrite slice_56.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_59.
Lemma slice_59_reference s i ghost : to_Zpos (word_59 (encoded_leaves s i ghost)) = Reference.v69 s i.
Proof. rewrite slice_59 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v69, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_60.
Lemma slice_60 v : word_60 v = take 8 (drop 48 (v 40)).
Proof.
 unfold word_60, closed_60, expr_60, word_of_eval.
 change (drop 0 (take 8 (word_56 v)) = take 8 (drop 48 (v 40))).
 rewrite slice_56.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_60.
Transparent word_62.
Lemma slice_62 v : word_62 v = take 4 (drop 60 (v 40)).
Proof.
 unfold word_62, closed_62, expr_62, word_of_eval.
 change (drop 4 (take 8 (word_59 v)) = take 4 (drop 60 (v 40))).
 rewrite slice_59.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_62.
Lemma slice_62_reference s i ghost : to_Zpos (word_62 (encoded_leaves s i ghost)) = Reference.v72 s i.
Proof. rewrite slice_62 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v72, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_63.
Lemma slice_63 v : word_63 v = take 4 (drop 56 (v 40)).
Proof.
 unfold word_63, closed_63, expr_63, word_of_eval.
 change (drop 0 (take 4 (word_59 v)) = take 4 (drop 56 (v 40))).
 rewrite slice_59.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_63.
Transparent word_65.
Lemma slice_65 v : word_65 v = take 1 (drop 63 (v 40)).
Proof.
 unfold word_65, closed_65, expr_65, word_of_eval.
 change (drop 3 (take 4 (word_62 v)) = take 1 (drop 63 (v 40))).
 rewrite slice_62.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_65.
Lemma slice_65_reference s i ghost : to_Zpos (word_65 (encoded_leaves s i ghost)) = Reference.v75 s i.
Proof. rewrite slice_65 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v75, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_66.
Lemma slice_66 v : word_66 v = take 1 (drop 62 (v 40)).
Proof.
 unfold word_66, closed_66, expr_66, word_of_eval.
 change (drop 2 (take 3 (word_62 v)) = take 1 (drop 62 (v 40))).
 rewrite slice_62.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_66.
Lemma slice_66_reference s i ghost : to_Zpos (word_66 (encoded_leaves s i ghost)) = Reference.v77 s i.
Proof. rewrite slice_66 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v77, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_67.
Lemma slice_67 v : word_67 v = take 1 (drop 61 (v 40)).
Proof.
 unfold word_67, closed_67, expr_67, word_of_eval.
 change (drop 1 (take 2 (word_62 v)) = take 1 (drop 61 (v 40))).
 rewrite slice_62.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_67.
Lemma slice_67_reference s i ghost : to_Zpos (word_67 (encoded_leaves s i ghost)) = Reference.v79 s i.
Proof. rewrite slice_67 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v79, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_70.
Lemma slice_70 v : word_70 v = take 1 (drop 59 (v 40)).
Proof.
 unfold word_70, closed_70, expr_70, word_of_eval.
 change (drop 3 (take 4 (word_63 v)) = take 1 (drop 59 (v 40))).
 rewrite slice_63.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_70.
Lemma slice_70_reference s i ghost : to_Zpos (word_70 (encoded_leaves s i ghost)) = Reference.v83 s i.
Proof. rewrite slice_70 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v83, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_71.
Lemma slice_71 v : word_71 v = take 1 (drop 58 (v 40)).
Proof.
 unfold word_71, closed_71, expr_71, word_of_eval.
 change (drop 2 (take 3 (word_63 v)) = take 1 (drop 58 (v 40))).
 rewrite slice_63.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_71.
Lemma slice_71_reference s i ghost : to_Zpos (word_71 (encoded_leaves s i ghost)) = Reference.v84 s i.
Proof. rewrite slice_71 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v84, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_72.
Lemma slice_72 v : word_72 v = take 1 (drop 57 (v 40)).
Proof.
 unfold word_72, closed_72, expr_72, word_of_eval.
 change (drop 1 (take 2 (word_63 v)) = take 1 (drop 57 (v 40))).
 rewrite slice_63.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_72.
Lemma slice_72_reference s i ghost : to_Zpos (word_72 (encoded_leaves s i ghost)) = Reference.v85 s i.
Proof. rewrite slice_72 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v85, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_77.
Lemma slice_77 v : word_77 v = take 4 (drop 52 (v 40)).
Proof.
 unfold word_77, closed_77, expr_77, word_of_eval.
 change (drop 4 (take 8 (word_60 v)) = take 4 (drop 52 (v 40))).
 rewrite slice_60.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_77.
Lemma slice_77_reference s i ghost : to_Zpos (word_77 (encoded_leaves s i ghost)) = Reference.v91 s i.
Proof. rewrite slice_77 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v91, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_78.
Lemma slice_78 v : word_78 v = take 4 (drop 48 (v 40)).
Proof.
 unfold word_78, closed_78, expr_78, word_of_eval.
 change (drop 0 (take 4 (word_60 v)) = take 4 (drop 48 (v 40))).
 rewrite slice_60.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_78.
Transparent word_80.
Lemma slice_80 v : word_80 v = take 1 (drop 55 (v 40)).
Proof.
 unfold word_80, closed_80, expr_80, word_of_eval.
 change (drop 3 (take 4 (word_77 v)) = take 1 (drop 55 (v 40))).
 rewrite slice_77.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_80.
Lemma slice_80_reference s i ghost : to_Zpos (word_80 (encoded_leaves s i ghost)) = Reference.v93 s i.
Proof. rewrite slice_80 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v93, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_81.
Lemma slice_81 v : word_81 v = take 1 (drop 54 (v 40)).
Proof.
 unfold word_81, closed_81, expr_81, word_of_eval.
 change (drop 2 (take 3 (word_77 v)) = take 1 (drop 54 (v 40))).
 rewrite slice_77.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_81.
Lemma slice_81_reference s i ghost : to_Zpos (word_81 (encoded_leaves s i ghost)) = Reference.v94 s i.
Proof. rewrite slice_81 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v94, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_82.
Lemma slice_82 v : word_82 v = take 1 (drop 53 (v 40)).
Proof.
 unfold word_82, closed_82, expr_82, word_of_eval.
 change (drop 1 (take 2 (word_77 v)) = take 1 (drop 53 (v 40))).
 rewrite slice_77.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_82.
Lemma slice_82_reference s i ghost : to_Zpos (word_82 (encoded_leaves s i ghost)) = Reference.v95 s i.
Proof. rewrite slice_82 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v95, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_85.
Lemma slice_85 v : word_85 v = take 1 (drop 51 (v 40)).
Proof.
 unfold word_85, closed_85, expr_85, word_of_eval.
 change (drop 3 (take 4 (word_78 v)) = take 1 (drop 51 (v 40))).
 rewrite slice_78.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_85.
Lemma slice_85_reference s i ghost : to_Zpos (word_85 (encoded_leaves s i ghost)) = Reference.v99 s i.
Proof. rewrite slice_85 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v99, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_86.
Lemma slice_86 v : word_86 v = take 1 (drop 50 (v 40)).
Proof.
 unfold word_86, closed_86, expr_86, word_of_eval.
 change (drop 2 (take 3 (word_78 v)) = take 1 (drop 50 (v 40))).
 rewrite slice_78.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_86.
Lemma slice_86_reference s i ghost : to_Zpos (word_86 (encoded_leaves s i ghost)) = Reference.v100 s i.
Proof. rewrite slice_86 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v100, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_87.
Lemma slice_87 v : word_87 v = take 1 (drop 49 (v 40)).
Proof.
 unfold word_87, closed_87, expr_87, word_of_eval.
 change (drop 1 (take 2 (word_78 v)) = take 1 (drop 49 (v 40))).
 rewrite slice_78.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_87.
Lemma slice_87_reference s i ghost : to_Zpos (word_87 (encoded_leaves s i ghost)) = Reference.v101 s i.
Proof. rewrite slice_87 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v101, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_94.
Lemma slice_94 v : word_94 v = take 8 (drop 40 (v 40)).
Proof.
 unfold word_94, closed_94, expr_94, word_of_eval.
 change (drop 8 (take 16 (word_57 v)) = take 8 (drop 40 (v 40))).
 rewrite slice_57.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_94.
Lemma slice_94_reference s i ghost : to_Zpos (word_94 (encoded_leaves s i ghost)) = Reference.v109 s i.
Proof. rewrite slice_94 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v109, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_95.
Lemma slice_95 v : word_95 v = take 8 (drop 32 (v 40)).
Proof.
 unfold word_95, closed_95, expr_95, word_of_eval.
 change (drop 0 (take 8 (word_57 v)) = take 8 (drop 32 (v 40))).
 rewrite slice_57.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_95.
Transparent word_97.
Lemma slice_97 v : word_97 v = take 4 (drop 44 (v 40)).
Proof.
 unfold word_97, closed_97, expr_97, word_of_eval.
 change (drop 4 (take 8 (word_94 v)) = take 4 (drop 44 (v 40))).
 rewrite slice_94.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_97.
Lemma slice_97_reference s i ghost : to_Zpos (word_97 (encoded_leaves s i ghost)) = Reference.v111 s i.
Proof. rewrite slice_97 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v111, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_98.
Lemma slice_98 v : word_98 v = take 4 (drop 40 (v 40)).
Proof.
 unfold word_98, closed_98, expr_98, word_of_eval.
 change (drop 0 (take 4 (word_94 v)) = take 4 (drop 40 (v 40))).
 rewrite slice_94.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_98.
Transparent word_100.
Lemma slice_100 v : word_100 v = take 1 (drop 47 (v 40)).
Proof.
 unfold word_100, closed_100, expr_100, word_of_eval.
 change (drop 3 (take 4 (word_97 v)) = take 1 (drop 47 (v 40))).
 rewrite slice_97.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_100.
Lemma slice_100_reference s i ghost : to_Zpos (word_100 (encoded_leaves s i ghost)) = Reference.v113 s i.
Proof. rewrite slice_100 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v113, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_101.
Lemma slice_101 v : word_101 v = take 1 (drop 46 (v 40)).
Proof.
 unfold word_101, closed_101, expr_101, word_of_eval.
 change (drop 2 (take 3 (word_97 v)) = take 1 (drop 46 (v 40))).
 rewrite slice_97.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_101.
Lemma slice_101_reference s i ghost : to_Zpos (word_101 (encoded_leaves s i ghost)) = Reference.v114 s i.
Proof. rewrite slice_101 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v114, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_102.
Lemma slice_102 v : word_102 v = take 1 (drop 45 (v 40)).
Proof.
 unfold word_102, closed_102, expr_102, word_of_eval.
 change (drop 1 (take 2 (word_97 v)) = take 1 (drop 45 (v 40))).
 rewrite slice_97.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_102.
Lemma slice_102_reference s i ghost : to_Zpos (word_102 (encoded_leaves s i ghost)) = Reference.v115 s i.
Proof. rewrite slice_102 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v115, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_105.
Lemma slice_105 v : word_105 v = take 1 (drop 43 (v 40)).
Proof.
 unfold word_105, closed_105, expr_105, word_of_eval.
 change (drop 3 (take 4 (word_98 v)) = take 1 (drop 43 (v 40))).
 rewrite slice_98.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_105.
Lemma slice_105_reference s i ghost : to_Zpos (word_105 (encoded_leaves s i ghost)) = Reference.v119 s i.
Proof. rewrite slice_105 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v119, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_106.
Lemma slice_106 v : word_106 v = take 1 (drop 42 (v 40)).
Proof.
 unfold word_106, closed_106, expr_106, word_of_eval.
 change (drop 2 (take 3 (word_98 v)) = take 1 (drop 42 (v 40))).
 rewrite slice_98.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_106.
Lemma slice_106_reference s i ghost : to_Zpos (word_106 (encoded_leaves s i ghost)) = Reference.v120 s i.
Proof. rewrite slice_106 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v120, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_107.
Lemma slice_107 v : word_107 v = take 1 (drop 41 (v 40)).
Proof.
 unfold word_107, closed_107, expr_107, word_of_eval.
 change (drop 1 (take 2 (word_98 v)) = take 1 (drop 41 (v 40))).
 rewrite slice_98.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_107.
Lemma slice_107_reference s i ghost : to_Zpos (word_107 (encoded_leaves s i ghost)) = Reference.v121 s i.
Proof. rewrite slice_107 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v121, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_112.
Lemma slice_112 v : word_112 v = take 4 (drop 36 (v 40)).
Proof.
 unfold word_112, closed_112, expr_112, word_of_eval.
 change (drop 4 (take 8 (word_95 v)) = take 4 (drop 36 (v 40))).
 rewrite slice_95.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_112.
Lemma slice_112_reference s i ghost : to_Zpos (word_112 (encoded_leaves s i ghost)) = Reference.v127 s i.
Proof. rewrite slice_112 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v127, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_113.
Lemma slice_113 v : word_113 v = take 4 (drop 32 (v 40)).
Proof.
 unfold word_113, closed_113, expr_113, word_of_eval.
 change (drop 0 (take 4 (word_95 v)) = take 4 (drop 32 (v 40))).
 rewrite slice_95.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_113.
Transparent word_115.
Lemma slice_115 v : word_115 v = take 1 (drop 39 (v 40)).
Proof.
 unfold word_115, closed_115, expr_115, word_of_eval.
 change (drop 3 (take 4 (word_112 v)) = take 1 (drop 39 (v 40))).
 rewrite slice_112.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_115.
Lemma slice_115_reference s i ghost : to_Zpos (word_115 (encoded_leaves s i ghost)) = Reference.v129 s i.
Proof. rewrite slice_115 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v129, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_116.
Lemma slice_116 v : word_116 v = take 1 (drop 38 (v 40)).
Proof.
 unfold word_116, closed_116, expr_116, word_of_eval.
 change (drop 2 (take 3 (word_112 v)) = take 1 (drop 38 (v 40))).
 rewrite slice_112.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_116.
Lemma slice_116_reference s i ghost : to_Zpos (word_116 (encoded_leaves s i ghost)) = Reference.v130 s i.
Proof. rewrite slice_116 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v130, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_117.
Lemma slice_117 v : word_117 v = take 1 (drop 37 (v 40)).
Proof.
 unfold word_117, closed_117, expr_117, word_of_eval.
 change (drop 1 (take 2 (word_112 v)) = take 1 (drop 37 (v 40))).
 rewrite slice_112.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_117.
Lemma slice_117_reference s i ghost : to_Zpos (word_117 (encoded_leaves s i ghost)) = Reference.v131 s i.
Proof. rewrite slice_117 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v131, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_120.
Lemma slice_120 v : word_120 v = take 1 (drop 35 (v 40)).
Proof.
 unfold word_120, closed_120, expr_120, word_of_eval.
 change (drop 3 (take 4 (word_113 v)) = take 1 (drop 35 (v 40))).
 rewrite slice_113.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_120.
Lemma slice_120_reference s i ghost : to_Zpos (word_120 (encoded_leaves s i ghost)) = Reference.v135 s i.
Proof. rewrite slice_120 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v135, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_121.
Lemma slice_121 v : word_121 v = take 1 (drop 34 (v 40)).
Proof.
 unfold word_121, closed_121, expr_121, word_of_eval.
 change (drop 2 (take 3 (word_113 v)) = take 1 (drop 34 (v 40))).
 rewrite slice_113.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_121.
Lemma slice_121_reference s i ghost : to_Zpos (word_121 (encoded_leaves s i ghost)) = Reference.v136 s i.
Proof. rewrite slice_121 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v136, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_122.
Lemma slice_122 v : word_122 v = take 1 (drop 33 (v 40)).
Proof.
 unfold word_122, closed_122, expr_122, word_of_eval.
 change (drop 1 (take 2 (word_113 v)) = take 1 (drop 33 (v 40))).
 rewrite slice_113.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_122.
Lemma slice_122_reference s i ghost : to_Zpos (word_122 (encoded_leaves s i ghost)) = Reference.v137 s i.
Proof. rewrite slice_122 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v137, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_131.
Lemma slice_131 v : word_131 v = take 16 (drop 16 (v 40)).
Proof.
 unfold word_131, closed_131, expr_131, word_of_eval.
 change (drop 16 (take 32 (word_54 v)) = take 16 (drop 16 (v 40))).
 rewrite slice_54.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_131.
Lemma slice_131_reference s i ghost : to_Zpos (word_131 (encoded_leaves s i ghost)) = Reference.v147 s i.
Proof. rewrite slice_131 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v147, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_132.
Lemma slice_132 v : word_132 v = take 16 (drop 0 (v 40)).
Proof.
 unfold word_132, closed_132, expr_132, word_of_eval.
 change (drop 0 (take 16 (word_54 v)) = take 16 (drop 0 (v 40))).
 rewrite slice_54.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_132.
Transparent word_134.
Lemma slice_134 v : word_134 v = take 8 (drop 24 (v 40)).
Proof.
 unfold word_134, closed_134, expr_134, word_of_eval.
 change (drop 8 (take 16 (word_131 v)) = take 8 (drop 24 (v 40))).
 rewrite slice_131.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_134.
Lemma slice_134_reference s i ghost : to_Zpos (word_134 (encoded_leaves s i ghost)) = Reference.v149 s i.
Proof. rewrite slice_134 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v149, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_135.
Lemma slice_135 v : word_135 v = take 8 (drop 16 (v 40)).
Proof.
 unfold word_135, closed_135, expr_135, word_of_eval.
 change (drop 0 (take 8 (word_131 v)) = take 8 (drop 16 (v 40))).
 rewrite slice_131.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_135.
Transparent word_137.
Lemma slice_137 v : word_137 v = take 4 (drop 28 (v 40)).
Proof.
 unfold word_137, closed_137, expr_137, word_of_eval.
 change (drop 4 (take 8 (word_134 v)) = take 4 (drop 28 (v 40))).
 rewrite slice_134.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_137.
Lemma slice_137_reference s i ghost : to_Zpos (word_137 (encoded_leaves s i ghost)) = Reference.v151 s i.
Proof. rewrite slice_137 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v151, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_138.
Lemma slice_138 v : word_138 v = take 4 (drop 24 (v 40)).
Proof.
 unfold word_138, closed_138, expr_138, word_of_eval.
 change (drop 0 (take 4 (word_134 v)) = take 4 (drop 24 (v 40))).
 rewrite slice_134.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_138.
Transparent word_140.
Lemma slice_140 v : word_140 v = take 1 (drop 31 (v 40)).
Proof.
 unfold word_140, closed_140, expr_140, word_of_eval.
 change (drop 3 (take 4 (word_137 v)) = take 1 (drop 31 (v 40))).
 rewrite slice_137.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_140.
Lemma slice_140_reference s i ghost : to_Zpos (word_140 (encoded_leaves s i ghost)) = Reference.v153 s i.
Proof. rewrite slice_140 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v153, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_141.
Lemma slice_141 v : word_141 v = take 1 (drop 30 (v 40)).
Proof.
 unfold word_141, closed_141, expr_141, word_of_eval.
 change (drop 2 (take 3 (word_137 v)) = take 1 (drop 30 (v 40))).
 rewrite slice_137.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_141.
Lemma slice_141_reference s i ghost : to_Zpos (word_141 (encoded_leaves s i ghost)) = Reference.v154 s i.
Proof. rewrite slice_141 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v154, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_142.
Lemma slice_142 v : word_142 v = take 1 (drop 29 (v 40)).
Proof.
 unfold word_142, closed_142, expr_142, word_of_eval.
 change (drop 1 (take 2 (word_137 v)) = take 1 (drop 29 (v 40))).
 rewrite slice_137.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_142.
Lemma slice_142_reference s i ghost : to_Zpos (word_142 (encoded_leaves s i ghost)) = Reference.v155 s i.
Proof. rewrite slice_142 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v155, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_145.
Lemma slice_145 v : word_145 v = take 1 (drop 27 (v 40)).
Proof.
 unfold word_145, closed_145, expr_145, word_of_eval.
 change (drop 3 (take 4 (word_138 v)) = take 1 (drop 27 (v 40))).
 rewrite slice_138.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_145.
Lemma slice_145_reference s i ghost : to_Zpos (word_145 (encoded_leaves s i ghost)) = Reference.v159 s i.
Proof. rewrite slice_145 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v159, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_146.
Lemma slice_146 v : word_146 v = take 1 (drop 26 (v 40)).
Proof.
 unfold word_146, closed_146, expr_146, word_of_eval.
 change (drop 2 (take 3 (word_138 v)) = take 1 (drop 26 (v 40))).
 rewrite slice_138.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_146.
Lemma slice_146_reference s i ghost : to_Zpos (word_146 (encoded_leaves s i ghost)) = Reference.v160 s i.
Proof. rewrite slice_146 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v160, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_147.
Lemma slice_147 v : word_147 v = take 1 (drop 25 (v 40)).
Proof.
 unfold word_147, closed_147, expr_147, word_of_eval.
 change (drop 1 (take 2 (word_138 v)) = take 1 (drop 25 (v 40))).
 rewrite slice_138.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_147.
Lemma slice_147_reference s i ghost : to_Zpos (word_147 (encoded_leaves s i ghost)) = Reference.v161 s i.
Proof. rewrite slice_147 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v161, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_152.
Lemma slice_152 v : word_152 v = take 4 (drop 20 (v 40)).
Proof.
 unfold word_152, closed_152, expr_152, word_of_eval.
 change (drop 4 (take 8 (word_135 v)) = take 4 (drop 20 (v 40))).
 rewrite slice_135.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_152.
Lemma slice_152_reference s i ghost : to_Zpos (word_152 (encoded_leaves s i ghost)) = Reference.v167 s i.
Proof. rewrite slice_152 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v167, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_153.
Lemma slice_153 v : word_153 v = take 4 (drop 16 (v 40)).
Proof.
 unfold word_153, closed_153, expr_153, word_of_eval.
 change (drop 0 (take 4 (word_135 v)) = take 4 (drop 16 (v 40))).
 rewrite slice_135.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_153.
Transparent word_155.
Lemma slice_155 v : word_155 v = take 1 (drop 23 (v 40)).
Proof.
 unfold word_155, closed_155, expr_155, word_of_eval.
 change (drop 3 (take 4 (word_152 v)) = take 1 (drop 23 (v 40))).
 rewrite slice_152.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_155.
Lemma slice_155_reference s i ghost : to_Zpos (word_155 (encoded_leaves s i ghost)) = Reference.v169 s i.
Proof. rewrite slice_155 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v169, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_156.
Lemma slice_156 v : word_156 v = take 1 (drop 22 (v 40)).
Proof.
 unfold word_156, closed_156, expr_156, word_of_eval.
 change (drop 2 (take 3 (word_152 v)) = take 1 (drop 22 (v 40))).
 rewrite slice_152.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_156.
Lemma slice_156_reference s i ghost : to_Zpos (word_156 (encoded_leaves s i ghost)) = Reference.v170 s i.
Proof. rewrite slice_156 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v170, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_157.
Lemma slice_157 v : word_157 v = take 1 (drop 21 (v 40)).
Proof.
 unfold word_157, closed_157, expr_157, word_of_eval.
 change (drop 1 (take 2 (word_152 v)) = take 1 (drop 21 (v 40))).
 rewrite slice_152.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_157.
Lemma slice_157_reference s i ghost : to_Zpos (word_157 (encoded_leaves s i ghost)) = Reference.v171 s i.
Proof. rewrite slice_157 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v171, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_160.
Lemma slice_160 v : word_160 v = take 1 (drop 19 (v 40)).
Proof.
 unfold word_160, closed_160, expr_160, word_of_eval.
 change (drop 3 (take 4 (word_153 v)) = take 1 (drop 19 (v 40))).
 rewrite slice_153.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_160.
Lemma slice_160_reference s i ghost : to_Zpos (word_160 (encoded_leaves s i ghost)) = Reference.v175 s i.
Proof. rewrite slice_160 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v175, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_161.
Lemma slice_161 v : word_161 v = take 1 (drop 18 (v 40)).
Proof.
 unfold word_161, closed_161, expr_161, word_of_eval.
 change (drop 2 (take 3 (word_153 v)) = take 1 (drop 18 (v 40))).
 rewrite slice_153.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_161.
Lemma slice_161_reference s i ghost : to_Zpos (word_161 (encoded_leaves s i ghost)) = Reference.v176 s i.
Proof. rewrite slice_161 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v176, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_162.
Lemma slice_162 v : word_162 v = take 1 (drop 17 (v 40)).
Proof.
 unfold word_162, closed_162, expr_162, word_of_eval.
 change (drop 1 (take 2 (word_153 v)) = take 1 (drop 17 (v 40))).
 rewrite slice_153.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_162.
Lemma slice_162_reference s i ghost : to_Zpos (word_162 (encoded_leaves s i ghost)) = Reference.v177 s i.
Proof. rewrite slice_162 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v177, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_169.
Lemma slice_169 v : word_169 v = take 8 (drop 8 (v 40)).
Proof.
 unfold word_169, closed_169, expr_169, word_of_eval.
 change (drop 8 (take 16 (word_132 v)) = take 8 (drop 8 (v 40))).
 rewrite slice_132.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_169.
Lemma slice_169_reference s i ghost : to_Zpos (word_169 (encoded_leaves s i ghost)) = Reference.v185 s i.
Proof. rewrite slice_169 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v185, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_170.
Lemma slice_170 v : word_170 v = take 8 (drop 0 (v 40)).
Proof.
 unfold word_170, closed_170, expr_170, word_of_eval.
 change (drop 0 (take 8 (word_132 v)) = take 8 (drop 0 (v 40))).
 rewrite slice_132.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_170.
Transparent word_172.
Lemma slice_172 v : word_172 v = take 4 (drop 12 (v 40)).
Proof.
 unfold word_172, closed_172, expr_172, word_of_eval.
 change (drop 4 (take 8 (word_169 v)) = take 4 (drop 12 (v 40))).
 rewrite slice_169.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_172.
Lemma slice_172_reference s i ghost : to_Zpos (word_172 (encoded_leaves s i ghost)) = Reference.v187 s i.
Proof. rewrite slice_172 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v187, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_173.
Lemma slice_173 v : word_173 v = take 4 (drop 8 (v 40)).
Proof.
 unfold word_173, closed_173, expr_173, word_of_eval.
 change (drop 0 (take 4 (word_169 v)) = take 4 (drop 8 (v 40))).
 rewrite slice_169.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_173.
Transparent word_175.
Lemma slice_175 v : word_175 v = take 1 (drop 15 (v 40)).
Proof.
 unfold word_175, closed_175, expr_175, word_of_eval.
 change (drop 3 (take 4 (word_172 v)) = take 1 (drop 15 (v 40))).
 rewrite slice_172.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_175.
Lemma slice_175_reference s i ghost : to_Zpos (word_175 (encoded_leaves s i ghost)) = Reference.v189 s i.
Proof. rewrite slice_175 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v189, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_176.
Lemma slice_176 v : word_176 v = take 1 (drop 14 (v 40)).
Proof.
 unfold word_176, closed_176, expr_176, word_of_eval.
 change (drop 2 (take 3 (word_172 v)) = take 1 (drop 14 (v 40))).
 rewrite slice_172.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_176.
Lemma slice_176_reference s i ghost : to_Zpos (word_176 (encoded_leaves s i ghost)) = Reference.v190 s i.
Proof. rewrite slice_176 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v190, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_177.
Lemma slice_177 v : word_177 v = take 1 (drop 13 (v 40)).
Proof.
 unfold word_177, closed_177, expr_177, word_of_eval.
 change (drop 1 (take 2 (word_172 v)) = take 1 (drop 13 (v 40))).
 rewrite slice_172.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_177.
Lemma slice_177_reference s i ghost : to_Zpos (word_177 (encoded_leaves s i ghost)) = Reference.v191 s i.
Proof. rewrite slice_177 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v191, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_180.
Lemma slice_180 v : word_180 v = take 1 (drop 11 (v 40)).
Proof.
 unfold word_180, closed_180, expr_180, word_of_eval.
 change (drop 3 (take 4 (word_173 v)) = take 1 (drop 11 (v 40))).
 rewrite slice_173.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_180.
Lemma slice_180_reference s i ghost : to_Zpos (word_180 (encoded_leaves s i ghost)) = Reference.v195 s i.
Proof. rewrite slice_180 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v195, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_181.
Lemma slice_181 v : word_181 v = take 1 (drop 10 (v 40)).
Proof.
 unfold word_181, closed_181, expr_181, word_of_eval.
 change (drop 2 (take 3 (word_173 v)) = take 1 (drop 10 (v 40))).
 rewrite slice_173.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_181.
Lemma slice_181_reference s i ghost : to_Zpos (word_181 (encoded_leaves s i ghost)) = Reference.v196 s i.
Proof. rewrite slice_181 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v196, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_182.
Lemma slice_182 v : word_182 v = take 1 (drop 9 (v 40)).
Proof.
 unfold word_182, closed_182, expr_182, word_of_eval.
 change (drop 1 (take 2 (word_173 v)) = take 1 (drop 9 (v 40))).
 rewrite slice_173.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_182.
Lemma slice_182_reference s i ghost : to_Zpos (word_182 (encoded_leaves s i ghost)) = Reference.v197 s i.
Proof. rewrite slice_182 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v197, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_187.
Lemma slice_187 v : word_187 v = take 4 (drop 4 (v 40)).
Proof.
 unfold word_187, closed_187, expr_187, word_of_eval.
 change (drop 4 (take 8 (word_170 v)) = take 4 (drop 4 (v 40))).
 rewrite slice_170.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_187.
Lemma slice_187_reference s i ghost : to_Zpos (word_187 (encoded_leaves s i ghost)) = Reference.v203 s i.
Proof. rewrite slice_187 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v203, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_188.
Lemma slice_188 v : word_188 v = take 4 (drop 0 (v 40)).
Proof.
 unfold word_188, closed_188, expr_188, word_of_eval.
 change (drop 0 (take 4 (word_170 v)) = take 4 (drop 0 (v 40))).
 rewrite slice_170.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_188.
Transparent word_190.
Lemma slice_190 v : word_190 v = take 1 (drop 7 (v 40)).
Proof.
 unfold word_190, closed_190, expr_190, word_of_eval.
 change (drop 3 (take 4 (word_187 v)) = take 1 (drop 7 (v 40))).
 rewrite slice_187.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_190.
Lemma slice_190_reference s i ghost : to_Zpos (word_190 (encoded_leaves s i ghost)) = Reference.v205 s i.
Proof. rewrite slice_190 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v205, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_191.
Lemma slice_191 v : word_191 v = take 1 (drop 6 (v 40)).
Proof.
 unfold word_191, closed_191, expr_191, word_of_eval.
 change (drop 2 (take 3 (word_187 v)) = take 1 (drop 6 (v 40))).
 rewrite slice_187.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_191.
Lemma slice_191_reference s i ghost : to_Zpos (word_191 (encoded_leaves s i ghost)) = Reference.v206 s i.
Proof. rewrite slice_191 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v206, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_192.
Lemma slice_192 v : word_192 v = take 1 (drop 5 (v 40)).
Proof.
 unfold word_192, closed_192, expr_192, word_of_eval.
 change (drop 1 (take 2 (word_187 v)) = take 1 (drop 5 (v 40))).
 rewrite slice_187.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_192.
Lemma slice_192_reference s i ghost : to_Zpos (word_192 (encoded_leaves s i ghost)) = Reference.v207 s i.
Proof. rewrite slice_192 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v207, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_195.
Lemma slice_195 v : word_195 v = take 1 (drop 3 (v 40)).
Proof.
 unfold word_195, closed_195, expr_195, word_of_eval.
 change (drop 3 (take 4 (word_188 v)) = take 1 (drop 3 (v 40))).
 rewrite slice_188.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_195.
Lemma slice_195_reference s i ghost : to_Zpos (word_195 (encoded_leaves s i ghost)) = Reference.v211 s i.
Proof. rewrite slice_195 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v211, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_196.
Lemma slice_196 v : word_196 v = take 1 (drop 2 (v 40)).
Proof.
 unfold word_196, closed_196, expr_196, word_of_eval.
 change (drop 2 (take 3 (word_188 v)) = take 1 (drop 2 (v 40))).
 rewrite slice_188.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_196.
Lemma slice_196_reference s i ghost : to_Zpos (word_196 (encoded_leaves s i ghost)) = Reference.v212 s i.
Proof. rewrite slice_196 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v212, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_197.
Lemma slice_197 v : word_197 v = take 1 (drop 1 (v 40)).
Proof.
 unfold word_197, closed_197, expr_197, word_of_eval.
 change (drop 1 (take 2 (word_188 v)) = take 1 (drop 1 (v 40))).
 rewrite slice_188.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_197.
Lemma slice_197_reference s i ghost : to_Zpos (word_197 (encoded_leaves s i ghost)) = Reference.v213 s i.
Proof. rewrite slice_197 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v213, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_210.
Lemma slice_210 v : word_210 v = take 1 (drop 64 (v 43)).
Proof.
 unfold word_210, closed_210, expr_210, word_of_eval.
 change (drop 64 (take 65 (word_43 v)) = take 1 (drop 64 (v 43))).
 Transparent word_43.
 unfold word_43.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_210.
Opaque word_43.
Lemma slice_210_reference s i ghost : to_Zpos (word_210 (encoded_leaves s i ghost)) = Reference.v227 s i.
Proof. rewrite slice_210 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v227, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_211.
Lemma slice_211 v : word_211 v = take 64 (drop 0 (v 43)).
Proof.
 unfold word_211, closed_211, expr_211, word_of_eval.
 change (drop 0 (take 64 (word_43 v)) = take 64 (drop 0 (v 43))).
 Transparent word_43.
 unfold word_43.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_211.
Opaque word_43.
Transparent word_213.
Lemma slice_213 v : word_213 v = take 32 (drop 32 (v 43)).
Proof.
 unfold word_213, closed_213, expr_213, word_of_eval.
 change (drop 32 (take 64 (word_211 v)) = take 32 (drop 32 (v 43))).
 rewrite slice_211.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_213.
Lemma slice_213_reference s i ghost : to_Zpos (word_213 (encoded_leaves s i ghost)) = Reference.v228 s i.
Proof. rewrite slice_213 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v228, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_214.
Lemma slice_214 v : word_214 v = take 32 (drop 0 (v 43)).
Proof.
 unfold word_214, closed_214, expr_214, word_of_eval.
 change (drop 0 (take 32 (word_211 v)) = take 32 (drop 0 (v 43))).
 rewrite slice_211.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_214.
Transparent word_216.
Lemma slice_216 v : word_216 v = take 16 (drop 48 (v 43)).
Proof.
 unfold word_216, closed_216, expr_216, word_of_eval.
 change (drop 16 (take 32 (word_213 v)) = take 16 (drop 48 (v 43))).
 rewrite slice_213.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_216.
Lemma slice_216_reference s i ghost : to_Zpos (word_216 (encoded_leaves s i ghost)) = Reference.v230 s i.
Proof. rewrite slice_216 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v230, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_217.
Lemma slice_217 v : word_217 v = take 16 (drop 32 (v 43)).
Proof.
 unfold word_217, closed_217, expr_217, word_of_eval.
 change (drop 0 (take 16 (word_213 v)) = take 16 (drop 32 (v 43))).
 rewrite slice_213.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_217.
Transparent word_219.
Lemma slice_219 v : word_219 v = take 8 (drop 56 (v 43)).
Proof.
 unfold word_219, closed_219, expr_219, word_of_eval.
 change (drop 8 (take 16 (word_216 v)) = take 8 (drop 56 (v 43))).
 rewrite slice_216.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_219.
Lemma slice_219_reference s i ghost : to_Zpos (word_219 (encoded_leaves s i ghost)) = Reference.v232 s i.
Proof. rewrite slice_219 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v232, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_220.
Lemma slice_220 v : word_220 v = take 8 (drop 48 (v 43)).
Proof.
 unfold word_220, closed_220, expr_220, word_of_eval.
 change (drop 0 (take 8 (word_216 v)) = take 8 (drop 48 (v 43))).
 rewrite slice_216.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_220.
Transparent word_222.
Lemma slice_222 v : word_222 v = take 4 (drop 60 (v 43)).
Proof.
 unfold word_222, closed_222, expr_222, word_of_eval.
 change (drop 4 (take 8 (word_219 v)) = take 4 (drop 60 (v 43))).
 rewrite slice_219.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_222.
Lemma slice_222_reference s i ghost : to_Zpos (word_222 (encoded_leaves s i ghost)) = Reference.v234 s i.
Proof. rewrite slice_222 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v234, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_223.
Lemma slice_223 v : word_223 v = take 4 (drop 56 (v 43)).
Proof.
 unfold word_223, closed_223, expr_223, word_of_eval.
 change (drop 0 (take 4 (word_219 v)) = take 4 (drop 56 (v 43))).
 rewrite slice_219.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_223.
Transparent word_225.
Lemma slice_225 v : word_225 v = take 1 (drop 63 (v 43)).
Proof.
 unfold word_225, closed_225, expr_225, word_of_eval.
 change (drop 3 (take 4 (word_222 v)) = take 1 (drop 63 (v 43))).
 rewrite slice_222.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_225.
Lemma slice_225_reference s i ghost : to_Zpos (word_225 (encoded_leaves s i ghost)) = Reference.v236 s i.
Proof. rewrite slice_225 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v236, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_226.
Lemma slice_226 v : word_226 v = take 1 (drop 62 (v 43)).
Proof.
 unfold word_226, closed_226, expr_226, word_of_eval.
 change (drop 2 (take 3 (word_222 v)) = take 1 (drop 62 (v 43))).
 rewrite slice_222.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_226.
Lemma slice_226_reference s i ghost : to_Zpos (word_226 (encoded_leaves s i ghost)) = Reference.v237 s i.
Proof. rewrite slice_226 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v237, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_227.
Lemma slice_227 v : word_227 v = take 1 (drop 61 (v 43)).
Proof.
 unfold word_227, closed_227, expr_227, word_of_eval.
 change (drop 1 (take 2 (word_222 v)) = take 1 (drop 61 (v 43))).
 rewrite slice_222.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_227.
Lemma slice_227_reference s i ghost : to_Zpos (word_227 (encoded_leaves s i ghost)) = Reference.v238 s i.
Proof. rewrite slice_227 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v238, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_230.
Lemma slice_230 v : word_230 v = take 1 (drop 59 (v 43)).
Proof.
 unfold word_230, closed_230, expr_230, word_of_eval.
 change (drop 3 (take 4 (word_223 v)) = take 1 (drop 59 (v 43))).
 rewrite slice_223.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_230.
Lemma slice_230_reference s i ghost : to_Zpos (word_230 (encoded_leaves s i ghost)) = Reference.v242 s i.
Proof. rewrite slice_230 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v242, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_231.
Lemma slice_231 v : word_231 v = take 1 (drop 58 (v 43)).
Proof.
 unfold word_231, closed_231, expr_231, word_of_eval.
 change (drop 2 (take 3 (word_223 v)) = take 1 (drop 58 (v 43))).
 rewrite slice_223.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_231.
Lemma slice_231_reference s i ghost : to_Zpos (word_231 (encoded_leaves s i ghost)) = Reference.v243 s i.
Proof. rewrite slice_231 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v243, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_232.
Lemma slice_232 v : word_232 v = take 1 (drop 57 (v 43)).
Proof.
 unfold word_232, closed_232, expr_232, word_of_eval.
 change (drop 1 (take 2 (word_223 v)) = take 1 (drop 57 (v 43))).
 rewrite slice_223.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_232.
Lemma slice_232_reference s i ghost : to_Zpos (word_232 (encoded_leaves s i ghost)) = Reference.v244 s i.
Proof. rewrite slice_232 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v244, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_237.
Lemma slice_237 v : word_237 v = take 4 (drop 52 (v 43)).
Proof.
 unfold word_237, closed_237, expr_237, word_of_eval.
 change (drop 4 (take 8 (word_220 v)) = take 4 (drop 52 (v 43))).
 rewrite slice_220.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_237.
Lemma slice_237_reference s i ghost : to_Zpos (word_237 (encoded_leaves s i ghost)) = Reference.v250 s i.
Proof. rewrite slice_237 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v250, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_238.
Lemma slice_238 v : word_238 v = take 4 (drop 48 (v 43)).
Proof.
 unfold word_238, closed_238, expr_238, word_of_eval.
 change (drop 0 (take 4 (word_220 v)) = take 4 (drop 48 (v 43))).
 rewrite slice_220.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_238.
Transparent word_240.
Lemma slice_240 v : word_240 v = take 1 (drop 55 (v 43)).
Proof.
 unfold word_240, closed_240, expr_240, word_of_eval.
 change (drop 3 (take 4 (word_237 v)) = take 1 (drop 55 (v 43))).
 rewrite slice_237.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_240.
Lemma slice_240_reference s i ghost : to_Zpos (word_240 (encoded_leaves s i ghost)) = Reference.v252 s i.
Proof. rewrite slice_240 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v252, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_241.
Lemma slice_241 v : word_241 v = take 1 (drop 54 (v 43)).
Proof.
 unfold word_241, closed_241, expr_241, word_of_eval.
 change (drop 2 (take 3 (word_237 v)) = take 1 (drop 54 (v 43))).
 rewrite slice_237.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_241.
Lemma slice_241_reference s i ghost : to_Zpos (word_241 (encoded_leaves s i ghost)) = Reference.v253 s i.
Proof. rewrite slice_241 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v253, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_242.
Lemma slice_242 v : word_242 v = take 1 (drop 53 (v 43)).
Proof.
 unfold word_242, closed_242, expr_242, word_of_eval.
 change (drop 1 (take 2 (word_237 v)) = take 1 (drop 53 (v 43))).
 rewrite slice_237.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_242.
Lemma slice_242_reference s i ghost : to_Zpos (word_242 (encoded_leaves s i ghost)) = Reference.v254 s i.
Proof. rewrite slice_242 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v254, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_245.
Lemma slice_245 v : word_245 v = take 1 (drop 51 (v 43)).
Proof.
 unfold word_245, closed_245, expr_245, word_of_eval.
 change (drop 3 (take 4 (word_238 v)) = take 1 (drop 51 (v 43))).
 rewrite slice_238.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_245.
Lemma slice_245_reference s i ghost : to_Zpos (word_245 (encoded_leaves s i ghost)) = Reference.v258 s i.
Proof. rewrite slice_245 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v258, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_246.
Lemma slice_246 v : word_246 v = take 1 (drop 50 (v 43)).
Proof.
 unfold word_246, closed_246, expr_246, word_of_eval.
 change (drop 2 (take 3 (word_238 v)) = take 1 (drop 50 (v 43))).
 rewrite slice_238.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_246.
Lemma slice_246_reference s i ghost : to_Zpos (word_246 (encoded_leaves s i ghost)) = Reference.v259 s i.
Proof. rewrite slice_246 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v259, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_247.
Lemma slice_247 v : word_247 v = take 1 (drop 49 (v 43)).
Proof.
 unfold word_247, closed_247, expr_247, word_of_eval.
 change (drop 1 (take 2 (word_238 v)) = take 1 (drop 49 (v 43))).
 rewrite slice_238.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_247.
Lemma slice_247_reference s i ghost : to_Zpos (word_247 (encoded_leaves s i ghost)) = Reference.v260 s i.
Proof. rewrite slice_247 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v260, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_254.
Lemma slice_254 v : word_254 v = take 8 (drop 40 (v 43)).
Proof.
 unfold word_254, closed_254, expr_254, word_of_eval.
 change (drop 8 (take 16 (word_217 v)) = take 8 (drop 40 (v 43))).
 rewrite slice_217.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_254.
Lemma slice_254_reference s i ghost : to_Zpos (word_254 (encoded_leaves s i ghost)) = Reference.v268 s i.
Proof. rewrite slice_254 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v268, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_255.
Lemma slice_255 v : word_255 v = take 8 (drop 32 (v 43)).
Proof.
 unfold word_255, closed_255, expr_255, word_of_eval.
 change (drop 0 (take 8 (word_217 v)) = take 8 (drop 32 (v 43))).
 rewrite slice_217.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_255.
Transparent word_257.
Lemma slice_257 v : word_257 v = take 4 (drop 44 (v 43)).
Proof.
 unfold word_257, closed_257, expr_257, word_of_eval.
 change (drop 4 (take 8 (word_254 v)) = take 4 (drop 44 (v 43))).
 rewrite slice_254.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_257.
Lemma slice_257_reference s i ghost : to_Zpos (word_257 (encoded_leaves s i ghost)) = Reference.v270 s i.
Proof. rewrite slice_257 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v270, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_258.
Lemma slice_258 v : word_258 v = take 4 (drop 40 (v 43)).
Proof.
 unfold word_258, closed_258, expr_258, word_of_eval.
 change (drop 0 (take 4 (word_254 v)) = take 4 (drop 40 (v 43))).
 rewrite slice_254.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_258.
Transparent word_260.
Lemma slice_260 v : word_260 v = take 1 (drop 47 (v 43)).
Proof.
 unfold word_260, closed_260, expr_260, word_of_eval.
 change (drop 3 (take 4 (word_257 v)) = take 1 (drop 47 (v 43))).
 rewrite slice_257.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_260.
Lemma slice_260_reference s i ghost : to_Zpos (word_260 (encoded_leaves s i ghost)) = Reference.v272 s i.
Proof. rewrite slice_260 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v272, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_261.
Lemma slice_261 v : word_261 v = take 1 (drop 46 (v 43)).
Proof.
 unfold word_261, closed_261, expr_261, word_of_eval.
 change (drop 2 (take 3 (word_257 v)) = take 1 (drop 46 (v 43))).
 rewrite slice_257.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_261.
Lemma slice_261_reference s i ghost : to_Zpos (word_261 (encoded_leaves s i ghost)) = Reference.v273 s i.
Proof. rewrite slice_261 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v273, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_262.
Lemma slice_262 v : word_262 v = take 1 (drop 45 (v 43)).
Proof.
 unfold word_262, closed_262, expr_262, word_of_eval.
 change (drop 1 (take 2 (word_257 v)) = take 1 (drop 45 (v 43))).
 rewrite slice_257.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_262.
Lemma slice_262_reference s i ghost : to_Zpos (word_262 (encoded_leaves s i ghost)) = Reference.v274 s i.
Proof. rewrite slice_262 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v274, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_265.
Lemma slice_265 v : word_265 v = take 1 (drop 43 (v 43)).
Proof.
 unfold word_265, closed_265, expr_265, word_of_eval.
 change (drop 3 (take 4 (word_258 v)) = take 1 (drop 43 (v 43))).
 rewrite slice_258.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_265.
Lemma slice_265_reference s i ghost : to_Zpos (word_265 (encoded_leaves s i ghost)) = Reference.v278 s i.
Proof. rewrite slice_265 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v278, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_266.
Lemma slice_266 v : word_266 v = take 1 (drop 42 (v 43)).
Proof.
 unfold word_266, closed_266, expr_266, word_of_eval.
 change (drop 2 (take 3 (word_258 v)) = take 1 (drop 42 (v 43))).
 rewrite slice_258.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_266.
Lemma slice_266_reference s i ghost : to_Zpos (word_266 (encoded_leaves s i ghost)) = Reference.v279 s i.
Proof. rewrite slice_266 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v279, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_267.
Lemma slice_267 v : word_267 v = take 1 (drop 41 (v 43)).
Proof.
 unfold word_267, closed_267, expr_267, word_of_eval.
 change (drop 1 (take 2 (word_258 v)) = take 1 (drop 41 (v 43))).
 rewrite slice_258.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_267.
Lemma slice_267_reference s i ghost : to_Zpos (word_267 (encoded_leaves s i ghost)) = Reference.v280 s i.
Proof. rewrite slice_267 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v280, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_272.
Lemma slice_272 v : word_272 v = take 4 (drop 36 (v 43)).
Proof.
 unfold word_272, closed_272, expr_272, word_of_eval.
 change (drop 4 (take 8 (word_255 v)) = take 4 (drop 36 (v 43))).
 rewrite slice_255.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_272.
Lemma slice_272_reference s i ghost : to_Zpos (word_272 (encoded_leaves s i ghost)) = Reference.v286 s i.
Proof. rewrite slice_272 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v286, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_273.
Lemma slice_273 v : word_273 v = take 4 (drop 32 (v 43)).
Proof.
 unfold word_273, closed_273, expr_273, word_of_eval.
 change (drop 0 (take 4 (word_255 v)) = take 4 (drop 32 (v 43))).
 rewrite slice_255.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_273.
Transparent word_275.
Lemma slice_275 v : word_275 v = take 1 (drop 39 (v 43)).
Proof.
 unfold word_275, closed_275, expr_275, word_of_eval.
 change (drop 3 (take 4 (word_272 v)) = take 1 (drop 39 (v 43))).
 rewrite slice_272.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_275.
Lemma slice_275_reference s i ghost : to_Zpos (word_275 (encoded_leaves s i ghost)) = Reference.v288 s i.
Proof. rewrite slice_275 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v288, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_276.
Lemma slice_276 v : word_276 v = take 1 (drop 38 (v 43)).
Proof.
 unfold word_276, closed_276, expr_276, word_of_eval.
 change (drop 2 (take 3 (word_272 v)) = take 1 (drop 38 (v 43))).
 rewrite slice_272.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_276.
Lemma slice_276_reference s i ghost : to_Zpos (word_276 (encoded_leaves s i ghost)) = Reference.v289 s i.
Proof. rewrite slice_276 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v289, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_277.
Lemma slice_277 v : word_277 v = take 1 (drop 37 (v 43)).
Proof.
 unfold word_277, closed_277, expr_277, word_of_eval.
 change (drop 1 (take 2 (word_272 v)) = take 1 (drop 37 (v 43))).
 rewrite slice_272.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_277.
Lemma slice_277_reference s i ghost : to_Zpos (word_277 (encoded_leaves s i ghost)) = Reference.v290 s i.
Proof. rewrite slice_277 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v290, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_280.
Lemma slice_280 v : word_280 v = take 1 (drop 35 (v 43)).
Proof.
 unfold word_280, closed_280, expr_280, word_of_eval.
 change (drop 3 (take 4 (word_273 v)) = take 1 (drop 35 (v 43))).
 rewrite slice_273.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_280.
Lemma slice_280_reference s i ghost : to_Zpos (word_280 (encoded_leaves s i ghost)) = Reference.v294 s i.
Proof. rewrite slice_280 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v294, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_281.
Lemma slice_281 v : word_281 v = take 1 (drop 34 (v 43)).
Proof.
 unfold word_281, closed_281, expr_281, word_of_eval.
 change (drop 2 (take 3 (word_273 v)) = take 1 (drop 34 (v 43))).
 rewrite slice_273.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_281.
Lemma slice_281_reference s i ghost : to_Zpos (word_281 (encoded_leaves s i ghost)) = Reference.v295 s i.
Proof. rewrite slice_281 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v295, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_282.
Lemma slice_282 v : word_282 v = take 1 (drop 33 (v 43)).
Proof.
 unfold word_282, closed_282, expr_282, word_of_eval.
 change (drop 1 (take 2 (word_273 v)) = take 1 (drop 33 (v 43))).
 rewrite slice_273.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_282.
Lemma slice_282_reference s i ghost : to_Zpos (word_282 (encoded_leaves s i ghost)) = Reference.v296 s i.
Proof. rewrite slice_282 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v296, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_291.
Lemma slice_291 v : word_291 v = take 16 (drop 16 (v 43)).
Proof.
 unfold word_291, closed_291, expr_291, word_of_eval.
 change (drop 16 (take 32 (word_214 v)) = take 16 (drop 16 (v 43))).
 rewrite slice_214.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_291.
Lemma slice_291_reference s i ghost : to_Zpos (word_291 (encoded_leaves s i ghost)) = Reference.v306 s i.
Proof. rewrite slice_291 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v306, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_292.
Lemma slice_292 v : word_292 v = take 16 (drop 0 (v 43)).
Proof.
 unfold word_292, closed_292, expr_292, word_of_eval.
 change (drop 0 (take 16 (word_214 v)) = take 16 (drop 0 (v 43))).
 rewrite slice_214.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_292.
Transparent word_294.
Lemma slice_294 v : word_294 v = take 8 (drop 24 (v 43)).
Proof.
 unfold word_294, closed_294, expr_294, word_of_eval.
 change (drop 8 (take 16 (word_291 v)) = take 8 (drop 24 (v 43))).
 rewrite slice_291.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_294.
Lemma slice_294_reference s i ghost : to_Zpos (word_294 (encoded_leaves s i ghost)) = Reference.v308 s i.
Proof. rewrite slice_294 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v308, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_295.
Lemma slice_295 v : word_295 v = take 8 (drop 16 (v 43)).
Proof.
 unfold word_295, closed_295, expr_295, word_of_eval.
 change (drop 0 (take 8 (word_291 v)) = take 8 (drop 16 (v 43))).
 rewrite slice_291.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_295.
Transparent word_297.
Lemma slice_297 v : word_297 v = take 4 (drop 28 (v 43)).
Proof.
 unfold word_297, closed_297, expr_297, word_of_eval.
 change (drop 4 (take 8 (word_294 v)) = take 4 (drop 28 (v 43))).
 rewrite slice_294.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_297.
Lemma slice_297_reference s i ghost : to_Zpos (word_297 (encoded_leaves s i ghost)) = Reference.v310 s i.
Proof. rewrite slice_297 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v310, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_298.
Lemma slice_298 v : word_298 v = take 4 (drop 24 (v 43)).
Proof.
 unfold word_298, closed_298, expr_298, word_of_eval.
 change (drop 0 (take 4 (word_294 v)) = take 4 (drop 24 (v 43))).
 rewrite slice_294.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_298.
Transparent word_300.
Lemma slice_300 v : word_300 v = take 1 (drop 31 (v 43)).
Proof.
 unfold word_300, closed_300, expr_300, word_of_eval.
 change (drop 3 (take 4 (word_297 v)) = take 1 (drop 31 (v 43))).
 rewrite slice_297.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_300.
Lemma slice_300_reference s i ghost : to_Zpos (word_300 (encoded_leaves s i ghost)) = Reference.v312 s i.
Proof. rewrite slice_300 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v312, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_301.
Lemma slice_301 v : word_301 v = take 1 (drop 30 (v 43)).
Proof.
 unfold word_301, closed_301, expr_301, word_of_eval.
 change (drop 2 (take 3 (word_297 v)) = take 1 (drop 30 (v 43))).
 rewrite slice_297.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_301.
Lemma slice_301_reference s i ghost : to_Zpos (word_301 (encoded_leaves s i ghost)) = Reference.v313 s i.
Proof. rewrite slice_301 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v313, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_302.
Lemma slice_302 v : word_302 v = take 1 (drop 29 (v 43)).
Proof.
 unfold word_302, closed_302, expr_302, word_of_eval.
 change (drop 1 (take 2 (word_297 v)) = take 1 (drop 29 (v 43))).
 rewrite slice_297.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_302.
Lemma slice_302_reference s i ghost : to_Zpos (word_302 (encoded_leaves s i ghost)) = Reference.v314 s i.
Proof. rewrite slice_302 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v314, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_305.
Lemma slice_305 v : word_305 v = take 1 (drop 27 (v 43)).
Proof.
 unfold word_305, closed_305, expr_305, word_of_eval.
 change (drop 3 (take 4 (word_298 v)) = take 1 (drop 27 (v 43))).
 rewrite slice_298.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_305.
Lemma slice_305_reference s i ghost : to_Zpos (word_305 (encoded_leaves s i ghost)) = Reference.v318 s i.
Proof. rewrite slice_305 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v318, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_306.
Lemma slice_306 v : word_306 v = take 1 (drop 26 (v 43)).
Proof.
 unfold word_306, closed_306, expr_306, word_of_eval.
 change (drop 2 (take 3 (word_298 v)) = take 1 (drop 26 (v 43))).
 rewrite slice_298.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_306.
Lemma slice_306_reference s i ghost : to_Zpos (word_306 (encoded_leaves s i ghost)) = Reference.v319 s i.
Proof. rewrite slice_306 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v319, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_307.
Lemma slice_307 v : word_307 v = take 1 (drop 25 (v 43)).
Proof.
 unfold word_307, closed_307, expr_307, word_of_eval.
 change (drop 1 (take 2 (word_298 v)) = take 1 (drop 25 (v 43))).
 rewrite slice_298.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_307.
Lemma slice_307_reference s i ghost : to_Zpos (word_307 (encoded_leaves s i ghost)) = Reference.v320 s i.
Proof. rewrite slice_307 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v320, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_312.
Lemma slice_312 v : word_312 v = take 4 (drop 20 (v 43)).
Proof.
 unfold word_312, closed_312, expr_312, word_of_eval.
 change (drop 4 (take 8 (word_295 v)) = take 4 (drop 20 (v 43))).
 rewrite slice_295.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_312.
Lemma slice_312_reference s i ghost : to_Zpos (word_312 (encoded_leaves s i ghost)) = Reference.v326 s i.
Proof. rewrite slice_312 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v326, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_313.
Lemma slice_313 v : word_313 v = take 4 (drop 16 (v 43)).
Proof.
 unfold word_313, closed_313, expr_313, word_of_eval.
 change (drop 0 (take 4 (word_295 v)) = take 4 (drop 16 (v 43))).
 rewrite slice_295.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_313.
Transparent word_315.
Lemma slice_315 v : word_315 v = take 1 (drop 23 (v 43)).
Proof.
 unfold word_315, closed_315, expr_315, word_of_eval.
 change (drop 3 (take 4 (word_312 v)) = take 1 (drop 23 (v 43))).
 rewrite slice_312.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_315.
Lemma slice_315_reference s i ghost : to_Zpos (word_315 (encoded_leaves s i ghost)) = Reference.v328 s i.
Proof. rewrite slice_315 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v328, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_316.
Lemma slice_316 v : word_316 v = take 1 (drop 22 (v 43)).
Proof.
 unfold word_316, closed_316, expr_316, word_of_eval.
 change (drop 2 (take 3 (word_312 v)) = take 1 (drop 22 (v 43))).
 rewrite slice_312.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_316.
Lemma slice_316_reference s i ghost : to_Zpos (word_316 (encoded_leaves s i ghost)) = Reference.v329 s i.
Proof. rewrite slice_316 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v329, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_317.
Lemma slice_317 v : word_317 v = take 1 (drop 21 (v 43)).
Proof.
 unfold word_317, closed_317, expr_317, word_of_eval.
 change (drop 1 (take 2 (word_312 v)) = take 1 (drop 21 (v 43))).
 rewrite slice_312.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_317.
Lemma slice_317_reference s i ghost : to_Zpos (word_317 (encoded_leaves s i ghost)) = Reference.v330 s i.
Proof. rewrite slice_317 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v330, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_320.
Lemma slice_320 v : word_320 v = take 1 (drop 19 (v 43)).
Proof.
 unfold word_320, closed_320, expr_320, word_of_eval.
 change (drop 3 (take 4 (word_313 v)) = take 1 (drop 19 (v 43))).
 rewrite slice_313.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_320.
Lemma slice_320_reference s i ghost : to_Zpos (word_320 (encoded_leaves s i ghost)) = Reference.v334 s i.
Proof. rewrite slice_320 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v334, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_321.
Lemma slice_321 v : word_321 v = take 1 (drop 18 (v 43)).
Proof.
 unfold word_321, closed_321, expr_321, word_of_eval.
 change (drop 2 (take 3 (word_313 v)) = take 1 (drop 18 (v 43))).
 rewrite slice_313.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_321.
Lemma slice_321_reference s i ghost : to_Zpos (word_321 (encoded_leaves s i ghost)) = Reference.v335 s i.
Proof. rewrite slice_321 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v335, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_322.
Lemma slice_322 v : word_322 v = take 1 (drop 17 (v 43)).
Proof.
 unfold word_322, closed_322, expr_322, word_of_eval.
 change (drop 1 (take 2 (word_313 v)) = take 1 (drop 17 (v 43))).
 rewrite slice_313.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_322.
Lemma slice_322_reference s i ghost : to_Zpos (word_322 (encoded_leaves s i ghost)) = Reference.v336 s i.
Proof. rewrite slice_322 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v336, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_329.
Lemma slice_329 v : word_329 v = take 8 (drop 8 (v 43)).
Proof.
 unfold word_329, closed_329, expr_329, word_of_eval.
 change (drop 8 (take 16 (word_292 v)) = take 8 (drop 8 (v 43))).
 rewrite slice_292.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_329.
Lemma slice_329_reference s i ghost : to_Zpos (word_329 (encoded_leaves s i ghost)) = Reference.v344 s i.
Proof. rewrite slice_329 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v344, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_330.
Lemma slice_330 v : word_330 v = take 8 (drop 0 (v 43)).
Proof.
 unfold word_330, closed_330, expr_330, word_of_eval.
 change (drop 0 (take 8 (word_292 v)) = take 8 (drop 0 (v 43))).
 rewrite slice_292.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_330.
Transparent word_332.
Lemma slice_332 v : word_332 v = take 4 (drop 12 (v 43)).
Proof.
 unfold word_332, closed_332, expr_332, word_of_eval.
 change (drop 4 (take 8 (word_329 v)) = take 4 (drop 12 (v 43))).
 rewrite slice_329.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_332.
Lemma slice_332_reference s i ghost : to_Zpos (word_332 (encoded_leaves s i ghost)) = Reference.v346 s i.
Proof. rewrite slice_332 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v346, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_333.
Lemma slice_333 v : word_333 v = take 4 (drop 8 (v 43)).
Proof.
 unfold word_333, closed_333, expr_333, word_of_eval.
 change (drop 0 (take 4 (word_329 v)) = take 4 (drop 8 (v 43))).
 rewrite slice_329.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_333.
Transparent word_335.
Lemma slice_335 v : word_335 v = take 1 (drop 15 (v 43)).
Proof.
 unfold word_335, closed_335, expr_335, word_of_eval.
 change (drop 3 (take 4 (word_332 v)) = take 1 (drop 15 (v 43))).
 rewrite slice_332.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_335.
Lemma slice_335_reference s i ghost : to_Zpos (word_335 (encoded_leaves s i ghost)) = Reference.v348 s i.
Proof. rewrite slice_335 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v348, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_336.
Lemma slice_336 v : word_336 v = take 1 (drop 14 (v 43)).
Proof.
 unfold word_336, closed_336, expr_336, word_of_eval.
 change (drop 2 (take 3 (word_332 v)) = take 1 (drop 14 (v 43))).
 rewrite slice_332.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_336.
Lemma slice_336_reference s i ghost : to_Zpos (word_336 (encoded_leaves s i ghost)) = Reference.v349 s i.
Proof. rewrite slice_336 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v349, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_337.
Lemma slice_337 v : word_337 v = take 1 (drop 13 (v 43)).
Proof.
 unfold word_337, closed_337, expr_337, word_of_eval.
 change (drop 1 (take 2 (word_332 v)) = take 1 (drop 13 (v 43))).
 rewrite slice_332.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_337.
Lemma slice_337_reference s i ghost : to_Zpos (word_337 (encoded_leaves s i ghost)) = Reference.v350 s i.
Proof. rewrite slice_337 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v350, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_340.
Lemma slice_340 v : word_340 v = take 1 (drop 11 (v 43)).
Proof.
 unfold word_340, closed_340, expr_340, word_of_eval.
 change (drop 3 (take 4 (word_333 v)) = take 1 (drop 11 (v 43))).
 rewrite slice_333.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_340.
Lemma slice_340_reference s i ghost : to_Zpos (word_340 (encoded_leaves s i ghost)) = Reference.v354 s i.
Proof. rewrite slice_340 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v354, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_341.
Lemma slice_341 v : word_341 v = take 1 (drop 10 (v 43)).
Proof.
 unfold word_341, closed_341, expr_341, word_of_eval.
 change (drop 2 (take 3 (word_333 v)) = take 1 (drop 10 (v 43))).
 rewrite slice_333.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_341.
Lemma slice_341_reference s i ghost : to_Zpos (word_341 (encoded_leaves s i ghost)) = Reference.v355 s i.
Proof. rewrite slice_341 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v355, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_342.
Lemma slice_342 v : word_342 v = take 1 (drop 9 (v 43)).
Proof.
 unfold word_342, closed_342, expr_342, word_of_eval.
 change (drop 1 (take 2 (word_333 v)) = take 1 (drop 9 (v 43))).
 rewrite slice_333.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_342.
Lemma slice_342_reference s i ghost : to_Zpos (word_342 (encoded_leaves s i ghost)) = Reference.v356 s i.
Proof. rewrite slice_342 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v356, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_347.
Lemma slice_347 v : word_347 v = take 4 (drop 4 (v 43)).
Proof.
 unfold word_347, closed_347, expr_347, word_of_eval.
 change (drop 4 (take 8 (word_330 v)) = take 4 (drop 4 (v 43))).
 rewrite slice_330.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_347.
Lemma slice_347_reference s i ghost : to_Zpos (word_347 (encoded_leaves s i ghost)) = Reference.v362 s i.
Proof. rewrite slice_347 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v362, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_348.
Lemma slice_348 v : word_348 v = take 4 (drop 0 (v 43)).
Proof.
 unfold word_348, closed_348, expr_348, word_of_eval.
 change (drop 0 (take 4 (word_330 v)) = take 4 (drop 0 (v 43))).
 rewrite slice_330.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_348.
Transparent word_350.
Lemma slice_350 v : word_350 v = take 1 (drop 7 (v 43)).
Proof.
 unfold word_350, closed_350, expr_350, word_of_eval.
 change (drop 3 (take 4 (word_347 v)) = take 1 (drop 7 (v 43))).
 rewrite slice_347.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_350.
Lemma slice_350_reference s i ghost : to_Zpos (word_350 (encoded_leaves s i ghost)) = Reference.v364 s i.
Proof. rewrite slice_350 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v364, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_351.
Lemma slice_351 v : word_351 v = take 1 (drop 6 (v 43)).
Proof.
 unfold word_351, closed_351, expr_351, word_of_eval.
 change (drop 2 (take 3 (word_347 v)) = take 1 (drop 6 (v 43))).
 rewrite slice_347.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_351.
Lemma slice_351_reference s i ghost : to_Zpos (word_351 (encoded_leaves s i ghost)) = Reference.v365 s i.
Proof. rewrite slice_351 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v365, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_352.
Lemma slice_352 v : word_352 v = take 1 (drop 5 (v 43)).
Proof.
 unfold word_352, closed_352, expr_352, word_of_eval.
 change (drop 1 (take 2 (word_347 v)) = take 1 (drop 5 (v 43))).
 rewrite slice_347.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_352.
Lemma slice_352_reference s i ghost : to_Zpos (word_352 (encoded_leaves s i ghost)) = Reference.v366 s i.
Proof. rewrite slice_352 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v366, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_355.
Lemma slice_355 v : word_355 v = take 1 (drop 3 (v 43)).
Proof.
 unfold word_355, closed_355, expr_355, word_of_eval.
 change (drop 3 (take 4 (word_348 v)) = take 1 (drop 3 (v 43))).
 rewrite slice_348.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_355.
Lemma slice_355_reference s i ghost : to_Zpos (word_355 (encoded_leaves s i ghost)) = Reference.v370 s i.
Proof. rewrite slice_355 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v370, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_356.
Lemma slice_356 v : word_356 v = take 1 (drop 2 (v 43)).
Proof.
 unfold word_356, closed_356, expr_356, word_of_eval.
 change (drop 2 (take 3 (word_348 v)) = take 1 (drop 2 (v 43))).
 rewrite slice_348.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_356.
Lemma slice_356_reference s i ghost : to_Zpos (word_356 (encoded_leaves s i ghost)) = Reference.v371 s i.
Proof. rewrite slice_356 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v371, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_357.
Lemma slice_357 v : word_357 v = take 1 (drop 1 (v 43)).
Proof.
 unfold word_357, closed_357, expr_357, word_of_eval.
 change (drop 1 (take 2 (word_348 v)) = take 1 (drop 1 (v 43))).
 rewrite slice_348.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_357.
Lemma slice_357_reference s i ghost : to_Zpos (word_357 (encoded_leaves s i ghost)) = Reference.v372 s i.
Proof. rewrite slice_357 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v372, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_405.
Lemma slice_405 v : word_405 v = take 64 (drop 65 (v 20)).
Proof.
 unfold word_405, closed_405, expr_405, word_of_eval.
 change (drop 1 (take 65 (word_21 v)) = take 64 (drop 65 (v 20))).
 rewrite slice_21.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_405.
Lemma slice_405_reference s i ghost : to_Zpos (word_405 (encoded_leaves s i ghost)) = Reference.v402 s i.
Proof. rewrite slice_405 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v402, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_422.
Lemma slice_422 v : word_422 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_422, closed_422, expr_422, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_422.
Opaque word_1.
Transparent word_425.
Lemma slice_425 v : word_425 v = take 64 (drop 1 (v 43)).
Proof.
 unfold word_425, closed_425, expr_425, word_of_eval.
 change (drop 1 (take 65 (word_43 v)) = take 64 (drop 1 (v 43))).
 Transparent word_43.
 unfold word_43.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_425.
Opaque word_43.
Lemma slice_425_reference s i ghost : to_Zpos (word_425 (encoded_leaves s i ghost)) = Reference.v417 s i.
Proof. rewrite slice_425 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v417, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_427.
Lemma slice_427 v : word_427 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_427, closed_427, expr_427, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_427.
Opaque word_1.
Transparent word_431.
Lemma slice_431 v : word_431 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_431, closed_431, expr_431, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_431.
Opaque word_1.
Transparent word_436.
Lemma slice_436 v : word_436 v = take 64 (drop 1 (v 43)).
Proof.
 unfold word_436, closed_436, expr_436, word_of_eval.
 change (drop 1 (take 65 (word_43 v)) = take 64 (drop 1 (v 43))).
 Transparent word_43.
 unfold word_43.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_436.
Opaque word_43.
Lemma slice_436_reference s i ghost : to_Zpos (word_436 (encoded_leaves s i ghost)) = Reference.v417 s i.
Proof. rewrite slice_436 unsigned_take unsigned_drop. unfold encoded_leaves. rewrite decode_encode.
 unfold Reference.v417, Radix2Divider.CIRCTBits.word, normalize, modulus. reflexivity. Qed.
Transparent word_438.
Lemma slice_438 v : word_438 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_438, closed_438, expr_438, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_438.
Opaque word_1.
Transparent word_442.
Lemma slice_442 v : word_442 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_442, closed_442, expr_442, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_442.
Opaque word_1.
Transparent word_450.
Lemma slice_450 v : word_450 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_450, closed_450, expr_450, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_450.
Opaque word_1.
Transparent word_455.
Lemma slice_455 v : word_455 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_455, closed_455, expr_455, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_455.
Opaque word_1.
Transparent word_462.
Lemma slice_462 v : word_462 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_462, closed_462, expr_462, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_462.
Opaque word_1.
Transparent word_470.
Lemma slice_470 v : word_470 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_470, closed_470, expr_470, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_470.
Opaque word_1.
Transparent word_477.
Lemma slice_477 v : word_477 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_477, closed_477, expr_477, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_477.
Opaque word_1.
Transparent word_481.
Lemma slice_481 v : word_481 v = take 1 (drop 0 (v 1)).
Proof.
 unfold word_481, closed_481, expr_481, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (v 1))).
 Transparent word_1.
 unfold word_1.
 rewrite !slice_drop_take ?drop_drop ?slice_take_take. reflexivity.
Qed.
Opaque word_481.
Opaque word_1.
Print Assumptions slice_53.
