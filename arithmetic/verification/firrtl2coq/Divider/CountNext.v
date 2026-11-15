From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing MuxShapes ScalarOps LeafWords ControlStart Controls ReferenceNormalization Commit.
Local Open Scope Z_scope.
Local Opaque Reference.v386 Reference.v388.
Lemma count_initial_reference s i ghost :
 normalize 6 (to_Zpos (word_374 (encoded_leaves s i ghost))) = Reference.v391 s i.
Proof.
 rewrite mux_integer_374 mux_integer_373 control_372_reference control_371_reference leaf_18_integer.
 unfold Reference.v391, Reference.v390, Reference.v389, Reference.v62, Reference.v9, Radix2Divider.CIRCTBits.word.
 rewrite Z.shiftr_0_r.
 change (normalize 6 (normalize 7 (if Z.eqb (normalize 1 (Reference.r1_ndivBy0Reg s)) 1 then 0 else
 normalize 7 (if Z.eqb (Reference.v388 s i) 1 then 63 else Reference.v386 s i))) =
 normalize 6 (if Z.eqb (normalize 1 (Reference.r1_ndivBy0Reg s)) 1 then 0 else
 normalize 6 (if Z.eqb (Reference.v388 s i) 1 then 63 else normalize 6 (Reference.v386 s i)))).
 destruct (Z.eqb (normalize 1 (Reference.r1_ndivBy0Reg s)) 1), (Z.eqb (Reference.v388 s i) 1);
 repeat (rewrite normalize_nested; [|lia]); reflexivity.
Qed.
Local Opaque Reference.v2 Reference.v4 Reference.v6 Reference.v8 Reference.v391 Reference.v395.
Lemma count_advance_reference s i ghost :
 normalize 6 (to_Zpos (word_398 (encoded_leaves s i ghost))) = Reference.v396 s i.
Proof.
 rewrite mux_integer_398 mux_integer_394 control_375_reference control_377_reference control_387_reference leaf_51_integer.
 unfold Reference.v396, Reference.v393, Reference.v392, Reference.v22, Radix2Divider.CIRCTBits.word.
 have A := normalize_range 1 (Reference.v6 s i).
 have B := normalize_range 1 (Reference.v8 s i).
 rewrite reference_6_normalized in A. rewrite reference_8_normalized in B.
 change (0 <= Reference.v6 s i < 2) in A. change (0 <= Reference.v8 s i < 2) in B.
 have A_cases : Reference.v6 s i = 0 \/ Reference.v6 s i = 1 by lia.
 have B_cases : Reference.v8 s i = 0 \/ Reference.v8 s i = 1 by lia.
 destruct A_cases as [A0|A1]; destruct B_cases as [B0|B1]; rewrite ?A0 ?A1 ?B0 ?B1.
 - change (normalize 6 (normalize 6 (normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s)))) = normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s))).
   repeat (rewrite normalize_nested; [|lia]); reflexivity.
 - change (normalize 6 (normalize 6 (normalize 6 (Reference.v395 s i))) = normalize 6 (Reference.v395 s i)).
   repeat (rewrite normalize_nested; [|lia]); reflexivity.
 - change (normalize 6 (normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s))) = normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s))).
   repeat (rewrite normalize_nested; [|lia]); reflexivity.
 - change (normalize 6 (normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s))) = normalize 6 (normalize 6 (Reference.r9_ncnt_5Fvalue s))).
   repeat (rewrite normalize_nested; [|lia]); reflexivity.
Qed.
Local Opaque Reference.v396.
Lemma count_select_reference s i ghost :
 normalize 6 (to_Zpos (word_399 (encoded_leaves s i ghost))) = Reference.v397 s i.
Proof.
 rewrite mux_integer_399 control_52_reference.
 unfold Reference.v397, Radix2Divider.CIRCTBits.word.
 change (normalize 6 (normalize 7 (if Z.eqb (Reference.v4 s i) 1 then to_Zpos (word_374 (encoded_leaves s i ghost)) else to_Zpos (word_398 (encoded_leaves s i ghost)))) =
 normalize 6 (if Z.eqb (Reference.v4 s i) 1 then Reference.v391 s i else Reference.v396 s i)).
 destruct (Z.eqb (Reference.v4 s i) 1);
 rewrite normalize_nested; [|lia| |lia];
 rewrite ?count_initial_reference ?count_advance_reference ?reference_391_normalized ?reference_396_normalized; reflexivity.
Qed.
Local Opaque Reference.v397.
Lemma count_403_reference s i ghost :
 normalize 6 (to_Zpos (word_403 (encoded_leaves s i ghost))) = Reference.v398 s i.
Proof.
 rewrite mux_integer_403 control_16_reference leaf_51_integer.
 unfold Reference.v398, Radix2Divider.CIRCTBits.word.
 change (normalize 6 (normalize 7 (if Z.eqb (Reference.v2 s i) 1 then normalize 6 (Reference.r9_ncnt_5Fvalue s) else to_Zpos (word_399 (encoded_leaves s i ghost)))) =
 normalize 6 (if Z.eqb (Reference.v2 s i) 1 then normalize 6 (Reference.r9_ncnt_5Fvalue s) else Reference.v397 s i)).
 destruct (Z.eqb (Reference.v2 s i) 1);
 repeat (rewrite normalize_nested; [|lia]); rewrite ?count_select_reference ?reference_397_normalized; reflexivity.
Qed.
Print Assumptions count_403_reference.
