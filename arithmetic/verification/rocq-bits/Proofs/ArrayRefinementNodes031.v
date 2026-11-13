(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes030.
Lemma node_31000 (s : N.State) (i : N.Inputs) :
  R.v31000 (state s) (inputs i) = Zmod.unsigned (N.v31000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31000 s i)) at 1.
  unfold R.v31000, N.v31000.
  unfold R.v6, N.v6.
  rewrite ?node_12564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31001 (s : N.State) (i : N.Inputs) :
  R.v31001 (state s) (inputs i) = Zmod.unsigned (N.v31001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31001 s i)) at 1.
  unfold R.v31001, N.v31001.
  rewrite ?node_30999.
  rewrite ?node_31000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31002 (s : N.State) (i : N.Inputs) :
  R.v31002 (state s) (inputs i) = Zmod.unsigned (N.v31002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31002 s i)) at 1.
  unfold R.v31002, N.v31002.
  rewrite ?node_30998.
  rewrite ?node_31001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31003 (s : N.State) (i : N.Inputs) :
  R.v31003 (state s) (inputs i) = Zmod.unsigned (N.v31003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31003 s i)) at 1.
  unfold R.v31003, N.v31003.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31004 (s : N.State) (i : N.Inputs) :
  R.v31004 (state s) (inputs i) = Zmod.unsigned (N.v31004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31004 s i)) at 1.
  unfold R.v31004, N.v31004.
  rewrite ?node_12429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31005 (s : N.State) (i : N.Inputs) :
  R.v31005 (state s) (inputs i) = Zmod.unsigned (N.v31005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31005 s i)) at 1.
  unfold R.v31005, N.v31005.
  unfold R.v6, N.v6.
  rewrite !state_r1565_nr_5F1570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1565_nr_5F1570 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31006 (s : N.State) (i : N.Inputs) :
  R.v31006 (state s) (inputs i) = Zmod.unsigned (N.v31006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31006 s i)) at 1.
  unfold R.v31006, N.v31006.
  unfold R.v6, N.v6.
  rewrite ?node_12425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31007 (s : N.State) (i : N.Inputs) :
  R.v31007 (state s) (inputs i) = Zmod.unsigned (N.v31007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31007 s i)) at 1.
  unfold R.v31007, N.v31007.
  rewrite ?node_31005.
  rewrite ?node_31006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31008 (s : N.State) (i : N.Inputs) :
  R.v31008 (state s) (inputs i) = Zmod.unsigned (N.v31008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31008 s i)) at 1.
  unfold R.v31008, N.v31008.
  unfold R.v16484, N.v16484.
  rewrite ?node_31007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31009 (s : N.State) (i : N.Inputs) :
  R.v31009 (state s) (inputs i) = Zmod.unsigned (N.v31009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31009 s i)) at 1.
  unfold R.v31009, N.v31009.
  rewrite ?node_31004.
  rewrite ?node_31008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31010 (s : N.State) (i : N.Inputs) :
  R.v31010 (state s) (inputs i) = Zmod.unsigned (N.v31010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31010 s i)) at 1.
  unfold R.v31010, N.v31010.
  unfold R.v6, N.v6.
  rewrite ?node_31009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31011 (s : N.State) (i : N.Inputs) :
  R.v31011 (state s) (inputs i) = Zmod.unsigned (N.v31011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31011 s i)) at 1.
  unfold R.v31011, N.v31011.
  rewrite ?node_12430.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31012 (s : N.State) (i : N.Inputs) :
  R.v31012 (state s) (inputs i) = Zmod.unsigned (N.v31012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31012 s i)) at 1.
  unfold R.v31012, N.v31012.
  unfold R.v6, N.v6.
  rewrite ?node_12607.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31013 (s : N.State) (i : N.Inputs) :
  R.v31013 (state s) (inputs i) = Zmod.unsigned (N.v31013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31013 s i)) at 1.
  unfold R.v31013, N.v31013.
  rewrite ?node_31011.
  rewrite ?node_31012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31014 (s : N.State) (i : N.Inputs) :
  R.v31014 (state s) (inputs i) = Zmod.unsigned (N.v31014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31014 s i)) at 1.
  unfold R.v31014, N.v31014.
  rewrite ?node_31010.
  rewrite ?node_31013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31015 (s : N.State) (i : N.Inputs) :
  R.v31015 (state s) (inputs i) = Zmod.unsigned (N.v31015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31015 s i)) at 1.
  unfold R.v31015, N.v31015.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31016 (s : N.State) (i : N.Inputs) :
  R.v31016 (state s) (inputs i) = Zmod.unsigned (N.v31016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31016 s i)) at 1.
  unfold R.v31016, N.v31016.
  rewrite ?node_12441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31017 (s : N.State) (i : N.Inputs) :
  R.v31017 (state s) (inputs i) = Zmod.unsigned (N.v31017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31017 s i)) at 1.
  unfold R.v31017, N.v31017.
  unfold R.v16463, N.v16463.
  rewrite !state_r1569_nr_5F1574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1569_nr_5F1574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31018 (s : N.State) (i : N.Inputs) :
  R.v31018 (state s) (inputs i) = Zmod.unsigned (N.v31018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31018 s i)) at 1.
  unfold R.v31018, N.v31018.
  unfold R.v16463, N.v16463.
  rewrite !state_r1568_nr_5F1573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1568_nr_5F1573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31019 (s : N.State) (i : N.Inputs) :
  R.v31019 (state s) (inputs i) = Zmod.unsigned (N.v31019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31019 s i)) at 1.
  unfold R.v31019, N.v31019.
  unfold R.v6, N.v6.
  rewrite !state_r1567_nr_5F1572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1567_nr_5F1572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31020 (s : N.State) (i : N.Inputs) :
  R.v31020 (state s) (inputs i) = Zmod.unsigned (N.v31020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31020 s i)) at 1.
  unfold R.v31020, N.v31020.
  unfold R.v6, N.v6.
  rewrite !state_r1566_nr_5F1571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1566_nr_5F1571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31021 (s : N.State) (i : N.Inputs) :
  R.v31021 (state s) (inputs i) = Zmod.unsigned (N.v31021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31021 s i)) at 1.
  unfold R.v31021, N.v31021.
  rewrite ?node_31019.
  rewrite ?node_31020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31022 (s : N.State) (i : N.Inputs) :
  R.v31022 (state s) (inputs i) = Zmod.unsigned (N.v31022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31022 s i)) at 1.
  unfold R.v31022, N.v31022.
  unfold R.v16484, N.v16484.
  rewrite ?node_31021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31023 (s : N.State) (i : N.Inputs) :
  R.v31023 (state s) (inputs i) = Zmod.unsigned (N.v31023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31023 s i)) at 1.
  unfold R.v31023, N.v31023.
  rewrite ?node_31016.
  rewrite ?node_31017.
  rewrite ?node_31018.
  rewrite ?node_31022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31024 (s : N.State) (i : N.Inputs) :
  R.v31024 (state s) (inputs i) = Zmod.unsigned (N.v31024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31024 s i)) at 1.
  unfold R.v31024, N.v31024.
  unfold R.v6, N.v6.
  rewrite ?node_31023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31025 (s : N.State) (i : N.Inputs) :
  R.v31025 (state s) (inputs i) = Zmod.unsigned (N.v31025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31025 s i)) at 1.
  unfold R.v31025, N.v31025.
  rewrite ?node_12442.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31026 (s : N.State) (i : N.Inputs) :
  R.v31026 (state s) (inputs i) = Zmod.unsigned (N.v31026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31026 s i)) at 1.
  unfold R.v31026, N.v31026.
  unfold R.v6, N.v6.
  rewrite ?node_12576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31027 (s : N.State) (i : N.Inputs) :
  R.v31027 (state s) (inputs i) = Zmod.unsigned (N.v31027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31027 s i)) at 1.
  unfold R.v31027, N.v31027.
  unfold R.v6, N.v6.
  rewrite ?node_12611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31028 (s : N.State) (i : N.Inputs) :
  R.v31028 (state s) (inputs i) = Zmod.unsigned (N.v31028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31028 s i)) at 1.
  unfold R.v31028, N.v31028.
  rewrite ?node_31025.
  rewrite ?node_31026.
  rewrite ?node_31027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31029 (s : N.State) (i : N.Inputs) :
  R.v31029 (state s) (inputs i) = Zmod.unsigned (N.v31029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31029 s i)) at 1.
  unfold R.v31029, N.v31029.
  rewrite ?node_31024.
  rewrite ?node_31028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31030 (s : N.State) (i : N.Inputs) :
  R.v31030 (state s) (inputs i) = Zmod.unsigned (N.v31030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31030 s i)) at 1.
  unfold R.v31030, N.v31030.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31031 (s : N.State) (i : N.Inputs) :
  R.v31031 (state s) (inputs i) = Zmod.unsigned (N.v31031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31031 s i)) at 1.
  unfold R.v31031, N.v31031.
  unfold R.v16463, N.v16463.
  rewrite !state_r1568_nr_5F1573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1568_nr_5F1573 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31032 (s : N.State) (i : N.Inputs) :
  R.v31032 (state s) (inputs i) = Zmod.unsigned (N.v31032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31032 s i)) at 1.
  unfold R.v31032, N.v31032.
  unfold R.v6, N.v6.
  rewrite !state_r1567_nr_5F1572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1567_nr_5F1572 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31033 (s : N.State) (i : N.Inputs) :
  R.v31033 (state s) (inputs i) = Zmod.unsigned (N.v31033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31033 s i)) at 1.
  unfold R.v31033, N.v31033.
  unfold R.v6, N.v6.
  rewrite !state_r1566_nr_5F1571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1566_nr_5F1571 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31034 (s : N.State) (i : N.Inputs) :
  R.v31034 (state s) (inputs i) = Zmod.unsigned (N.v31034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31034 s i)) at 1.
  unfold R.v31034, N.v31034.
  rewrite ?node_31032.
  rewrite ?node_31033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31035 (s : N.State) (i : N.Inputs) :
  R.v31035 (state s) (inputs i) = Zmod.unsigned (N.v31035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31035 s i)) at 1.
  unfold R.v31035, N.v31035.
  unfold R.v16484, N.v16484.
  rewrite ?node_31034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31036 (s : N.State) (i : N.Inputs) :
  R.v31036 (state s) (inputs i) = Zmod.unsigned (N.v31036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31036 s i)) at 1.
  unfold R.v31036, N.v31036.
  rewrite ?node_31031.
  rewrite ?node_31035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31037 (s : N.State) (i : N.Inputs) :
  R.v31037 (state s) (inputs i) = Zmod.unsigned (N.v31037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31037 s i)) at 1.
  unfold R.v31037, N.v31037.
  unfold R.v6, N.v6.
  rewrite ?node_31036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31038 (s : N.State) (i : N.Inputs) :
  R.v31038 (state s) (inputs i) = Zmod.unsigned (N.v31038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31038 s i)) at 1.
  unfold R.v31038, N.v31038.
  rewrite ?node_12437.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31039 (s : N.State) (i : N.Inputs) :
  R.v31039 (state s) (inputs i) = Zmod.unsigned (N.v31039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31039 s i)) at 1.
  unfold R.v31039, N.v31039.
  unfold R.v6, N.v6.
  rewrite ?node_12576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31040 (s : N.State) (i : N.Inputs) :
  R.v31040 (state s) (inputs i) = Zmod.unsigned (N.v31040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31040 s i)) at 1.
  unfold R.v31040, N.v31040.
  rewrite ?node_31038.
  rewrite ?node_31039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31041 (s : N.State) (i : N.Inputs) :
  R.v31041 (state s) (inputs i) = Zmod.unsigned (N.v31041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31041 s i)) at 1.
  unfold R.v31041, N.v31041.
  rewrite ?node_31037.
  rewrite ?node_31040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31042 (s : N.State) (i : N.Inputs) :
  R.v31042 (state s) (inputs i) = Zmod.unsigned (N.v31042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31042 s i)) at 1.
  unfold R.v31042, N.v31042.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31043 (s : N.State) (i : N.Inputs) :
  R.v31043 (state s) (inputs i) = Zmod.unsigned (N.v31043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31043 s i)) at 1.
  unfold R.v31043, N.v31043.
  rewrite ?node_12441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31044 (s : N.State) (i : N.Inputs) :
  R.v31044 (state s) (inputs i) = Zmod.unsigned (N.v31044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31044 s i)) at 1.
  unfold R.v31044, N.v31044.
  unfold R.v6, N.v6.
  rewrite !state_r1569_nr_5F1574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1569_nr_5F1574 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31045 (s : N.State) (i : N.Inputs) :
  R.v31045 (state s) (inputs i) = Zmod.unsigned (N.v31045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31045 s i)) at 1.
  unfold R.v31045, N.v31045.
  unfold R.v6, N.v6.
  rewrite ?node_12437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31046 (s : N.State) (i : N.Inputs) :
  R.v31046 (state s) (inputs i) = Zmod.unsigned (N.v31046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31046 s i)) at 1.
  unfold R.v31046, N.v31046.
  rewrite ?node_31044.
  rewrite ?node_31045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31047 (s : N.State) (i : N.Inputs) :
  R.v31047 (state s) (inputs i) = Zmod.unsigned (N.v31047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31047 s i)) at 1.
  unfold R.v31047, N.v31047.
  unfold R.v16484, N.v16484.
  rewrite ?node_31046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31048 (s : N.State) (i : N.Inputs) :
  R.v31048 (state s) (inputs i) = Zmod.unsigned (N.v31048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31048 s i)) at 1.
  unfold R.v31048, N.v31048.
  rewrite ?node_31043.
  rewrite ?node_31047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31049 (s : N.State) (i : N.Inputs) :
  R.v31049 (state s) (inputs i) = Zmod.unsigned (N.v31049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31049 s i)) at 1.
  unfold R.v31049, N.v31049.
  unfold R.v6, N.v6.
  rewrite ?node_31048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31050 (s : N.State) (i : N.Inputs) :
  R.v31050 (state s) (inputs i) = Zmod.unsigned (N.v31050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31050 s i)) at 1.
  unfold R.v31050, N.v31050.
  rewrite ?node_12442.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31051 (s : N.State) (i : N.Inputs) :
  R.v31051 (state s) (inputs i) = Zmod.unsigned (N.v31051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31051 s i)) at 1.
  unfold R.v31051, N.v31051.
  unfold R.v6, N.v6.
  rewrite ?node_12611.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31052 (s : N.State) (i : N.Inputs) :
  R.v31052 (state s) (inputs i) = Zmod.unsigned (N.v31052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31052 s i)) at 1.
  unfold R.v31052, N.v31052.
  rewrite ?node_31050.
  rewrite ?node_31051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31053 (s : N.State) (i : N.Inputs) :
  R.v31053 (state s) (inputs i) = Zmod.unsigned (N.v31053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31053 s i)) at 1.
  unfold R.v31053, N.v31053.
  rewrite ?node_31049.
  rewrite ?node_31052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31054 (s : N.State) (i : N.Inputs) :
  R.v31054 (state s) (inputs i) = Zmod.unsigned (N.v31054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31054 s i)) at 1.
  unfold R.v31054, N.v31054.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31055 (s : N.State) (i : N.Inputs) :
  R.v31055 (state s) (inputs i) = Zmod.unsigned (N.v31055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31055 s i)) at 1.
  unfold R.v31055, N.v31055.
  rewrite ?node_12448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31056 (s : N.State) (i : N.Inputs) :
  R.v31056 (state s) (inputs i) = Zmod.unsigned (N.v31056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31056 s i)) at 1.
  unfold R.v31056, N.v31056.
  unfold R.v16463, N.v16463.
  rewrite !state_r1573_nr_5F1578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1573_nr_5F1578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31057 (s : N.State) (i : N.Inputs) :
  R.v31057 (state s) (inputs i) = Zmod.unsigned (N.v31057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31057 s i)) at 1.
  unfold R.v31057, N.v31057.
  unfold R.v16463, N.v16463.
  rewrite !state_r1572_nr_5F1577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1572_nr_5F1577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31058 (s : N.State) (i : N.Inputs) :
  R.v31058 (state s) (inputs i) = Zmod.unsigned (N.v31058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31058 s i)) at 1.
  unfold R.v31058, N.v31058.
  unfold R.v6, N.v6.
  rewrite !state_r1571_nr_5F1576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1571_nr_5F1576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31059 (s : N.State) (i : N.Inputs) :
  R.v31059 (state s) (inputs i) = Zmod.unsigned (N.v31059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31059 s i)) at 1.
  unfold R.v31059, N.v31059.
  unfold R.v6, N.v6.
  rewrite !state_r1570_nr_5F1575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1570_nr_5F1575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31060 (s : N.State) (i : N.Inputs) :
  R.v31060 (state s) (inputs i) = Zmod.unsigned (N.v31060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31060 s i)) at 1.
  unfold R.v31060, N.v31060.
  rewrite ?node_31058.
  rewrite ?node_31059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31061 (s : N.State) (i : N.Inputs) :
  R.v31061 (state s) (inputs i) = Zmod.unsigned (N.v31061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31061 s i)) at 1.
  unfold R.v31061, N.v31061.
  unfold R.v16484, N.v16484.
  rewrite ?node_31060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31062 (s : N.State) (i : N.Inputs) :
  R.v31062 (state s) (inputs i) = Zmod.unsigned (N.v31062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31062 s i)) at 1.
  unfold R.v31062, N.v31062.
  rewrite ?node_31055.
  rewrite ?node_31056.
  rewrite ?node_31057.
  rewrite ?node_31061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31063 (s : N.State) (i : N.Inputs) :
  R.v31063 (state s) (inputs i) = Zmod.unsigned (N.v31063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31063 s i)) at 1.
  unfold R.v31063, N.v31063.
  unfold R.v6, N.v6.
  rewrite ?node_31062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31064 (s : N.State) (i : N.Inputs) :
  R.v31064 (state s) (inputs i) = Zmod.unsigned (N.v31064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31064 s i)) at 1.
  unfold R.v31064, N.v31064.
  rewrite ?node_12449.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31065 (s : N.State) (i : N.Inputs) :
  R.v31065 (state s) (inputs i) = Zmod.unsigned (N.v31065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31065 s i)) at 1.
  unfold R.v31065, N.v31065.
  unfold R.v6, N.v6.
  rewrite ?node_12583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31066 (s : N.State) (i : N.Inputs) :
  R.v31066 (state s) (inputs i) = Zmod.unsigned (N.v31066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31066 s i)) at 1.
  unfold R.v31066, N.v31066.
  unfold R.v6, N.v6.
  rewrite ?node_12620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31067 (s : N.State) (i : N.Inputs) :
  R.v31067 (state s) (inputs i) = Zmod.unsigned (N.v31067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31067 s i)) at 1.
  unfold R.v31067, N.v31067.
  rewrite ?node_31064.
  rewrite ?node_31065.
  rewrite ?node_31066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31068 (s : N.State) (i : N.Inputs) :
  R.v31068 (state s) (inputs i) = Zmod.unsigned (N.v31068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31068 s i)) at 1.
  unfold R.v31068, N.v31068.
  rewrite ?node_31063.
  rewrite ?node_31067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31069 (s : N.State) (i : N.Inputs) :
  R.v31069 (state s) (inputs i) = Zmod.unsigned (N.v31069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31069 s i)) at 1.
  unfold R.v31069, N.v31069.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31070 (s : N.State) (i : N.Inputs) :
  R.v31070 (state s) (inputs i) = Zmod.unsigned (N.v31070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31070 s i)) at 1.
  unfold R.v31070, N.v31070.
  unfold R.v16463, N.v16463.
  rewrite !state_r1572_nr_5F1577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1572_nr_5F1577 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31071 (s : N.State) (i : N.Inputs) :
  R.v31071 (state s) (inputs i) = Zmod.unsigned (N.v31071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31071 s i)) at 1.
  unfold R.v31071, N.v31071.
  unfold R.v6, N.v6.
  rewrite !state_r1571_nr_5F1576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1571_nr_5F1576 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31072 (s : N.State) (i : N.Inputs) :
  R.v31072 (state s) (inputs i) = Zmod.unsigned (N.v31072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31072 s i)) at 1.
  unfold R.v31072, N.v31072.
  unfold R.v6, N.v6.
  rewrite !state_r1570_nr_5F1575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1570_nr_5F1575 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31073 (s : N.State) (i : N.Inputs) :
  R.v31073 (state s) (inputs i) = Zmod.unsigned (N.v31073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31073 s i)) at 1.
  unfold R.v31073, N.v31073.
  rewrite ?node_31071.
  rewrite ?node_31072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31074 (s : N.State) (i : N.Inputs) :
  R.v31074 (state s) (inputs i) = Zmod.unsigned (N.v31074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31074 s i)) at 1.
  unfold R.v31074, N.v31074.
  unfold R.v16484, N.v16484.
  rewrite ?node_31073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31075 (s : N.State) (i : N.Inputs) :
  R.v31075 (state s) (inputs i) = Zmod.unsigned (N.v31075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31075 s i)) at 1.
  unfold R.v31075, N.v31075.
  rewrite ?node_31070.
  rewrite ?node_31074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31076 (s : N.State) (i : N.Inputs) :
  R.v31076 (state s) (inputs i) = Zmod.unsigned (N.v31076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31076 s i)) at 1.
  unfold R.v31076, N.v31076.
  unfold R.v6, N.v6.
  rewrite ?node_31075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31077 (s : N.State) (i : N.Inputs) :
  R.v31077 (state s) (inputs i) = Zmod.unsigned (N.v31077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31077 s i)) at 1.
  unfold R.v31077, N.v31077.
  rewrite ?node_12444.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31078 (s : N.State) (i : N.Inputs) :
  R.v31078 (state s) (inputs i) = Zmod.unsigned (N.v31078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31078 s i)) at 1.
  unfold R.v31078, N.v31078.
  unfold R.v6, N.v6.
  rewrite ?node_12583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31079 (s : N.State) (i : N.Inputs) :
  R.v31079 (state s) (inputs i) = Zmod.unsigned (N.v31079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31079 s i)) at 1.
  unfold R.v31079, N.v31079.
  rewrite ?node_31077.
  rewrite ?node_31078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31080 (s : N.State) (i : N.Inputs) :
  R.v31080 (state s) (inputs i) = Zmod.unsigned (N.v31080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31080 s i)) at 1.
  unfold R.v31080, N.v31080.
  rewrite ?node_31076.
  rewrite ?node_31079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31081 (s : N.State) (i : N.Inputs) :
  R.v31081 (state s) (inputs i) = Zmod.unsigned (N.v31081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31081 s i)) at 1.
  unfold R.v31081, N.v31081.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31082 (s : N.State) (i : N.Inputs) :
  R.v31082 (state s) (inputs i) = Zmod.unsigned (N.v31082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31082 s i)) at 1.
  unfold R.v31082, N.v31082.
  rewrite ?node_12448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31083 (s : N.State) (i : N.Inputs) :
  R.v31083 (state s) (inputs i) = Zmod.unsigned (N.v31083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31083 s i)) at 1.
  unfold R.v31083, N.v31083.
  unfold R.v6, N.v6.
  rewrite !state_r1573_nr_5F1578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1573_nr_5F1578 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31084 (s : N.State) (i : N.Inputs) :
  R.v31084 (state s) (inputs i) = Zmod.unsigned (N.v31084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31084 s i)) at 1.
  unfold R.v31084, N.v31084.
  unfold R.v6, N.v6.
  rewrite ?node_12444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31085 (s : N.State) (i : N.Inputs) :
  R.v31085 (state s) (inputs i) = Zmod.unsigned (N.v31085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31085 s i)) at 1.
  unfold R.v31085, N.v31085.
  rewrite ?node_31083.
  rewrite ?node_31084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31086 (s : N.State) (i : N.Inputs) :
  R.v31086 (state s) (inputs i) = Zmod.unsigned (N.v31086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31086 s i)) at 1.
  unfold R.v31086, N.v31086.
  unfold R.v16484, N.v16484.
  rewrite ?node_31085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31087 (s : N.State) (i : N.Inputs) :
  R.v31087 (state s) (inputs i) = Zmod.unsigned (N.v31087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31087 s i)) at 1.
  unfold R.v31087, N.v31087.
  rewrite ?node_31082.
  rewrite ?node_31086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31088 (s : N.State) (i : N.Inputs) :
  R.v31088 (state s) (inputs i) = Zmod.unsigned (N.v31088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31088 s i)) at 1.
  unfold R.v31088, N.v31088.
  unfold R.v6, N.v6.
  rewrite ?node_31087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31089 (s : N.State) (i : N.Inputs) :
  R.v31089 (state s) (inputs i) = Zmod.unsigned (N.v31089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31089 s i)) at 1.
  unfold R.v31089, N.v31089.
  rewrite ?node_12449.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31090 (s : N.State) (i : N.Inputs) :
  R.v31090 (state s) (inputs i) = Zmod.unsigned (N.v31090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31090 s i)) at 1.
  unfold R.v31090, N.v31090.
  unfold R.v6, N.v6.
  rewrite ?node_12620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31091 (s : N.State) (i : N.Inputs) :
  R.v31091 (state s) (inputs i) = Zmod.unsigned (N.v31091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31091 s i)) at 1.
  unfold R.v31091, N.v31091.
  rewrite ?node_31089.
  rewrite ?node_31090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31092 (s : N.State) (i : N.Inputs) :
  R.v31092 (state s) (inputs i) = Zmod.unsigned (N.v31092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31092 s i)) at 1.
  unfold R.v31092, N.v31092.
  rewrite ?node_31088.
  rewrite ?node_31091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31093 (s : N.State) (i : N.Inputs) :
  R.v31093 (state s) (inputs i) = Zmod.unsigned (N.v31093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31093 s i)) at 1.
  unfold R.v31093, N.v31093.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31094 (s : N.State) (i : N.Inputs) :
  R.v31094 (state s) (inputs i) = Zmod.unsigned (N.v31094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31094 s i)) at 1.
  unfold R.v31094, N.v31094.
  unfold R.v16463, N.v16463.
  rewrite !state_r1576_nr_5F1581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1576_nr_5F1581 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31095 (s : N.State) (i : N.Inputs) :
  R.v31095 (state s) (inputs i) = Zmod.unsigned (N.v31095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31095 s i)) at 1.
  unfold R.v31095, N.v31095.
  unfold R.v6, N.v6.
  rewrite !state_r1575_nr_5F1580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1575_nr_5F1580 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31096 (s : N.State) (i : N.Inputs) :
  R.v31096 (state s) (inputs i) = Zmod.unsigned (N.v31096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31096 s i)) at 1.
  unfold R.v31096, N.v31096.
  unfold R.v6, N.v6.
  rewrite !state_r1574_nr_5F1579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1574_nr_5F1579 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31097 (s : N.State) (i : N.Inputs) :
  R.v31097 (state s) (inputs i) = Zmod.unsigned (N.v31097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31097 s i)) at 1.
  unfold R.v31097, N.v31097.
  rewrite ?node_31095.
  rewrite ?node_31096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31098 (s : N.State) (i : N.Inputs) :
  R.v31098 (state s) (inputs i) = Zmod.unsigned (N.v31098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31098 s i)) at 1.
  unfold R.v31098, N.v31098.
  unfold R.v16484, N.v16484.
  rewrite ?node_31097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31099 (s : N.State) (i : N.Inputs) :
  R.v31099 (state s) (inputs i) = Zmod.unsigned (N.v31099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31099 s i)) at 1.
  unfold R.v31099, N.v31099.
  rewrite ?node_31094.
  rewrite ?node_31098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31100 (s : N.State) (i : N.Inputs) :
  R.v31100 (state s) (inputs i) = Zmod.unsigned (N.v31100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31100 s i)) at 1.
  unfold R.v31100, N.v31100.
  unfold R.v6, N.v6.
  rewrite ?node_31099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31101 (s : N.State) (i : N.Inputs) :
  R.v31101 (state s) (inputs i) = Zmod.unsigned (N.v31101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31101 s i)) at 1.
  unfold R.v31101, N.v31101.
  rewrite ?node_12452.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31102 (s : N.State) (i : N.Inputs) :
  R.v31102 (state s) (inputs i) = Zmod.unsigned (N.v31102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31102 s i)) at 1.
  unfold R.v31102, N.v31102.
  unfold R.v6, N.v6.
  rewrite ?node_12623.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31103 (s : N.State) (i : N.Inputs) :
  R.v31103 (state s) (inputs i) = Zmod.unsigned (N.v31103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31103 s i)) at 1.
  unfold R.v31103, N.v31103.
  rewrite ?node_31101.
  rewrite ?node_31102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31104 (s : N.State) (i : N.Inputs) :
  R.v31104 (state s) (inputs i) = Zmod.unsigned (N.v31104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31104 s i)) at 1.
  unfold R.v31104, N.v31104.
  rewrite ?node_31100.
  rewrite ?node_31103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31105 (s : N.State) (i : N.Inputs) :
  R.v31105 (state s) (inputs i) = Zmod.unsigned (N.v31105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31105 s i)) at 1.
  unfold R.v31105, N.v31105.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31106 (s : N.State) (i : N.Inputs) :
  R.v31106 (state s) (inputs i) = Zmod.unsigned (N.v31106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31106 s i)) at 1.
  unfold R.v31106, N.v31106.
  rewrite ?node_12541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31107 (s : N.State) (i : N.Inputs) :
  R.v31107 (state s) (inputs i) = Zmod.unsigned (N.v31107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31107 s i)) at 1.
  unfold R.v31107, N.v31107.
  unfold R.v16463, N.v16463.
  rewrite !state_r1579_nr_5F1585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1579_nr_5F1585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31108 (s : N.State) (i : N.Inputs) :
  R.v31108 (state s) (inputs i) = Zmod.unsigned (N.v31108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31108 s i)) at 1.
  unfold R.v31108, N.v31108.
  unfold R.v16463, N.v16463.
  rewrite !state_r1578_nr_5F1584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1578_nr_5F1584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31109 (s : N.State) (i : N.Inputs) :
  R.v31109 (state s) (inputs i) = Zmod.unsigned (N.v31109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31109 s i)) at 1.
  unfold R.v31109, N.v31109.
  unfold R.v6, N.v6.
  rewrite !state_r1577_nr_5F1583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1577_nr_5F1583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31110 (s : N.State) (i : N.Inputs) :
  R.v31110 (state s) (inputs i) = Zmod.unsigned (N.v31110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31110 s i)) at 1.
  unfold R.v31110, N.v31110.
  unfold R.v19, N.v19.
  rewrite ?node_31109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31111 (s : N.State) (i : N.Inputs) :
  R.v31111 (state s) (inputs i) = Zmod.unsigned (N.v31111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31111 s i)) at 1.
  unfold R.v31111, N.v31111.
  unfold R.v16484, N.v16484.
  rewrite ?node_31110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31112 (s : N.State) (i : N.Inputs) :
  R.v31112 (state s) (inputs i) = Zmod.unsigned (N.v31112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31112 s i)) at 1.
  unfold R.v31112, N.v31112.
  rewrite ?node_31106.
  rewrite ?node_31107.
  rewrite ?node_31108.
  rewrite ?node_31111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31113 (s : N.State) (i : N.Inputs) :
  R.v31113 (state s) (inputs i) = Zmod.unsigned (N.v31113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31113 s i)) at 1.
  unfold R.v31113, N.v31113.
  unfold R.v6, N.v6.
  rewrite ?node_31112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31114 (s : N.State) (i : N.Inputs) :
  R.v31114 (state s) (inputs i) = Zmod.unsigned (N.v31114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31114 s i)) at 1.
  unfold R.v31114, N.v31114.
  rewrite ?node_12542.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31115 (s : N.State) (i : N.Inputs) :
  R.v31115 (state s) (inputs i) = Zmod.unsigned (N.v31115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31115 s i)) at 1.
  unfold R.v31115, N.v31115.
  unfold R.v6, N.v6.
  rewrite ?node_12673.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31116 (s : N.State) (i : N.Inputs) :
  R.v31116 (state s) (inputs i) = Zmod.unsigned (N.v31116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31116 s i)) at 1.
  unfold R.v31116, N.v31116.
  unfold R.v6, N.v6.
  rewrite ?node_12722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31117 (s : N.State) (i : N.Inputs) :
  R.v31117 (state s) (inputs i) = Zmod.unsigned (N.v31117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31117 s i)) at 1.
  unfold R.v31117, N.v31117.
  rewrite ?node_31114.
  rewrite ?node_31115.
  rewrite ?node_31116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31118 (s : N.State) (i : N.Inputs) :
  R.v31118 (state s) (inputs i) = Zmod.unsigned (N.v31118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31118 s i)) at 1.
  unfold R.v31118, N.v31118.
  rewrite ?node_31113.
  rewrite ?node_31117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31119 (s : N.State) (i : N.Inputs) :
  R.v31119 (state s) (inputs i) = Zmod.unsigned (N.v31119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31119 s i)) at 1.
  unfold R.v31119, N.v31119.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31120 (s : N.State) (i : N.Inputs) :
  R.v31120 (state s) (inputs i) = Zmod.unsigned (N.v31120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31120 s i)) at 1.
  unfold R.v31120, N.v31120.
  unfold R.v16463, N.v16463.
  rewrite !state_r1578_nr_5F1584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1578_nr_5F1584 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31121 (s : N.State) (i : N.Inputs) :
  R.v31121 (state s) (inputs i) = Zmod.unsigned (N.v31121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31121 s i)) at 1.
  unfold R.v31121, N.v31121.
  unfold R.v6, N.v6.
  rewrite !state_r1577_nr_5F1583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1577_nr_5F1583 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31122 (s : N.State) (i : N.Inputs) :
  R.v31122 (state s) (inputs i) = Zmod.unsigned (N.v31122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31122 s i)) at 1.
  unfold R.v31122, N.v31122.
  unfold R.v19, N.v19.
  rewrite ?node_31121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31123 (s : N.State) (i : N.Inputs) :
  R.v31123 (state s) (inputs i) = Zmod.unsigned (N.v31123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31123 s i)) at 1.
  unfold R.v31123, N.v31123.
  unfold R.v16484, N.v16484.
  rewrite ?node_31122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31124 (s : N.State) (i : N.Inputs) :
  R.v31124 (state s) (inputs i) = Zmod.unsigned (N.v31124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31124 s i)) at 1.
  unfold R.v31124, N.v31124.
  rewrite ?node_31120.
  rewrite ?node_31123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31125 (s : N.State) (i : N.Inputs) :
  R.v31125 (state s) (inputs i) = Zmod.unsigned (N.v31125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31125 s i)) at 1.
  unfold R.v31125, N.v31125.
  unfold R.v6, N.v6.
  rewrite ?node_31124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31126 (s : N.State) (i : N.Inputs) :
  R.v31126 (state s) (inputs i) = Zmod.unsigned (N.v31126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31126 s i)) at 1.
  unfold R.v31126, N.v31126.
  rewrite ?node_12537.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31127 (s : N.State) (i : N.Inputs) :
  R.v31127 (state s) (inputs i) = Zmod.unsigned (N.v31127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31127 s i)) at 1.
  unfold R.v31127, N.v31127.
  unfold R.v6, N.v6.
  rewrite ?node_12673.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31128 (s : N.State) (i : N.Inputs) :
  R.v31128 (state s) (inputs i) = Zmod.unsigned (N.v31128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31128 s i)) at 1.
  unfold R.v31128, N.v31128.
  rewrite ?node_31126.
  rewrite ?node_31127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31129 (s : N.State) (i : N.Inputs) :
  R.v31129 (state s) (inputs i) = Zmod.unsigned (N.v31129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31129 s i)) at 1.
  unfold R.v31129, N.v31129.
  rewrite ?node_31125.
  rewrite ?node_31128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31130 (s : N.State) (i : N.Inputs) :
  R.v31130 (state s) (inputs i) = Zmod.unsigned (N.v31130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31130 s i)) at 1.
  unfold R.v31130, N.v31130.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31131 (s : N.State) (i : N.Inputs) :
  R.v31131 (state s) (inputs i) = Zmod.unsigned (N.v31131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31131 s i)) at 1.
  unfold R.v31131, N.v31131.
  rewrite ?node_12541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31132 (s : N.State) (i : N.Inputs) :
  R.v31132 (state s) (inputs i) = Zmod.unsigned (N.v31132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31132 s i)) at 1.
  unfold R.v31132, N.v31132.
  unfold R.v6, N.v6.
  rewrite !state_r1579_nr_5F1585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1579_nr_5F1585 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31133 (s : N.State) (i : N.Inputs) :
  R.v31133 (state s) (inputs i) = Zmod.unsigned (N.v31133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31133 s i)) at 1.
  unfold R.v31133, N.v31133.
  unfold R.v6, N.v6.
  rewrite ?node_12537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31134 (s : N.State) (i : N.Inputs) :
  R.v31134 (state s) (inputs i) = Zmod.unsigned (N.v31134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31134 s i)) at 1.
  unfold R.v31134, N.v31134.
  rewrite ?node_31132.
  rewrite ?node_31133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31135 (s : N.State) (i : N.Inputs) :
  R.v31135 (state s) (inputs i) = Zmod.unsigned (N.v31135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31135 s i)) at 1.
  unfold R.v31135, N.v31135.
  unfold R.v16484, N.v16484.
  rewrite ?node_31134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31136 (s : N.State) (i : N.Inputs) :
  R.v31136 (state s) (inputs i) = Zmod.unsigned (N.v31136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31136 s i)) at 1.
  unfold R.v31136, N.v31136.
  rewrite ?node_31131.
  rewrite ?node_31135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31137 (s : N.State) (i : N.Inputs) :
  R.v31137 (state s) (inputs i) = Zmod.unsigned (N.v31137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31137 s i)) at 1.
  unfold R.v31137, N.v31137.
  unfold R.v6, N.v6.
  rewrite ?node_31136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31138 (s : N.State) (i : N.Inputs) :
  R.v31138 (state s) (inputs i) = Zmod.unsigned (N.v31138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31138 s i)) at 1.
  unfold R.v31138, N.v31138.
  rewrite ?node_12542.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31139 (s : N.State) (i : N.Inputs) :
  R.v31139 (state s) (inputs i) = Zmod.unsigned (N.v31139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31139 s i)) at 1.
  unfold R.v31139, N.v31139.
  unfold R.v6, N.v6.
  rewrite ?node_12722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31140 (s : N.State) (i : N.Inputs) :
  R.v31140 (state s) (inputs i) = Zmod.unsigned (N.v31140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31140 s i)) at 1.
  unfold R.v31140, N.v31140.
  rewrite ?node_31138.
  rewrite ?node_31139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31141 (s : N.State) (i : N.Inputs) :
  R.v31141 (state s) (inputs i) = Zmod.unsigned (N.v31141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31141 s i)) at 1.
  unfold R.v31141, N.v31141.
  rewrite ?node_31137.
  rewrite ?node_31140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31142 (s : N.State) (i : N.Inputs) :
  R.v31142 (state s) (inputs i) = Zmod.unsigned (N.v31142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31142 s i)) at 1.
  unfold R.v31142, N.v31142.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31143 (s : N.State) (i : N.Inputs) :
  R.v31143 (state s) (inputs i) = Zmod.unsigned (N.v31143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31143 s i)) at 1.
  unfold R.v31143, N.v31143.
  rewrite ?node_12548.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31144 (s : N.State) (i : N.Inputs) :
  R.v31144 (state s) (inputs i) = Zmod.unsigned (N.v31144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31144 s i)) at 1.
  unfold R.v31144, N.v31144.
  unfold R.v16463, N.v16463.
  rewrite !state_r1583_nr_5F1589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1583_nr_5F1589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31145 (s : N.State) (i : N.Inputs) :
  R.v31145 (state s) (inputs i) = Zmod.unsigned (N.v31145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31145 s i)) at 1.
  unfold R.v31145, N.v31145.
  unfold R.v16463, N.v16463.
  rewrite !state_r1582_nr_5F1588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1582_nr_5F1588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31146 (s : N.State) (i : N.Inputs) :
  R.v31146 (state s) (inputs i) = Zmod.unsigned (N.v31146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31146 s i)) at 1.
  unfold R.v31146, N.v31146.
  unfold R.v6, N.v6.
  rewrite !state_r1581_nr_5F1587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1581_nr_5F1587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31147 (s : N.State) (i : N.Inputs) :
  R.v31147 (state s) (inputs i) = Zmod.unsigned (N.v31147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31147 s i)) at 1.
  unfold R.v31147, N.v31147.
  unfold R.v6, N.v6.
  rewrite !state_r1580_nr_5F1586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1580_nr_5F1586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31148 (s : N.State) (i : N.Inputs) :
  R.v31148 (state s) (inputs i) = Zmod.unsigned (N.v31148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31148 s i)) at 1.
  unfold R.v31148, N.v31148.
  rewrite ?node_31146.
  rewrite ?node_31147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31149 (s : N.State) (i : N.Inputs) :
  R.v31149 (state s) (inputs i) = Zmod.unsigned (N.v31149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31149 s i)) at 1.
  unfold R.v31149, N.v31149.
  unfold R.v16484, N.v16484.
  rewrite ?node_31148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31150 (s : N.State) (i : N.Inputs) :
  R.v31150 (state s) (inputs i) = Zmod.unsigned (N.v31150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31150 s i)) at 1.
  unfold R.v31150, N.v31150.
  rewrite ?node_31143.
  rewrite ?node_31144.
  rewrite ?node_31145.
  rewrite ?node_31149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31151 (s : N.State) (i : N.Inputs) :
  R.v31151 (state s) (inputs i) = Zmod.unsigned (N.v31151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31151 s i)) at 1.
  unfold R.v31151, N.v31151.
  unfold R.v6, N.v6.
  rewrite ?node_31150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31152 (s : N.State) (i : N.Inputs) :
  R.v31152 (state s) (inputs i) = Zmod.unsigned (N.v31152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31152 s i)) at 1.
  unfold R.v31152, N.v31152.
  rewrite ?node_12549.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31153 (s : N.State) (i : N.Inputs) :
  R.v31153 (state s) (inputs i) = Zmod.unsigned (N.v31153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31153 s i)) at 1.
  unfold R.v31153, N.v31153.
  unfold R.v6, N.v6.
  rewrite ?node_12680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31154 (s : N.State) (i : N.Inputs) :
  R.v31154 (state s) (inputs i) = Zmod.unsigned (N.v31154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31154 s i)) at 1.
  unfold R.v31154, N.v31154.
  unfold R.v6, N.v6.
  rewrite ?node_12731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31155 (s : N.State) (i : N.Inputs) :
  R.v31155 (state s) (inputs i) = Zmod.unsigned (N.v31155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31155 s i)) at 1.
  unfold R.v31155, N.v31155.
  rewrite ?node_31152.
  rewrite ?node_31153.
  rewrite ?node_31154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31156 (s : N.State) (i : N.Inputs) :
  R.v31156 (state s) (inputs i) = Zmod.unsigned (N.v31156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31156 s i)) at 1.
  unfold R.v31156, N.v31156.
  rewrite ?node_31151.
  rewrite ?node_31155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31157 (s : N.State) (i : N.Inputs) :
  R.v31157 (state s) (inputs i) = Zmod.unsigned (N.v31157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31157 s i)) at 1.
  unfold R.v31157, N.v31157.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31158 (s : N.State) (i : N.Inputs) :
  R.v31158 (state s) (inputs i) = Zmod.unsigned (N.v31158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31158 s i)) at 1.
  unfold R.v31158, N.v31158.
  unfold R.v16463, N.v16463.
  rewrite !state_r1582_nr_5F1588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1582_nr_5F1588 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31159 (s : N.State) (i : N.Inputs) :
  R.v31159 (state s) (inputs i) = Zmod.unsigned (N.v31159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31159 s i)) at 1.
  unfold R.v31159, N.v31159.
  unfold R.v6, N.v6.
  rewrite !state_r1581_nr_5F1587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1581_nr_5F1587 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31160 (s : N.State) (i : N.Inputs) :
  R.v31160 (state s) (inputs i) = Zmod.unsigned (N.v31160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31160 s i)) at 1.
  unfold R.v31160, N.v31160.
  unfold R.v6, N.v6.
  rewrite !state_r1580_nr_5F1586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1580_nr_5F1586 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31161 (s : N.State) (i : N.Inputs) :
  R.v31161 (state s) (inputs i) = Zmod.unsigned (N.v31161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31161 s i)) at 1.
  unfold R.v31161, N.v31161.
  rewrite ?node_31159.
  rewrite ?node_31160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31162 (s : N.State) (i : N.Inputs) :
  R.v31162 (state s) (inputs i) = Zmod.unsigned (N.v31162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31162 s i)) at 1.
  unfold R.v31162, N.v31162.
  unfold R.v16484, N.v16484.
  rewrite ?node_31161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31163 (s : N.State) (i : N.Inputs) :
  R.v31163 (state s) (inputs i) = Zmod.unsigned (N.v31163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31163 s i)) at 1.
  unfold R.v31163, N.v31163.
  rewrite ?node_31158.
  rewrite ?node_31162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31164 (s : N.State) (i : N.Inputs) :
  R.v31164 (state s) (inputs i) = Zmod.unsigned (N.v31164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31164 s i)) at 1.
  unfold R.v31164, N.v31164.
  unfold R.v6, N.v6.
  rewrite ?node_31163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31165 (s : N.State) (i : N.Inputs) :
  R.v31165 (state s) (inputs i) = Zmod.unsigned (N.v31165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31165 s i)) at 1.
  unfold R.v31165, N.v31165.
  rewrite ?node_12544.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31166 (s : N.State) (i : N.Inputs) :
  R.v31166 (state s) (inputs i) = Zmod.unsigned (N.v31166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31166 s i)) at 1.
  unfold R.v31166, N.v31166.
  unfold R.v6, N.v6.
  rewrite ?node_12680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31167 (s : N.State) (i : N.Inputs) :
  R.v31167 (state s) (inputs i) = Zmod.unsigned (N.v31167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31167 s i)) at 1.
  unfold R.v31167, N.v31167.
  rewrite ?node_31165.
  rewrite ?node_31166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31168 (s : N.State) (i : N.Inputs) :
  R.v31168 (state s) (inputs i) = Zmod.unsigned (N.v31168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31168 s i)) at 1.
  unfold R.v31168, N.v31168.
  rewrite ?node_31164.
  rewrite ?node_31167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31169 (s : N.State) (i : N.Inputs) :
  R.v31169 (state s) (inputs i) = Zmod.unsigned (N.v31169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31169 s i)) at 1.
  unfold R.v31169, N.v31169.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31170 (s : N.State) (i : N.Inputs) :
  R.v31170 (state s) (inputs i) = Zmod.unsigned (N.v31170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31170 s i)) at 1.
  unfold R.v31170, N.v31170.
  rewrite ?node_12548.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31171 (s : N.State) (i : N.Inputs) :
  R.v31171 (state s) (inputs i) = Zmod.unsigned (N.v31171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31171 s i)) at 1.
  unfold R.v31171, N.v31171.
  unfold R.v6, N.v6.
  rewrite !state_r1583_nr_5F1589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1583_nr_5F1589 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31172 (s : N.State) (i : N.Inputs) :
  R.v31172 (state s) (inputs i) = Zmod.unsigned (N.v31172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31172 s i)) at 1.
  unfold R.v31172, N.v31172.
  unfold R.v6, N.v6.
  rewrite ?node_12544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31173 (s : N.State) (i : N.Inputs) :
  R.v31173 (state s) (inputs i) = Zmod.unsigned (N.v31173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31173 s i)) at 1.
  unfold R.v31173, N.v31173.
  rewrite ?node_31171.
  rewrite ?node_31172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31174 (s : N.State) (i : N.Inputs) :
  R.v31174 (state s) (inputs i) = Zmod.unsigned (N.v31174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31174 s i)) at 1.
  unfold R.v31174, N.v31174.
  unfold R.v16484, N.v16484.
  rewrite ?node_31173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31175 (s : N.State) (i : N.Inputs) :
  R.v31175 (state s) (inputs i) = Zmod.unsigned (N.v31175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31175 s i)) at 1.
  unfold R.v31175, N.v31175.
  rewrite ?node_31170.
  rewrite ?node_31174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31176 (s : N.State) (i : N.Inputs) :
  R.v31176 (state s) (inputs i) = Zmod.unsigned (N.v31176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31176 s i)) at 1.
  unfold R.v31176, N.v31176.
  unfold R.v6, N.v6.
  rewrite ?node_31175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31177 (s : N.State) (i : N.Inputs) :
  R.v31177 (state s) (inputs i) = Zmod.unsigned (N.v31177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31177 s i)) at 1.
  unfold R.v31177, N.v31177.
  rewrite ?node_12549.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31178 (s : N.State) (i : N.Inputs) :
  R.v31178 (state s) (inputs i) = Zmod.unsigned (N.v31178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31178 s i)) at 1.
  unfold R.v31178, N.v31178.
  unfold R.v6, N.v6.
  rewrite ?node_12731.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31179 (s : N.State) (i : N.Inputs) :
  R.v31179 (state s) (inputs i) = Zmod.unsigned (N.v31179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31179 s i)) at 1.
  unfold R.v31179, N.v31179.
  rewrite ?node_31177.
  rewrite ?node_31178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31180 (s : N.State) (i : N.Inputs) :
  R.v31180 (state s) (inputs i) = Zmod.unsigned (N.v31180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31180 s i)) at 1.
  unfold R.v31180, N.v31180.
  rewrite ?node_31176.
  rewrite ?node_31179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31181 (s : N.State) (i : N.Inputs) :
  R.v31181 (state s) (inputs i) = Zmod.unsigned (N.v31181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31181 s i)) at 1.
  unfold R.v31181, N.v31181.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31182 (s : N.State) (i : N.Inputs) :
  R.v31182 (state s) (inputs i) = Zmod.unsigned (N.v31182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31182 s i)) at 1.
  unfold R.v31182, N.v31182.
  rewrite ?node_12556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31183 (s : N.State) (i : N.Inputs) :
  R.v31183 (state s) (inputs i) = Zmod.unsigned (N.v31183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31183 s i)) at 1.
  unfold R.v31183, N.v31183.
  unfold R.v16463, N.v16463.
  rewrite !state_r1587_nr_5F1593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1587_nr_5F1593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31184 (s : N.State) (i : N.Inputs) :
  R.v31184 (state s) (inputs i) = Zmod.unsigned (N.v31184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31184 s i)) at 1.
  unfold R.v31184, N.v31184.
  unfold R.v16463, N.v16463.
  rewrite !state_r1586_nr_5F1592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1586_nr_5F1592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31185 (s : N.State) (i : N.Inputs) :
  R.v31185 (state s) (inputs i) = Zmod.unsigned (N.v31185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31185 s i)) at 1.
  unfold R.v31185, N.v31185.
  unfold R.v6, N.v6.
  rewrite !state_r1585_nr_5F1591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1585_nr_5F1591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31186 (s : N.State) (i : N.Inputs) :
  R.v31186 (state s) (inputs i) = Zmod.unsigned (N.v31186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31186 s i)) at 1.
  unfold R.v31186, N.v31186.
  unfold R.v6, N.v6.
  rewrite !state_r1584_nr_5F1590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1584_nr_5F1590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31187 (s : N.State) (i : N.Inputs) :
  R.v31187 (state s) (inputs i) = Zmod.unsigned (N.v31187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31187 s i)) at 1.
  unfold R.v31187, N.v31187.
  rewrite ?node_31185.
  rewrite ?node_31186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31188 (s : N.State) (i : N.Inputs) :
  R.v31188 (state s) (inputs i) = Zmod.unsigned (N.v31188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31188 s i)) at 1.
  unfold R.v31188, N.v31188.
  unfold R.v16484, N.v16484.
  rewrite ?node_31187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31189 (s : N.State) (i : N.Inputs) :
  R.v31189 (state s) (inputs i) = Zmod.unsigned (N.v31189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31189 s i)) at 1.
  unfold R.v31189, N.v31189.
  rewrite ?node_31182.
  rewrite ?node_31183.
  rewrite ?node_31184.
  rewrite ?node_31188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31190 (s : N.State) (i : N.Inputs) :
  R.v31190 (state s) (inputs i) = Zmod.unsigned (N.v31190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31190 s i)) at 1.
  unfold R.v31190, N.v31190.
  unfold R.v6, N.v6.
  rewrite ?node_31189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31191 (s : N.State) (i : N.Inputs) :
  R.v31191 (state s) (inputs i) = Zmod.unsigned (N.v31191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31191 s i)) at 1.
  unfold R.v31191, N.v31191.
  rewrite ?node_12557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31192 (s : N.State) (i : N.Inputs) :
  R.v31192 (state s) (inputs i) = Zmod.unsigned (N.v31192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31192 s i)) at 1.
  unfold R.v31192, N.v31192.
  unfold R.v6, N.v6.
  rewrite ?node_12688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31193 (s : N.State) (i : N.Inputs) :
  R.v31193 (state s) (inputs i) = Zmod.unsigned (N.v31193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31193 s i)) at 1.
  unfold R.v31193, N.v31193.
  unfold R.v6, N.v6.
  rewrite ?node_12734.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31194 (s : N.State) (i : N.Inputs) :
  R.v31194 (state s) (inputs i) = Zmod.unsigned (N.v31194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31194 s i)) at 1.
  unfold R.v31194, N.v31194.
  rewrite ?node_31191.
  rewrite ?node_31192.
  rewrite ?node_31193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31195 (s : N.State) (i : N.Inputs) :
  R.v31195 (state s) (inputs i) = Zmod.unsigned (N.v31195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31195 s i)) at 1.
  unfold R.v31195, N.v31195.
  rewrite ?node_31190.
  rewrite ?node_31194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31196 (s : N.State) (i : N.Inputs) :
  R.v31196 (state s) (inputs i) = Zmod.unsigned (N.v31196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31196 s i)) at 1.
  unfold R.v31196, N.v31196.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31197 (s : N.State) (i : N.Inputs) :
  R.v31197 (state s) (inputs i) = Zmod.unsigned (N.v31197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31197 s i)) at 1.
  unfold R.v31197, N.v31197.
  unfold R.v16463, N.v16463.
  rewrite !state_r1586_nr_5F1592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1586_nr_5F1592 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31198 (s : N.State) (i : N.Inputs) :
  R.v31198 (state s) (inputs i) = Zmod.unsigned (N.v31198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31198 s i)) at 1.
  unfold R.v31198, N.v31198.
  unfold R.v6, N.v6.
  rewrite !state_r1585_nr_5F1591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1585_nr_5F1591 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31199 (s : N.State) (i : N.Inputs) :
  R.v31199 (state s) (inputs i) = Zmod.unsigned (N.v31199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31199 s i)) at 1.
  unfold R.v31199, N.v31199.
  unfold R.v6, N.v6.
  rewrite !state_r1584_nr_5F1590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1584_nr_5F1590 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31200 (s : N.State) (i : N.Inputs) :
  R.v31200 (state s) (inputs i) = Zmod.unsigned (N.v31200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31200 s i)) at 1.
  unfold R.v31200, N.v31200.
  rewrite ?node_31198.
  rewrite ?node_31199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31201 (s : N.State) (i : N.Inputs) :
  R.v31201 (state s) (inputs i) = Zmod.unsigned (N.v31201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31201 s i)) at 1.
  unfold R.v31201, N.v31201.
  unfold R.v16484, N.v16484.
  rewrite ?node_31200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31202 (s : N.State) (i : N.Inputs) :
  R.v31202 (state s) (inputs i) = Zmod.unsigned (N.v31202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31202 s i)) at 1.
  unfold R.v31202, N.v31202.
  rewrite ?node_31197.
  rewrite ?node_31201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31203 (s : N.State) (i : N.Inputs) :
  R.v31203 (state s) (inputs i) = Zmod.unsigned (N.v31203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31203 s i)) at 1.
  unfold R.v31203, N.v31203.
  unfold R.v6, N.v6.
  rewrite ?node_31202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31204 (s : N.State) (i : N.Inputs) :
  R.v31204 (state s) (inputs i) = Zmod.unsigned (N.v31204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31204 s i)) at 1.
  unfold R.v31204, N.v31204.
  rewrite ?node_12552.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31205 (s : N.State) (i : N.Inputs) :
  R.v31205 (state s) (inputs i) = Zmod.unsigned (N.v31205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31205 s i)) at 1.
  unfold R.v31205, N.v31205.
  unfold R.v6, N.v6.
  rewrite ?node_12688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31206 (s : N.State) (i : N.Inputs) :
  R.v31206 (state s) (inputs i) = Zmod.unsigned (N.v31206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31206 s i)) at 1.
  unfold R.v31206, N.v31206.
  rewrite ?node_31204.
  rewrite ?node_31205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31207 (s : N.State) (i : N.Inputs) :
  R.v31207 (state s) (inputs i) = Zmod.unsigned (N.v31207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31207 s i)) at 1.
  unfold R.v31207, N.v31207.
  rewrite ?node_31203.
  rewrite ?node_31206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31208 (s : N.State) (i : N.Inputs) :
  R.v31208 (state s) (inputs i) = Zmod.unsigned (N.v31208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31208 s i)) at 1.
  unfold R.v31208, N.v31208.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31209 (s : N.State) (i : N.Inputs) :
  R.v31209 (state s) (inputs i) = Zmod.unsigned (N.v31209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31209 s i)) at 1.
  unfold R.v31209, N.v31209.
  rewrite ?node_12556.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31210 (s : N.State) (i : N.Inputs) :
  R.v31210 (state s) (inputs i) = Zmod.unsigned (N.v31210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31210 s i)) at 1.
  unfold R.v31210, N.v31210.
  unfold R.v6, N.v6.
  rewrite !state_r1587_nr_5F1593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1587_nr_5F1593 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31211 (s : N.State) (i : N.Inputs) :
  R.v31211 (state s) (inputs i) = Zmod.unsigned (N.v31211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31211 s i)) at 1.
  unfold R.v31211, N.v31211.
  unfold R.v6, N.v6.
  rewrite ?node_12552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31212 (s : N.State) (i : N.Inputs) :
  R.v31212 (state s) (inputs i) = Zmod.unsigned (N.v31212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31212 s i)) at 1.
  unfold R.v31212, N.v31212.
  rewrite ?node_31210.
  rewrite ?node_31211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31213 (s : N.State) (i : N.Inputs) :
  R.v31213 (state s) (inputs i) = Zmod.unsigned (N.v31213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31213 s i)) at 1.
  unfold R.v31213, N.v31213.
  unfold R.v16484, N.v16484.
  rewrite ?node_31212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31214 (s : N.State) (i : N.Inputs) :
  R.v31214 (state s) (inputs i) = Zmod.unsigned (N.v31214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31214 s i)) at 1.
  unfold R.v31214, N.v31214.
  rewrite ?node_31209.
  rewrite ?node_31213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31215 (s : N.State) (i : N.Inputs) :
  R.v31215 (state s) (inputs i) = Zmod.unsigned (N.v31215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31215 s i)) at 1.
  unfold R.v31215, N.v31215.
  unfold R.v6, N.v6.
  rewrite ?node_31214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31216 (s : N.State) (i : N.Inputs) :
  R.v31216 (state s) (inputs i) = Zmod.unsigned (N.v31216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31216 s i)) at 1.
  unfold R.v31216, N.v31216.
  rewrite ?node_12557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31217 (s : N.State) (i : N.Inputs) :
  R.v31217 (state s) (inputs i) = Zmod.unsigned (N.v31217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31217 s i)) at 1.
  unfold R.v31217, N.v31217.
  unfold R.v6, N.v6.
  rewrite ?node_12734.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31218 (s : N.State) (i : N.Inputs) :
  R.v31218 (state s) (inputs i) = Zmod.unsigned (N.v31218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31218 s i)) at 1.
  unfold R.v31218, N.v31218.
  rewrite ?node_31216.
  rewrite ?node_31217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31219 (s : N.State) (i : N.Inputs) :
  R.v31219 (state s) (inputs i) = Zmod.unsigned (N.v31219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31219 s i)) at 1.
  unfold R.v31219, N.v31219.
  rewrite ?node_31215.
  rewrite ?node_31218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31220 (s : N.State) (i : N.Inputs) :
  R.v31220 (state s) (inputs i) = Zmod.unsigned (N.v31220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31220 s i)) at 1.
  unfold R.v31220, N.v31220.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31221 (s : N.State) (i : N.Inputs) :
  R.v31221 (state s) (inputs i) = Zmod.unsigned (N.v31221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31221 s i)) at 1.
  unfold R.v31221, N.v31221.
  rewrite ?node_12564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31222 (s : N.State) (i : N.Inputs) :
  R.v31222 (state s) (inputs i) = Zmod.unsigned (N.v31222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31222 s i)) at 1.
  unfold R.v31222, N.v31222.
  unfold R.v16463, N.v16463.
  rewrite !state_r1591_nr_5F1597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1591_nr_5F1597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31223 (s : N.State) (i : N.Inputs) :
  R.v31223 (state s) (inputs i) = Zmod.unsigned (N.v31223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31223 s i)) at 1.
  unfold R.v31223, N.v31223.
  unfold R.v16463, N.v16463.
  rewrite !state_r1590_nr_5F1596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1590_nr_5F1596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31224 (s : N.State) (i : N.Inputs) :
  R.v31224 (state s) (inputs i) = Zmod.unsigned (N.v31224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31224 s i)) at 1.
  unfold R.v31224, N.v31224.
  unfold R.v6, N.v6.
  rewrite !state_r1589_nr_5F1595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1589_nr_5F1595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31225 (s : N.State) (i : N.Inputs) :
  R.v31225 (state s) (inputs i) = Zmod.unsigned (N.v31225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31225 s i)) at 1.
  unfold R.v31225, N.v31225.
  unfold R.v6, N.v6.
  rewrite !state_r1588_nr_5F1594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1588_nr_5F1594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31226 (s : N.State) (i : N.Inputs) :
  R.v31226 (state s) (inputs i) = Zmod.unsigned (N.v31226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31226 s i)) at 1.
  unfold R.v31226, N.v31226.
  rewrite ?node_31224.
  rewrite ?node_31225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31227 (s : N.State) (i : N.Inputs) :
  R.v31227 (state s) (inputs i) = Zmod.unsigned (N.v31227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31227 s i)) at 1.
  unfold R.v31227, N.v31227.
  unfold R.v16484, N.v16484.
  rewrite ?node_31226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31228 (s : N.State) (i : N.Inputs) :
  R.v31228 (state s) (inputs i) = Zmod.unsigned (N.v31228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31228 s i)) at 1.
  unfold R.v31228, N.v31228.
  rewrite ?node_31221.
  rewrite ?node_31222.
  rewrite ?node_31223.
  rewrite ?node_31227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31229 (s : N.State) (i : N.Inputs) :
  R.v31229 (state s) (inputs i) = Zmod.unsigned (N.v31229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31229 s i)) at 1.
  unfold R.v31229, N.v31229.
  unfold R.v6, N.v6.
  rewrite ?node_31228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31230 (s : N.State) (i : N.Inputs) :
  R.v31230 (state s) (inputs i) = Zmod.unsigned (N.v31230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31230 s i)) at 1.
  unfold R.v31230, N.v31230.
  rewrite ?node_12565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31231 (s : N.State) (i : N.Inputs) :
  R.v31231 (state s) (inputs i) = Zmod.unsigned (N.v31231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31231 s i)) at 1.
  unfold R.v31231, N.v31231.
  unfold R.v6, N.v6.
  rewrite ?node_12696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31232 (s : N.State) (i : N.Inputs) :
  R.v31232 (state s) (inputs i) = Zmod.unsigned (N.v31232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31232 s i)) at 1.
  unfold R.v31232, N.v31232.
  unfold R.v6, N.v6.
  rewrite ?node_12738.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31233 (s : N.State) (i : N.Inputs) :
  R.v31233 (state s) (inputs i) = Zmod.unsigned (N.v31233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31233 s i)) at 1.
  unfold R.v31233, N.v31233.
  rewrite ?node_31230.
  rewrite ?node_31231.
  rewrite ?node_31232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31234 (s : N.State) (i : N.Inputs) :
  R.v31234 (state s) (inputs i) = Zmod.unsigned (N.v31234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31234 s i)) at 1.
  unfold R.v31234, N.v31234.
  rewrite ?node_31229.
  rewrite ?node_31233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31235 (s : N.State) (i : N.Inputs) :
  R.v31235 (state s) (inputs i) = Zmod.unsigned (N.v31235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31235 s i)) at 1.
  unfold R.v31235, N.v31235.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31236 (s : N.State) (i : N.Inputs) :
  R.v31236 (state s) (inputs i) = Zmod.unsigned (N.v31236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31236 s i)) at 1.
  unfold R.v31236, N.v31236.
  unfold R.v16463, N.v16463.
  rewrite !state_r1590_nr_5F1596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1590_nr_5F1596 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31237 (s : N.State) (i : N.Inputs) :
  R.v31237 (state s) (inputs i) = Zmod.unsigned (N.v31237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31237 s i)) at 1.
  unfold R.v31237, N.v31237.
  unfold R.v6, N.v6.
  rewrite !state_r1589_nr_5F1595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1589_nr_5F1595 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31238 (s : N.State) (i : N.Inputs) :
  R.v31238 (state s) (inputs i) = Zmod.unsigned (N.v31238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31238 s i)) at 1.
  unfold R.v31238, N.v31238.
  unfold R.v6, N.v6.
  rewrite !state_r1588_nr_5F1594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1588_nr_5F1594 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31239 (s : N.State) (i : N.Inputs) :
  R.v31239 (state s) (inputs i) = Zmod.unsigned (N.v31239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31239 s i)) at 1.
  unfold R.v31239, N.v31239.
  rewrite ?node_31237.
  rewrite ?node_31238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31240 (s : N.State) (i : N.Inputs) :
  R.v31240 (state s) (inputs i) = Zmod.unsigned (N.v31240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31240 s i)) at 1.
  unfold R.v31240, N.v31240.
  unfold R.v16484, N.v16484.
  rewrite ?node_31239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31241 (s : N.State) (i : N.Inputs) :
  R.v31241 (state s) (inputs i) = Zmod.unsigned (N.v31241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31241 s i)) at 1.
  unfold R.v31241, N.v31241.
  rewrite ?node_31236.
  rewrite ?node_31240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31242 (s : N.State) (i : N.Inputs) :
  R.v31242 (state s) (inputs i) = Zmod.unsigned (N.v31242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31242 s i)) at 1.
  unfold R.v31242, N.v31242.
  unfold R.v6, N.v6.
  rewrite ?node_31241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31243 (s : N.State) (i : N.Inputs) :
  R.v31243 (state s) (inputs i) = Zmod.unsigned (N.v31243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31243 s i)) at 1.
  unfold R.v31243, N.v31243.
  rewrite ?node_12560.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31244 (s : N.State) (i : N.Inputs) :
  R.v31244 (state s) (inputs i) = Zmod.unsigned (N.v31244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31244 s i)) at 1.
  unfold R.v31244, N.v31244.
  unfold R.v6, N.v6.
  rewrite ?node_12696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31245 (s : N.State) (i : N.Inputs) :
  R.v31245 (state s) (inputs i) = Zmod.unsigned (N.v31245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31245 s i)) at 1.
  unfold R.v31245, N.v31245.
  rewrite ?node_31243.
  rewrite ?node_31244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31246 (s : N.State) (i : N.Inputs) :
  R.v31246 (state s) (inputs i) = Zmod.unsigned (N.v31246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31246 s i)) at 1.
  unfold R.v31246, N.v31246.
  rewrite ?node_31242.
  rewrite ?node_31245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31247 (s : N.State) (i : N.Inputs) :
  R.v31247 (state s) (inputs i) = Zmod.unsigned (N.v31247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31247 s i)) at 1.
  unfold R.v31247, N.v31247.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31248 (s : N.State) (i : N.Inputs) :
  R.v31248 (state s) (inputs i) = Zmod.unsigned (N.v31248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31248 s i)) at 1.
  unfold R.v31248, N.v31248.
  rewrite ?node_12564.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31249 (s : N.State) (i : N.Inputs) :
  R.v31249 (state s) (inputs i) = Zmod.unsigned (N.v31249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31249 s i)) at 1.
  unfold R.v31249, N.v31249.
  unfold R.v6, N.v6.
  rewrite !state_r1591_nr_5F1597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1591_nr_5F1597 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31250 (s : N.State) (i : N.Inputs) :
  R.v31250 (state s) (inputs i) = Zmod.unsigned (N.v31250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31250 s i)) at 1.
  unfold R.v31250, N.v31250.
  unfold R.v6, N.v6.
  rewrite ?node_12560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31251 (s : N.State) (i : N.Inputs) :
  R.v31251 (state s) (inputs i) = Zmod.unsigned (N.v31251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31251 s i)) at 1.
  unfold R.v31251, N.v31251.
  rewrite ?node_31249.
  rewrite ?node_31250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31252 (s : N.State) (i : N.Inputs) :
  R.v31252 (state s) (inputs i) = Zmod.unsigned (N.v31252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31252 s i)) at 1.
  unfold R.v31252, N.v31252.
  unfold R.v16484, N.v16484.
  rewrite ?node_31251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31253 (s : N.State) (i : N.Inputs) :
  R.v31253 (state s) (inputs i) = Zmod.unsigned (N.v31253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31253 s i)) at 1.
  unfold R.v31253, N.v31253.
  rewrite ?node_31248.
  rewrite ?node_31252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31254 (s : N.State) (i : N.Inputs) :
  R.v31254 (state s) (inputs i) = Zmod.unsigned (N.v31254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31254 s i)) at 1.
  unfold R.v31254, N.v31254.
  unfold R.v6, N.v6.
  rewrite ?node_31253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31255 (s : N.State) (i : N.Inputs) :
  R.v31255 (state s) (inputs i) = Zmod.unsigned (N.v31255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31255 s i)) at 1.
  unfold R.v31255, N.v31255.
  rewrite ?node_12565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31256 (s : N.State) (i : N.Inputs) :
  R.v31256 (state s) (inputs i) = Zmod.unsigned (N.v31256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31256 s i)) at 1.
  unfold R.v31256, N.v31256.
  unfold R.v6, N.v6.
  rewrite ?node_12738.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31257 (s : N.State) (i : N.Inputs) :
  R.v31257 (state s) (inputs i) = Zmod.unsigned (N.v31257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31257 s i)) at 1.
  unfold R.v31257, N.v31257.
  rewrite ?node_31255.
  rewrite ?node_31256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31258 (s : N.State) (i : N.Inputs) :
  R.v31258 (state s) (inputs i) = Zmod.unsigned (N.v31258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31258 s i)) at 1.
  unfold R.v31258, N.v31258.
  rewrite ?node_31254.
  rewrite ?node_31257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31259 (s : N.State) (i : N.Inputs) :
  R.v31259 (state s) (inputs i) = Zmod.unsigned (N.v31259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31259 s i)) at 1.
  unfold R.v31259, N.v31259.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31260 (s : N.State) (i : N.Inputs) :
  R.v31260 (state s) (inputs i) = Zmod.unsigned (N.v31260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31260 s i)) at 1.
  unfold R.v31260, N.v31260.
  rewrite ?node_12576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31261 (s : N.State) (i : N.Inputs) :
  R.v31261 (state s) (inputs i) = Zmod.unsigned (N.v31261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31261 s i)) at 1.
  unfold R.v31261, N.v31261.
  unfold R.v16463, N.v16463.
  rewrite !state_r1595_nr_5F1601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1595_nr_5F1601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31262 (s : N.State) (i : N.Inputs) :
  R.v31262 (state s) (inputs i) = Zmod.unsigned (N.v31262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31262 s i)) at 1.
  unfold R.v31262, N.v31262.
  unfold R.v16463, N.v16463.
  rewrite !state_r1594_nr_5F1600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1594_nr_5F1600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31263 (s : N.State) (i : N.Inputs) :
  R.v31263 (state s) (inputs i) = Zmod.unsigned (N.v31263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31263 s i)) at 1.
  unfold R.v31263, N.v31263.
  unfold R.v6, N.v6.
  rewrite !state_r1593_nr_5F1599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1593_nr_5F1599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31264 (s : N.State) (i : N.Inputs) :
  R.v31264 (state s) (inputs i) = Zmod.unsigned (N.v31264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31264 s i)) at 1.
  unfold R.v31264, N.v31264.
  unfold R.v6, N.v6.
  rewrite !state_r1592_nr_5F1598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1592_nr_5F1598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31265 (s : N.State) (i : N.Inputs) :
  R.v31265 (state s) (inputs i) = Zmod.unsigned (N.v31265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31265 s i)) at 1.
  unfold R.v31265, N.v31265.
  rewrite ?node_31263.
  rewrite ?node_31264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31266 (s : N.State) (i : N.Inputs) :
  R.v31266 (state s) (inputs i) = Zmod.unsigned (N.v31266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31266 s i)) at 1.
  unfold R.v31266, N.v31266.
  unfold R.v16484, N.v16484.
  rewrite ?node_31265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31267 (s : N.State) (i : N.Inputs) :
  R.v31267 (state s) (inputs i) = Zmod.unsigned (N.v31267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31267 s i)) at 1.
  unfold R.v31267, N.v31267.
  rewrite ?node_31260.
  rewrite ?node_31261.
  rewrite ?node_31262.
  rewrite ?node_31266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31268 (s : N.State) (i : N.Inputs) :
  R.v31268 (state s) (inputs i) = Zmod.unsigned (N.v31268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31268 s i)) at 1.
  unfold R.v31268, N.v31268.
  unfold R.v6, N.v6.
  rewrite ?node_31267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31269 (s : N.State) (i : N.Inputs) :
  R.v31269 (state s) (inputs i) = Zmod.unsigned (N.v31269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31269 s i)) at 1.
  unfold R.v31269, N.v31269.
  rewrite ?node_12577.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31270 (s : N.State) (i : N.Inputs) :
  R.v31270 (state s) (inputs i) = Zmod.unsigned (N.v31270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31270 s i)) at 1.
  unfold R.v31270, N.v31270.
  unfold R.v6, N.v6.
  rewrite ?node_12708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31271 (s : N.State) (i : N.Inputs) :
  R.v31271 (state s) (inputs i) = Zmod.unsigned (N.v31271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31271 s i)) at 1.
  unfold R.v31271, N.v31271.
  unfold R.v6, N.v6.
  rewrite ?node_12742.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31272 (s : N.State) (i : N.Inputs) :
  R.v31272 (state s) (inputs i) = Zmod.unsigned (N.v31272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31272 s i)) at 1.
  unfold R.v31272, N.v31272.
  rewrite ?node_31269.
  rewrite ?node_31270.
  rewrite ?node_31271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31273 (s : N.State) (i : N.Inputs) :
  R.v31273 (state s) (inputs i) = Zmod.unsigned (N.v31273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31273 s i)) at 1.
  unfold R.v31273, N.v31273.
  rewrite ?node_31268.
  rewrite ?node_31272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31274 (s : N.State) (i : N.Inputs) :
  R.v31274 (state s) (inputs i) = Zmod.unsigned (N.v31274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31274 s i)) at 1.
  unfold R.v31274, N.v31274.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31275 (s : N.State) (i : N.Inputs) :
  R.v31275 (state s) (inputs i) = Zmod.unsigned (N.v31275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31275 s i)) at 1.
  unfold R.v31275, N.v31275.
  unfold R.v16463, N.v16463.
  rewrite !state_r1594_nr_5F1600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1594_nr_5F1600 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31276 (s : N.State) (i : N.Inputs) :
  R.v31276 (state s) (inputs i) = Zmod.unsigned (N.v31276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31276 s i)) at 1.
  unfold R.v31276, N.v31276.
  unfold R.v6, N.v6.
  rewrite !state_r1593_nr_5F1599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1593_nr_5F1599 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31277 (s : N.State) (i : N.Inputs) :
  R.v31277 (state s) (inputs i) = Zmod.unsigned (N.v31277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31277 s i)) at 1.
  unfold R.v31277, N.v31277.
  unfold R.v6, N.v6.
  rewrite !state_r1592_nr_5F1598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1592_nr_5F1598 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31278 (s : N.State) (i : N.Inputs) :
  R.v31278 (state s) (inputs i) = Zmod.unsigned (N.v31278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31278 s i)) at 1.
  unfold R.v31278, N.v31278.
  rewrite ?node_31276.
  rewrite ?node_31277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31279 (s : N.State) (i : N.Inputs) :
  R.v31279 (state s) (inputs i) = Zmod.unsigned (N.v31279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31279 s i)) at 1.
  unfold R.v31279, N.v31279.
  unfold R.v16484, N.v16484.
  rewrite ?node_31278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31280 (s : N.State) (i : N.Inputs) :
  R.v31280 (state s) (inputs i) = Zmod.unsigned (N.v31280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31280 s i)) at 1.
  unfold R.v31280, N.v31280.
  rewrite ?node_31275.
  rewrite ?node_31279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31281 (s : N.State) (i : N.Inputs) :
  R.v31281 (state s) (inputs i) = Zmod.unsigned (N.v31281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31281 s i)) at 1.
  unfold R.v31281, N.v31281.
  unfold R.v6, N.v6.
  rewrite ?node_31280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31282 (s : N.State) (i : N.Inputs) :
  R.v31282 (state s) (inputs i) = Zmod.unsigned (N.v31282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31282 s i)) at 1.
  unfold R.v31282, N.v31282.
  rewrite ?node_12572.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31283 (s : N.State) (i : N.Inputs) :
  R.v31283 (state s) (inputs i) = Zmod.unsigned (N.v31283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31283 s i)) at 1.
  unfold R.v31283, N.v31283.
  unfold R.v6, N.v6.
  rewrite ?node_12708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31284 (s : N.State) (i : N.Inputs) :
  R.v31284 (state s) (inputs i) = Zmod.unsigned (N.v31284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31284 s i)) at 1.
  unfold R.v31284, N.v31284.
  rewrite ?node_31282.
  rewrite ?node_31283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31285 (s : N.State) (i : N.Inputs) :
  R.v31285 (state s) (inputs i) = Zmod.unsigned (N.v31285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31285 s i)) at 1.
  unfold R.v31285, N.v31285.
  rewrite ?node_31281.
  rewrite ?node_31284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31286 (s : N.State) (i : N.Inputs) :
  R.v31286 (state s) (inputs i) = Zmod.unsigned (N.v31286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31286 s i)) at 1.
  unfold R.v31286, N.v31286.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31287 (s : N.State) (i : N.Inputs) :
  R.v31287 (state s) (inputs i) = Zmod.unsigned (N.v31287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31287 s i)) at 1.
  unfold R.v31287, N.v31287.
  rewrite ?node_12576.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31288 (s : N.State) (i : N.Inputs) :
  R.v31288 (state s) (inputs i) = Zmod.unsigned (N.v31288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31288 s i)) at 1.
  unfold R.v31288, N.v31288.
  unfold R.v6, N.v6.
  rewrite !state_r1595_nr_5F1601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1595_nr_5F1601 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31289 (s : N.State) (i : N.Inputs) :
  R.v31289 (state s) (inputs i) = Zmod.unsigned (N.v31289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31289 s i)) at 1.
  unfold R.v31289, N.v31289.
  unfold R.v6, N.v6.
  rewrite ?node_12572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31290 (s : N.State) (i : N.Inputs) :
  R.v31290 (state s) (inputs i) = Zmod.unsigned (N.v31290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31290 s i)) at 1.
  unfold R.v31290, N.v31290.
  rewrite ?node_31288.
  rewrite ?node_31289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31291 (s : N.State) (i : N.Inputs) :
  R.v31291 (state s) (inputs i) = Zmod.unsigned (N.v31291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31291 s i)) at 1.
  unfold R.v31291, N.v31291.
  unfold R.v16484, N.v16484.
  rewrite ?node_31290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31292 (s : N.State) (i : N.Inputs) :
  R.v31292 (state s) (inputs i) = Zmod.unsigned (N.v31292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31292 s i)) at 1.
  unfold R.v31292, N.v31292.
  rewrite ?node_31287.
  rewrite ?node_31291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31293 (s : N.State) (i : N.Inputs) :
  R.v31293 (state s) (inputs i) = Zmod.unsigned (N.v31293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31293 s i)) at 1.
  unfold R.v31293, N.v31293.
  unfold R.v6, N.v6.
  rewrite ?node_31292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31294 (s : N.State) (i : N.Inputs) :
  R.v31294 (state s) (inputs i) = Zmod.unsigned (N.v31294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31294 s i)) at 1.
  unfold R.v31294, N.v31294.
  rewrite ?node_12577.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31295 (s : N.State) (i : N.Inputs) :
  R.v31295 (state s) (inputs i) = Zmod.unsigned (N.v31295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31295 s i)) at 1.
  unfold R.v31295, N.v31295.
  unfold R.v6, N.v6.
  rewrite ?node_12742.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31296 (s : N.State) (i : N.Inputs) :
  R.v31296 (state s) (inputs i) = Zmod.unsigned (N.v31296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31296 s i)) at 1.
  unfold R.v31296, N.v31296.
  rewrite ?node_31294.
  rewrite ?node_31295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31297 (s : N.State) (i : N.Inputs) :
  R.v31297 (state s) (inputs i) = Zmod.unsigned (N.v31297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31297 s i)) at 1.
  unfold R.v31297, N.v31297.
  rewrite ?node_31293.
  rewrite ?node_31296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31298 (s : N.State) (i : N.Inputs) :
  R.v31298 (state s) (inputs i) = Zmod.unsigned (N.v31298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31298 s i)) at 1.
  unfold R.v31298, N.v31298.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31299 (s : N.State) (i : N.Inputs) :
  R.v31299 (state s) (inputs i) = Zmod.unsigned (N.v31299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31299 s i)) at 1.
  unfold R.v31299, N.v31299.
  rewrite ?node_12583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31300 (s : N.State) (i : N.Inputs) :
  R.v31300 (state s) (inputs i) = Zmod.unsigned (N.v31300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31300 s i)) at 1.
  unfold R.v31300, N.v31300.
  unfold R.v16463, N.v16463.
  rewrite !state_r1599_nr_5F1605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1599_nr_5F1605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31301 (s : N.State) (i : N.Inputs) :
  R.v31301 (state s) (inputs i) = Zmod.unsigned (N.v31301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31301 s i)) at 1.
  unfold R.v31301, N.v31301.
  unfold R.v16463, N.v16463.
  rewrite !state_r1598_nr_5F1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1598_nr_5F1604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31302 (s : N.State) (i : N.Inputs) :
  R.v31302 (state s) (inputs i) = Zmod.unsigned (N.v31302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31302 s i)) at 1.
  unfold R.v31302, N.v31302.
  unfold R.v6, N.v6.
  rewrite !state_r1597_nr_5F1603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1597_nr_5F1603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31303 (s : N.State) (i : N.Inputs) :
  R.v31303 (state s) (inputs i) = Zmod.unsigned (N.v31303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31303 s i)) at 1.
  unfold R.v31303, N.v31303.
  unfold R.v6, N.v6.
  rewrite !state_r1596_nr_5F1602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1596_nr_5F1602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31304 (s : N.State) (i : N.Inputs) :
  R.v31304 (state s) (inputs i) = Zmod.unsigned (N.v31304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31304 s i)) at 1.
  unfold R.v31304, N.v31304.
  rewrite ?node_31302.
  rewrite ?node_31303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31305 (s : N.State) (i : N.Inputs) :
  R.v31305 (state s) (inputs i) = Zmod.unsigned (N.v31305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31305 s i)) at 1.
  unfold R.v31305, N.v31305.
  unfold R.v16484, N.v16484.
  rewrite ?node_31304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31306 (s : N.State) (i : N.Inputs) :
  R.v31306 (state s) (inputs i) = Zmod.unsigned (N.v31306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31306 s i)) at 1.
  unfold R.v31306, N.v31306.
  rewrite ?node_31299.
  rewrite ?node_31300.
  rewrite ?node_31301.
  rewrite ?node_31305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31307 (s : N.State) (i : N.Inputs) :
  R.v31307 (state s) (inputs i) = Zmod.unsigned (N.v31307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31307 s i)) at 1.
  unfold R.v31307, N.v31307.
  unfold R.v6, N.v6.
  rewrite ?node_31306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31308 (s : N.State) (i : N.Inputs) :
  R.v31308 (state s) (inputs i) = Zmod.unsigned (N.v31308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31308 s i)) at 1.
  unfold R.v31308, N.v31308.
  rewrite ?node_12584.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31309 (s : N.State) (i : N.Inputs) :
  R.v31309 (state s) (inputs i) = Zmod.unsigned (N.v31309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31309 s i)) at 1.
  unfold R.v31309, N.v31309.
  unfold R.v6, N.v6.
  rewrite ?node_12715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31310 (s : N.State) (i : N.Inputs) :
  R.v31310 (state s) (inputs i) = Zmod.unsigned (N.v31310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31310 s i)) at 1.
  unfold R.v31310, N.v31310.
  unfold R.v6, N.v6.
  rewrite ?node_12751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31311 (s : N.State) (i : N.Inputs) :
  R.v31311 (state s) (inputs i) = Zmod.unsigned (N.v31311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31311 s i)) at 1.
  unfold R.v31311, N.v31311.
  rewrite ?node_31308.
  rewrite ?node_31309.
  rewrite ?node_31310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31312 (s : N.State) (i : N.Inputs) :
  R.v31312 (state s) (inputs i) = Zmod.unsigned (N.v31312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31312 s i)) at 1.
  unfold R.v31312, N.v31312.
  rewrite ?node_31307.
  rewrite ?node_31311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31313 (s : N.State) (i : N.Inputs) :
  R.v31313 (state s) (inputs i) = Zmod.unsigned (N.v31313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31313 s i)) at 1.
  unfold R.v31313, N.v31313.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31314 (s : N.State) (i : N.Inputs) :
  R.v31314 (state s) (inputs i) = Zmod.unsigned (N.v31314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31314 s i)) at 1.
  unfold R.v31314, N.v31314.
  unfold R.v16463, N.v16463.
  rewrite !state_r1598_nr_5F1604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1598_nr_5F1604 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31315 (s : N.State) (i : N.Inputs) :
  R.v31315 (state s) (inputs i) = Zmod.unsigned (N.v31315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31315 s i)) at 1.
  unfold R.v31315, N.v31315.
  unfold R.v6, N.v6.
  rewrite !state_r1597_nr_5F1603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1597_nr_5F1603 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31316 (s : N.State) (i : N.Inputs) :
  R.v31316 (state s) (inputs i) = Zmod.unsigned (N.v31316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31316 s i)) at 1.
  unfold R.v31316, N.v31316.
  unfold R.v6, N.v6.
  rewrite !state_r1596_nr_5F1602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1596_nr_5F1602 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31317 (s : N.State) (i : N.Inputs) :
  R.v31317 (state s) (inputs i) = Zmod.unsigned (N.v31317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31317 s i)) at 1.
  unfold R.v31317, N.v31317.
  rewrite ?node_31315.
  rewrite ?node_31316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31318 (s : N.State) (i : N.Inputs) :
  R.v31318 (state s) (inputs i) = Zmod.unsigned (N.v31318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31318 s i)) at 1.
  unfold R.v31318, N.v31318.
  unfold R.v16484, N.v16484.
  rewrite ?node_31317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31319 (s : N.State) (i : N.Inputs) :
  R.v31319 (state s) (inputs i) = Zmod.unsigned (N.v31319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31319 s i)) at 1.
  unfold R.v31319, N.v31319.
  rewrite ?node_31314.
  rewrite ?node_31318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31320 (s : N.State) (i : N.Inputs) :
  R.v31320 (state s) (inputs i) = Zmod.unsigned (N.v31320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31320 s i)) at 1.
  unfold R.v31320, N.v31320.
  unfold R.v6, N.v6.
  rewrite ?node_31319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31321 (s : N.State) (i : N.Inputs) :
  R.v31321 (state s) (inputs i) = Zmod.unsigned (N.v31321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31321 s i)) at 1.
  unfold R.v31321, N.v31321.
  rewrite ?node_12579.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31322 (s : N.State) (i : N.Inputs) :
  R.v31322 (state s) (inputs i) = Zmod.unsigned (N.v31322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31322 s i)) at 1.
  unfold R.v31322, N.v31322.
  unfold R.v6, N.v6.
  rewrite ?node_12715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31323 (s : N.State) (i : N.Inputs) :
  R.v31323 (state s) (inputs i) = Zmod.unsigned (N.v31323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31323 s i)) at 1.
  unfold R.v31323, N.v31323.
  rewrite ?node_31321.
  rewrite ?node_31322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31324 (s : N.State) (i : N.Inputs) :
  R.v31324 (state s) (inputs i) = Zmod.unsigned (N.v31324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31324 s i)) at 1.
  unfold R.v31324, N.v31324.
  rewrite ?node_31320.
  rewrite ?node_31323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31325 (s : N.State) (i : N.Inputs) :
  R.v31325 (state s) (inputs i) = Zmod.unsigned (N.v31325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31325 s i)) at 1.
  unfold R.v31325, N.v31325.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31326 (s : N.State) (i : N.Inputs) :
  R.v31326 (state s) (inputs i) = Zmod.unsigned (N.v31326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31326 s i)) at 1.
  unfold R.v31326, N.v31326.
  rewrite ?node_12583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31327 (s : N.State) (i : N.Inputs) :
  R.v31327 (state s) (inputs i) = Zmod.unsigned (N.v31327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31327 s i)) at 1.
  unfold R.v31327, N.v31327.
  unfold R.v6, N.v6.
  rewrite !state_r1599_nr_5F1605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1599_nr_5F1605 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31328 (s : N.State) (i : N.Inputs) :
  R.v31328 (state s) (inputs i) = Zmod.unsigned (N.v31328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31328 s i)) at 1.
  unfold R.v31328, N.v31328.
  unfold R.v6, N.v6.
  rewrite ?node_12579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31329 (s : N.State) (i : N.Inputs) :
  R.v31329 (state s) (inputs i) = Zmod.unsigned (N.v31329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31329 s i)) at 1.
  unfold R.v31329, N.v31329.
  rewrite ?node_31327.
  rewrite ?node_31328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31330 (s : N.State) (i : N.Inputs) :
  R.v31330 (state s) (inputs i) = Zmod.unsigned (N.v31330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31330 s i)) at 1.
  unfold R.v31330, N.v31330.
  unfold R.v16484, N.v16484.
  rewrite ?node_31329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31331 (s : N.State) (i : N.Inputs) :
  R.v31331 (state s) (inputs i) = Zmod.unsigned (N.v31331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31331 s i)) at 1.
  unfold R.v31331, N.v31331.
  rewrite ?node_31326.
  rewrite ?node_31330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31332 (s : N.State) (i : N.Inputs) :
  R.v31332 (state s) (inputs i) = Zmod.unsigned (N.v31332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31332 s i)) at 1.
  unfold R.v31332, N.v31332.
  unfold R.v6, N.v6.
  rewrite ?node_31331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31333 (s : N.State) (i : N.Inputs) :
  R.v31333 (state s) (inputs i) = Zmod.unsigned (N.v31333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31333 s i)) at 1.
  unfold R.v31333, N.v31333.
  rewrite ?node_12584.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31334 (s : N.State) (i : N.Inputs) :
  R.v31334 (state s) (inputs i) = Zmod.unsigned (N.v31334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31334 s i)) at 1.
  unfold R.v31334, N.v31334.
  unfold R.v6, N.v6.
  rewrite ?node_12751.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31335 (s : N.State) (i : N.Inputs) :
  R.v31335 (state s) (inputs i) = Zmod.unsigned (N.v31335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31335 s i)) at 1.
  unfold R.v31335, N.v31335.
  rewrite ?node_31333.
  rewrite ?node_31334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31336 (s : N.State) (i : N.Inputs) :
  R.v31336 (state s) (inputs i) = Zmod.unsigned (N.v31336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31336 s i)) at 1.
  unfold R.v31336, N.v31336.
  rewrite ?node_31332.
  rewrite ?node_31335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31337 (s : N.State) (i : N.Inputs) :
  R.v31337 (state s) (inputs i) = Zmod.unsigned (N.v31337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31337 s i)) at 1.
  unfold R.v31337, N.v31337.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31338 (s : N.State) (i : N.Inputs) :
  R.v31338 (state s) (inputs i) = Zmod.unsigned (N.v31338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31338 s i)) at 1.
  unfold R.v31338, N.v31338.
  unfold R.v16463, N.v16463.
  rewrite !state_r1602_nr_5F1608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1602_nr_5F1608 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31339 (s : N.State) (i : N.Inputs) :
  R.v31339 (state s) (inputs i) = Zmod.unsigned (N.v31339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31339 s i)) at 1.
  unfold R.v31339, N.v31339.
  unfold R.v6, N.v6.
  rewrite !state_r1601_nr_5F1607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1601_nr_5F1607 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31340 (s : N.State) (i : N.Inputs) :
  R.v31340 (state s) (inputs i) = Zmod.unsigned (N.v31340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31340 s i)) at 1.
  unfold R.v31340, N.v31340.
  unfold R.v6, N.v6.
  rewrite !state_r1600_nr_5F1606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1600_nr_5F1606 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31341 (s : N.State) (i : N.Inputs) :
  R.v31341 (state s) (inputs i) = Zmod.unsigned (N.v31341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31341 s i)) at 1.
  unfold R.v31341, N.v31341.
  rewrite ?node_31339.
  rewrite ?node_31340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31342 (s : N.State) (i : N.Inputs) :
  R.v31342 (state s) (inputs i) = Zmod.unsigned (N.v31342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31342 s i)) at 1.
  unfold R.v31342, N.v31342.
  unfold R.v16484, N.v16484.
  rewrite ?node_31341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31343 (s : N.State) (i : N.Inputs) :
  R.v31343 (state s) (inputs i) = Zmod.unsigned (N.v31343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31343 s i)) at 1.
  unfold R.v31343, N.v31343.
  rewrite ?node_31338.
  rewrite ?node_31342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31344 (s : N.State) (i : N.Inputs) :
  R.v31344 (state s) (inputs i) = Zmod.unsigned (N.v31344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31344 s i)) at 1.
  unfold R.v31344, N.v31344.
  unfold R.v6, N.v6.
  rewrite ?node_31343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31345 (s : N.State) (i : N.Inputs) :
  R.v31345 (state s) (inputs i) = Zmod.unsigned (N.v31345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31345 s i)) at 1.
  unfold R.v31345, N.v31345.
  rewrite ?node_12587.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31346 (s : N.State) (i : N.Inputs) :
  R.v31346 (state s) (inputs i) = Zmod.unsigned (N.v31346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31346 s i)) at 1.
  unfold R.v31346, N.v31346.
  unfold R.v6, N.v6.
  rewrite ?node_12754.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31347 (s : N.State) (i : N.Inputs) :
  R.v31347 (state s) (inputs i) = Zmod.unsigned (N.v31347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31347 s i)) at 1.
  unfold R.v31347, N.v31347.
  rewrite ?node_31345.
  rewrite ?node_31346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31348 (s : N.State) (i : N.Inputs) :
  R.v31348 (state s) (inputs i) = Zmod.unsigned (N.v31348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31348 s i)) at 1.
  unfold R.v31348, N.v31348.
  rewrite ?node_31344.
  rewrite ?node_31347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31349 (s : N.State) (i : N.Inputs) :
  R.v31349 (state s) (inputs i) = Zmod.unsigned (N.v31349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31349 s i)) at 1.
  unfold R.v31349, N.v31349.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31350 (s : N.State) (i : N.Inputs) :
  R.v31350 (state s) (inputs i) = Zmod.unsigned (N.v31350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31350 s i)) at 1.
  unfold R.v31350, N.v31350.
  rewrite ?node_12673.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31351 (s : N.State) (i : N.Inputs) :
  R.v31351 (state s) (inputs i) = Zmod.unsigned (N.v31351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31351 s i)) at 1.
  unfold R.v31351, N.v31351.
  unfold R.v16463, N.v16463.
  rewrite !state_r1606_nr_5F1612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1606_nr_5F1612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31352 (s : N.State) (i : N.Inputs) :
  R.v31352 (state s) (inputs i) = Zmod.unsigned (N.v31352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31352 s i)) at 1.
  unfold R.v31352, N.v31352.
  unfold R.v16463, N.v16463.
  rewrite !state_r1605_nr_5F1611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1605_nr_5F1611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31353 (s : N.State) (i : N.Inputs) :
  R.v31353 (state s) (inputs i) = Zmod.unsigned (N.v31353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31353 s i)) at 1.
  unfold R.v31353, N.v31353.
  unfold R.v6, N.v6.
  rewrite !state_r1604_nr_5F1610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1604_nr_5F1610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31354 (s : N.State) (i : N.Inputs) :
  R.v31354 (state s) (inputs i) = Zmod.unsigned (N.v31354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31354 s i)) at 1.
  unfold R.v31354, N.v31354.
  unfold R.v6, N.v6.
  rewrite !state_r1603_nr_5F1609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1603_nr_5F1609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31355 (s : N.State) (i : N.Inputs) :
  R.v31355 (state s) (inputs i) = Zmod.unsigned (N.v31355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31355 s i)) at 1.
  unfold R.v31355, N.v31355.
  rewrite ?node_31353.
  rewrite ?node_31354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31356 (s : N.State) (i : N.Inputs) :
  R.v31356 (state s) (inputs i) = Zmod.unsigned (N.v31356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31356 s i)) at 1.
  unfold R.v31356, N.v31356.
  unfold R.v16484, N.v16484.
  rewrite ?node_31355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31357 (s : N.State) (i : N.Inputs) :
  R.v31357 (state s) (inputs i) = Zmod.unsigned (N.v31357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31357 s i)) at 1.
  unfold R.v31357, N.v31357.
  rewrite ?node_31350.
  rewrite ?node_31351.
  rewrite ?node_31352.
  rewrite ?node_31356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31358 (s : N.State) (i : N.Inputs) :
  R.v31358 (state s) (inputs i) = Zmod.unsigned (N.v31358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31358 s i)) at 1.
  unfold R.v31358, N.v31358.
  unfold R.v6, N.v6.
  rewrite ?node_31357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31359 (s : N.State) (i : N.Inputs) :
  R.v31359 (state s) (inputs i) = Zmod.unsigned (N.v31359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31359 s i)) at 1.
  unfold R.v31359, N.v31359.
  rewrite ?node_12674.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31360 (s : N.State) (i : N.Inputs) :
  R.v31360 (state s) (inputs i) = Zmod.unsigned (N.v31360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31360 s i)) at 1.
  unfold R.v31360, N.v31360.
  unfold R.v6, N.v6.
  rewrite ?node_12803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31361 (s : N.State) (i : N.Inputs) :
  R.v31361 (state s) (inputs i) = Zmod.unsigned (N.v31361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31361 s i)) at 1.
  unfold R.v31361, N.v31361.
  unfold R.v6, N.v6.
  rewrite ?node_12852.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31362 (s : N.State) (i : N.Inputs) :
  R.v31362 (state s) (inputs i) = Zmod.unsigned (N.v31362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31362 s i)) at 1.
  unfold R.v31362, N.v31362.
  rewrite ?node_31359.
  rewrite ?node_31360.
  rewrite ?node_31361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31363 (s : N.State) (i : N.Inputs) :
  R.v31363 (state s) (inputs i) = Zmod.unsigned (N.v31363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31363 s i)) at 1.
  unfold R.v31363, N.v31363.
  rewrite ?node_31358.
  rewrite ?node_31362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31364 (s : N.State) (i : N.Inputs) :
  R.v31364 (state s) (inputs i) = Zmod.unsigned (N.v31364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31364 s i)) at 1.
  unfold R.v31364, N.v31364.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31365 (s : N.State) (i : N.Inputs) :
  R.v31365 (state s) (inputs i) = Zmod.unsigned (N.v31365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31365 s i)) at 1.
  unfold R.v31365, N.v31365.
  unfold R.v16463, N.v16463.
  rewrite !state_r1605_nr_5F1611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1605_nr_5F1611 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31366 (s : N.State) (i : N.Inputs) :
  R.v31366 (state s) (inputs i) = Zmod.unsigned (N.v31366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31366 s i)) at 1.
  unfold R.v31366, N.v31366.
  unfold R.v6, N.v6.
  rewrite !state_r1604_nr_5F1610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1604_nr_5F1610 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31367 (s : N.State) (i : N.Inputs) :
  R.v31367 (state s) (inputs i) = Zmod.unsigned (N.v31367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31367 s i)) at 1.
  unfold R.v31367, N.v31367.
  unfold R.v6, N.v6.
  rewrite !state_r1603_nr_5F1609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1603_nr_5F1609 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31368 (s : N.State) (i : N.Inputs) :
  R.v31368 (state s) (inputs i) = Zmod.unsigned (N.v31368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31368 s i)) at 1.
  unfold R.v31368, N.v31368.
  rewrite ?node_31366.
  rewrite ?node_31367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31369 (s : N.State) (i : N.Inputs) :
  R.v31369 (state s) (inputs i) = Zmod.unsigned (N.v31369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31369 s i)) at 1.
  unfold R.v31369, N.v31369.
  unfold R.v16484, N.v16484.
  rewrite ?node_31368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31370 (s : N.State) (i : N.Inputs) :
  R.v31370 (state s) (inputs i) = Zmod.unsigned (N.v31370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31370 s i)) at 1.
  unfold R.v31370, N.v31370.
  rewrite ?node_31365.
  rewrite ?node_31369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31371 (s : N.State) (i : N.Inputs) :
  R.v31371 (state s) (inputs i) = Zmod.unsigned (N.v31371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31371 s i)) at 1.
  unfold R.v31371, N.v31371.
  unfold R.v6, N.v6.
  rewrite ?node_31370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31372 (s : N.State) (i : N.Inputs) :
  R.v31372 (state s) (inputs i) = Zmod.unsigned (N.v31372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31372 s i)) at 1.
  unfold R.v31372, N.v31372.
  rewrite ?node_12670.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31373 (s : N.State) (i : N.Inputs) :
  R.v31373 (state s) (inputs i) = Zmod.unsigned (N.v31373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31373 s i)) at 1.
  unfold R.v31373, N.v31373.
  unfold R.v6, N.v6.
  rewrite ?node_12803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31374 (s : N.State) (i : N.Inputs) :
  R.v31374 (state s) (inputs i) = Zmod.unsigned (N.v31374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31374 s i)) at 1.
  unfold R.v31374, N.v31374.
  rewrite ?node_31372.
  rewrite ?node_31373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31375 (s : N.State) (i : N.Inputs) :
  R.v31375 (state s) (inputs i) = Zmod.unsigned (N.v31375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31375 s i)) at 1.
  unfold R.v31375, N.v31375.
  rewrite ?node_31371.
  rewrite ?node_31374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31376 (s : N.State) (i : N.Inputs) :
  R.v31376 (state s) (inputs i) = Zmod.unsigned (N.v31376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31376 s i)) at 1.
  unfold R.v31376, N.v31376.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31377 (s : N.State) (i : N.Inputs) :
  R.v31377 (state s) (inputs i) = Zmod.unsigned (N.v31377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31377 s i)) at 1.
  unfold R.v31377, N.v31377.
  rewrite ?node_12673.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31378 (s : N.State) (i : N.Inputs) :
  R.v31378 (state s) (inputs i) = Zmod.unsigned (N.v31378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31378 s i)) at 1.
  unfold R.v31378, N.v31378.
  unfold R.v6, N.v6.
  rewrite !state_r1606_nr_5F1612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1606_nr_5F1612 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31379 (s : N.State) (i : N.Inputs) :
  R.v31379 (state s) (inputs i) = Zmod.unsigned (N.v31379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31379 s i)) at 1.
  unfold R.v31379, N.v31379.
  unfold R.v6, N.v6.
  rewrite ?node_12670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31380 (s : N.State) (i : N.Inputs) :
  R.v31380 (state s) (inputs i) = Zmod.unsigned (N.v31380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31380 s i)) at 1.
  unfold R.v31380, N.v31380.
  rewrite ?node_31378.
  rewrite ?node_31379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31381 (s : N.State) (i : N.Inputs) :
  R.v31381 (state s) (inputs i) = Zmod.unsigned (N.v31381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31381 s i)) at 1.
  unfold R.v31381, N.v31381.
  unfold R.v16484, N.v16484.
  rewrite ?node_31380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31382 (s : N.State) (i : N.Inputs) :
  R.v31382 (state s) (inputs i) = Zmod.unsigned (N.v31382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31382 s i)) at 1.
  unfold R.v31382, N.v31382.
  rewrite ?node_31377.
  rewrite ?node_31381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31383 (s : N.State) (i : N.Inputs) :
  R.v31383 (state s) (inputs i) = Zmod.unsigned (N.v31383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31383 s i)) at 1.
  unfold R.v31383, N.v31383.
  unfold R.v6, N.v6.
  rewrite ?node_31382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31384 (s : N.State) (i : N.Inputs) :
  R.v31384 (state s) (inputs i) = Zmod.unsigned (N.v31384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31384 s i)) at 1.
  unfold R.v31384, N.v31384.
  rewrite ?node_12674.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31385 (s : N.State) (i : N.Inputs) :
  R.v31385 (state s) (inputs i) = Zmod.unsigned (N.v31385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31385 s i)) at 1.
  unfold R.v31385, N.v31385.
  unfold R.v6, N.v6.
  rewrite ?node_12852.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31386 (s : N.State) (i : N.Inputs) :
  R.v31386 (state s) (inputs i) = Zmod.unsigned (N.v31386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31386 s i)) at 1.
  unfold R.v31386, N.v31386.
  rewrite ?node_31384.
  rewrite ?node_31385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31387 (s : N.State) (i : N.Inputs) :
  R.v31387 (state s) (inputs i) = Zmod.unsigned (N.v31387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31387 s i)) at 1.
  unfold R.v31387, N.v31387.
  rewrite ?node_31383.
  rewrite ?node_31386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31388 (s : N.State) (i : N.Inputs) :
  R.v31388 (state s) (inputs i) = Zmod.unsigned (N.v31388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31388 s i)) at 1.
  unfold R.v31388, N.v31388.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31389 (s : N.State) (i : N.Inputs) :
  R.v31389 (state s) (inputs i) = Zmod.unsigned (N.v31389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31389 s i)) at 1.
  unfold R.v31389, N.v31389.
  rewrite ?node_12680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31390 (s : N.State) (i : N.Inputs) :
  R.v31390 (state s) (inputs i) = Zmod.unsigned (N.v31390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31390 s i)) at 1.
  unfold R.v31390, N.v31390.
  unfold R.v16463, N.v16463.
  rewrite !state_r1610_nr_5F1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1610_nr_5F1616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31391 (s : N.State) (i : N.Inputs) :
  R.v31391 (state s) (inputs i) = Zmod.unsigned (N.v31391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31391 s i)) at 1.
  unfold R.v31391, N.v31391.
  unfold R.v16463, N.v16463.
  rewrite !state_r1609_nr_5F1615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1609_nr_5F1615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31392 (s : N.State) (i : N.Inputs) :
  R.v31392 (state s) (inputs i) = Zmod.unsigned (N.v31392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31392 s i)) at 1.
  unfold R.v31392, N.v31392.
  unfold R.v6, N.v6.
  rewrite !state_r1608_nr_5F1614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1608_nr_5F1614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31393 (s : N.State) (i : N.Inputs) :
  R.v31393 (state s) (inputs i) = Zmod.unsigned (N.v31393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31393 s i)) at 1.
  unfold R.v31393, N.v31393.
  unfold R.v6, N.v6.
  rewrite !state_r1607_nr_5F1613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1607_nr_5F1613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31394 (s : N.State) (i : N.Inputs) :
  R.v31394 (state s) (inputs i) = Zmod.unsigned (N.v31394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31394 s i)) at 1.
  unfold R.v31394, N.v31394.
  rewrite ?node_31392.
  rewrite ?node_31393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31395 (s : N.State) (i : N.Inputs) :
  R.v31395 (state s) (inputs i) = Zmod.unsigned (N.v31395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31395 s i)) at 1.
  unfold R.v31395, N.v31395.
  unfold R.v16484, N.v16484.
  rewrite ?node_31394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31396 (s : N.State) (i : N.Inputs) :
  R.v31396 (state s) (inputs i) = Zmod.unsigned (N.v31396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31396 s i)) at 1.
  unfold R.v31396, N.v31396.
  rewrite ?node_31389.
  rewrite ?node_31390.
  rewrite ?node_31391.
  rewrite ?node_31395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31397 (s : N.State) (i : N.Inputs) :
  R.v31397 (state s) (inputs i) = Zmod.unsigned (N.v31397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31397 s i)) at 1.
  unfold R.v31397, N.v31397.
  unfold R.v6, N.v6.
  rewrite ?node_31396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31398 (s : N.State) (i : N.Inputs) :
  R.v31398 (state s) (inputs i) = Zmod.unsigned (N.v31398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31398 s i)) at 1.
  unfold R.v31398, N.v31398.
  rewrite ?node_12681.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31399 (s : N.State) (i : N.Inputs) :
  R.v31399 (state s) (inputs i) = Zmod.unsigned (N.v31399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31399 s i)) at 1.
  unfold R.v31399, N.v31399.
  unfold R.v6, N.v6.
  rewrite ?node_12810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31400 (s : N.State) (i : N.Inputs) :
  R.v31400 (state s) (inputs i) = Zmod.unsigned (N.v31400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31400 s i)) at 1.
  unfold R.v31400, N.v31400.
  unfold R.v6, N.v6.
  rewrite ?node_12861.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31401 (s : N.State) (i : N.Inputs) :
  R.v31401 (state s) (inputs i) = Zmod.unsigned (N.v31401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31401 s i)) at 1.
  unfold R.v31401, N.v31401.
  rewrite ?node_31398.
  rewrite ?node_31399.
  rewrite ?node_31400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31402 (s : N.State) (i : N.Inputs) :
  R.v31402 (state s) (inputs i) = Zmod.unsigned (N.v31402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31402 s i)) at 1.
  unfold R.v31402, N.v31402.
  rewrite ?node_31397.
  rewrite ?node_31401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31403 (s : N.State) (i : N.Inputs) :
  R.v31403 (state s) (inputs i) = Zmod.unsigned (N.v31403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31403 s i)) at 1.
  unfold R.v31403, N.v31403.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31404 (s : N.State) (i : N.Inputs) :
  R.v31404 (state s) (inputs i) = Zmod.unsigned (N.v31404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31404 s i)) at 1.
  unfold R.v31404, N.v31404.
  unfold R.v16463, N.v16463.
  rewrite !state_r1609_nr_5F1615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1609_nr_5F1615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31405 (s : N.State) (i : N.Inputs) :
  R.v31405 (state s) (inputs i) = Zmod.unsigned (N.v31405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31405 s i)) at 1.
  unfold R.v31405, N.v31405.
  unfold R.v6, N.v6.
  rewrite !state_r1608_nr_5F1614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1608_nr_5F1614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31406 (s : N.State) (i : N.Inputs) :
  R.v31406 (state s) (inputs i) = Zmod.unsigned (N.v31406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31406 s i)) at 1.
  unfold R.v31406, N.v31406.
  unfold R.v6, N.v6.
  rewrite !state_r1607_nr_5F1613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1607_nr_5F1613 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31407 (s : N.State) (i : N.Inputs) :
  R.v31407 (state s) (inputs i) = Zmod.unsigned (N.v31407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31407 s i)) at 1.
  unfold R.v31407, N.v31407.
  rewrite ?node_31405.
  rewrite ?node_31406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31408 (s : N.State) (i : N.Inputs) :
  R.v31408 (state s) (inputs i) = Zmod.unsigned (N.v31408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31408 s i)) at 1.
  unfold R.v31408, N.v31408.
  unfold R.v16484, N.v16484.
  rewrite ?node_31407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31409 (s : N.State) (i : N.Inputs) :
  R.v31409 (state s) (inputs i) = Zmod.unsigned (N.v31409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31409 s i)) at 1.
  unfold R.v31409, N.v31409.
  rewrite ?node_31404.
  rewrite ?node_31408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31410 (s : N.State) (i : N.Inputs) :
  R.v31410 (state s) (inputs i) = Zmod.unsigned (N.v31410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31410 s i)) at 1.
  unfold R.v31410, N.v31410.
  unfold R.v6, N.v6.
  rewrite ?node_31409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31411 (s : N.State) (i : N.Inputs) :
  R.v31411 (state s) (inputs i) = Zmod.unsigned (N.v31411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31411 s i)) at 1.
  unfold R.v31411, N.v31411.
  rewrite ?node_12676.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31412 (s : N.State) (i : N.Inputs) :
  R.v31412 (state s) (inputs i) = Zmod.unsigned (N.v31412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31412 s i)) at 1.
  unfold R.v31412, N.v31412.
  unfold R.v6, N.v6.
  rewrite ?node_12810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31413 (s : N.State) (i : N.Inputs) :
  R.v31413 (state s) (inputs i) = Zmod.unsigned (N.v31413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31413 s i)) at 1.
  unfold R.v31413, N.v31413.
  rewrite ?node_31411.
  rewrite ?node_31412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31414 (s : N.State) (i : N.Inputs) :
  R.v31414 (state s) (inputs i) = Zmod.unsigned (N.v31414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31414 s i)) at 1.
  unfold R.v31414, N.v31414.
  rewrite ?node_31410.
  rewrite ?node_31413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31415 (s : N.State) (i : N.Inputs) :
  R.v31415 (state s) (inputs i) = Zmod.unsigned (N.v31415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31415 s i)) at 1.
  unfold R.v31415, N.v31415.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31416 (s : N.State) (i : N.Inputs) :
  R.v31416 (state s) (inputs i) = Zmod.unsigned (N.v31416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31416 s i)) at 1.
  unfold R.v31416, N.v31416.
  rewrite ?node_12680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31417 (s : N.State) (i : N.Inputs) :
  R.v31417 (state s) (inputs i) = Zmod.unsigned (N.v31417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31417 s i)) at 1.
  unfold R.v31417, N.v31417.
  unfold R.v6, N.v6.
  rewrite !state_r1610_nr_5F1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1610_nr_5F1616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31418 (s : N.State) (i : N.Inputs) :
  R.v31418 (state s) (inputs i) = Zmod.unsigned (N.v31418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31418 s i)) at 1.
  unfold R.v31418, N.v31418.
  unfold R.v6, N.v6.
  rewrite ?node_12676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31419 (s : N.State) (i : N.Inputs) :
  R.v31419 (state s) (inputs i) = Zmod.unsigned (N.v31419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31419 s i)) at 1.
  unfold R.v31419, N.v31419.
  rewrite ?node_31417.
  rewrite ?node_31418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31420 (s : N.State) (i : N.Inputs) :
  R.v31420 (state s) (inputs i) = Zmod.unsigned (N.v31420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31420 s i)) at 1.
  unfold R.v31420, N.v31420.
  unfold R.v16484, N.v16484.
  rewrite ?node_31419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31421 (s : N.State) (i : N.Inputs) :
  R.v31421 (state s) (inputs i) = Zmod.unsigned (N.v31421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31421 s i)) at 1.
  unfold R.v31421, N.v31421.
  rewrite ?node_31416.
  rewrite ?node_31420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31422 (s : N.State) (i : N.Inputs) :
  R.v31422 (state s) (inputs i) = Zmod.unsigned (N.v31422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31422 s i)) at 1.
  unfold R.v31422, N.v31422.
  unfold R.v6, N.v6.
  rewrite ?node_31421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31423 (s : N.State) (i : N.Inputs) :
  R.v31423 (state s) (inputs i) = Zmod.unsigned (N.v31423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31423 s i)) at 1.
  unfold R.v31423, N.v31423.
  rewrite ?node_12681.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31424 (s : N.State) (i : N.Inputs) :
  R.v31424 (state s) (inputs i) = Zmod.unsigned (N.v31424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31424 s i)) at 1.
  unfold R.v31424, N.v31424.
  unfold R.v6, N.v6.
  rewrite ?node_12861.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31425 (s : N.State) (i : N.Inputs) :
  R.v31425 (state s) (inputs i) = Zmod.unsigned (N.v31425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31425 s i)) at 1.
  unfold R.v31425, N.v31425.
  rewrite ?node_31423.
  rewrite ?node_31424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31426 (s : N.State) (i : N.Inputs) :
  R.v31426 (state s) (inputs i) = Zmod.unsigned (N.v31426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31426 s i)) at 1.
  unfold R.v31426, N.v31426.
  rewrite ?node_31422.
  rewrite ?node_31425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31427 (s : N.State) (i : N.Inputs) :
  R.v31427 (state s) (inputs i) = Zmod.unsigned (N.v31427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31427 s i)) at 1.
  unfold R.v31427, N.v31427.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31428 (s : N.State) (i : N.Inputs) :
  R.v31428 (state s) (inputs i) = Zmod.unsigned (N.v31428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31428 s i)) at 1.
  unfold R.v31428, N.v31428.
  rewrite ?node_12688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31429 (s : N.State) (i : N.Inputs) :
  R.v31429 (state s) (inputs i) = Zmod.unsigned (N.v31429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31429 s i)) at 1.
  unfold R.v31429, N.v31429.
  unfold R.v16463, N.v16463.
  rewrite !state_r1614_nr_5F1620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1614_nr_5F1620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31430 (s : N.State) (i : N.Inputs) :
  R.v31430 (state s) (inputs i) = Zmod.unsigned (N.v31430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31430 s i)) at 1.
  unfold R.v31430, N.v31430.
  unfold R.v16463, N.v16463.
  rewrite !state_r1613_nr_5F1619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1613_nr_5F1619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31431 (s : N.State) (i : N.Inputs) :
  R.v31431 (state s) (inputs i) = Zmod.unsigned (N.v31431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31431 s i)) at 1.
  unfold R.v31431, N.v31431.
  unfold R.v6, N.v6.
  rewrite !state_r1612_nr_5F1618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1612_nr_5F1618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31432 (s : N.State) (i : N.Inputs) :
  R.v31432 (state s) (inputs i) = Zmod.unsigned (N.v31432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31432 s i)) at 1.
  unfold R.v31432, N.v31432.
  unfold R.v6, N.v6.
  rewrite !state_r1611_nr_5F1617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1611_nr_5F1617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31433 (s : N.State) (i : N.Inputs) :
  R.v31433 (state s) (inputs i) = Zmod.unsigned (N.v31433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31433 s i)) at 1.
  unfold R.v31433, N.v31433.
  rewrite ?node_31431.
  rewrite ?node_31432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31434 (s : N.State) (i : N.Inputs) :
  R.v31434 (state s) (inputs i) = Zmod.unsigned (N.v31434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31434 s i)) at 1.
  unfold R.v31434, N.v31434.
  unfold R.v16484, N.v16484.
  rewrite ?node_31433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31435 (s : N.State) (i : N.Inputs) :
  R.v31435 (state s) (inputs i) = Zmod.unsigned (N.v31435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31435 s i)) at 1.
  unfold R.v31435, N.v31435.
  rewrite ?node_31428.
  rewrite ?node_31429.
  rewrite ?node_31430.
  rewrite ?node_31434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31436 (s : N.State) (i : N.Inputs) :
  R.v31436 (state s) (inputs i) = Zmod.unsigned (N.v31436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31436 s i)) at 1.
  unfold R.v31436, N.v31436.
  unfold R.v6, N.v6.
  rewrite ?node_31435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31437 (s : N.State) (i : N.Inputs) :
  R.v31437 (state s) (inputs i) = Zmod.unsigned (N.v31437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31437 s i)) at 1.
  unfold R.v31437, N.v31437.
  rewrite ?node_12689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31438 (s : N.State) (i : N.Inputs) :
  R.v31438 (state s) (inputs i) = Zmod.unsigned (N.v31438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31438 s i)) at 1.
  unfold R.v31438, N.v31438.
  unfold R.v6, N.v6.
  rewrite ?node_12818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31439 (s : N.State) (i : N.Inputs) :
  R.v31439 (state s) (inputs i) = Zmod.unsigned (N.v31439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31439 s i)) at 1.
  unfold R.v31439, N.v31439.
  unfold R.v6, N.v6.
  rewrite ?node_12864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31440 (s : N.State) (i : N.Inputs) :
  R.v31440 (state s) (inputs i) = Zmod.unsigned (N.v31440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31440 s i)) at 1.
  unfold R.v31440, N.v31440.
  rewrite ?node_31437.
  rewrite ?node_31438.
  rewrite ?node_31439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31441 (s : N.State) (i : N.Inputs) :
  R.v31441 (state s) (inputs i) = Zmod.unsigned (N.v31441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31441 s i)) at 1.
  unfold R.v31441, N.v31441.
  rewrite ?node_31436.
  rewrite ?node_31440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31442 (s : N.State) (i : N.Inputs) :
  R.v31442 (state s) (inputs i) = Zmod.unsigned (N.v31442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31442 s i)) at 1.
  unfold R.v31442, N.v31442.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31443 (s : N.State) (i : N.Inputs) :
  R.v31443 (state s) (inputs i) = Zmod.unsigned (N.v31443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31443 s i)) at 1.
  unfold R.v31443, N.v31443.
  unfold R.v16463, N.v16463.
  rewrite !state_r1613_nr_5F1619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1613_nr_5F1619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31444 (s : N.State) (i : N.Inputs) :
  R.v31444 (state s) (inputs i) = Zmod.unsigned (N.v31444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31444 s i)) at 1.
  unfold R.v31444, N.v31444.
  unfold R.v6, N.v6.
  rewrite !state_r1612_nr_5F1618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1612_nr_5F1618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31445 (s : N.State) (i : N.Inputs) :
  R.v31445 (state s) (inputs i) = Zmod.unsigned (N.v31445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31445 s i)) at 1.
  unfold R.v31445, N.v31445.
  unfold R.v6, N.v6.
  rewrite !state_r1611_nr_5F1617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1611_nr_5F1617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31446 (s : N.State) (i : N.Inputs) :
  R.v31446 (state s) (inputs i) = Zmod.unsigned (N.v31446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31446 s i)) at 1.
  unfold R.v31446, N.v31446.
  rewrite ?node_31444.
  rewrite ?node_31445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31447 (s : N.State) (i : N.Inputs) :
  R.v31447 (state s) (inputs i) = Zmod.unsigned (N.v31447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31447 s i)) at 1.
  unfold R.v31447, N.v31447.
  unfold R.v16484, N.v16484.
  rewrite ?node_31446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31448 (s : N.State) (i : N.Inputs) :
  R.v31448 (state s) (inputs i) = Zmod.unsigned (N.v31448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31448 s i)) at 1.
  unfold R.v31448, N.v31448.
  rewrite ?node_31443.
  rewrite ?node_31447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31449 (s : N.State) (i : N.Inputs) :
  R.v31449 (state s) (inputs i) = Zmod.unsigned (N.v31449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31449 s i)) at 1.
  unfold R.v31449, N.v31449.
  unfold R.v6, N.v6.
  rewrite ?node_31448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31450 (s : N.State) (i : N.Inputs) :
  R.v31450 (state s) (inputs i) = Zmod.unsigned (N.v31450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31450 s i)) at 1.
  unfold R.v31450, N.v31450.
  rewrite ?node_12684.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31451 (s : N.State) (i : N.Inputs) :
  R.v31451 (state s) (inputs i) = Zmod.unsigned (N.v31451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31451 s i)) at 1.
  unfold R.v31451, N.v31451.
  unfold R.v6, N.v6.
  rewrite ?node_12818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31452 (s : N.State) (i : N.Inputs) :
  R.v31452 (state s) (inputs i) = Zmod.unsigned (N.v31452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31452 s i)) at 1.
  unfold R.v31452, N.v31452.
  rewrite ?node_31450.
  rewrite ?node_31451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31453 (s : N.State) (i : N.Inputs) :
  R.v31453 (state s) (inputs i) = Zmod.unsigned (N.v31453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31453 s i)) at 1.
  unfold R.v31453, N.v31453.
  rewrite ?node_31449.
  rewrite ?node_31452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31454 (s : N.State) (i : N.Inputs) :
  R.v31454 (state s) (inputs i) = Zmod.unsigned (N.v31454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31454 s i)) at 1.
  unfold R.v31454, N.v31454.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31455 (s : N.State) (i : N.Inputs) :
  R.v31455 (state s) (inputs i) = Zmod.unsigned (N.v31455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31455 s i)) at 1.
  unfold R.v31455, N.v31455.
  rewrite ?node_12688.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31456 (s : N.State) (i : N.Inputs) :
  R.v31456 (state s) (inputs i) = Zmod.unsigned (N.v31456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31456 s i)) at 1.
  unfold R.v31456, N.v31456.
  unfold R.v6, N.v6.
  rewrite !state_r1614_nr_5F1620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1614_nr_5F1620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31457 (s : N.State) (i : N.Inputs) :
  R.v31457 (state s) (inputs i) = Zmod.unsigned (N.v31457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31457 s i)) at 1.
  unfold R.v31457, N.v31457.
  unfold R.v6, N.v6.
  rewrite ?node_12684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31458 (s : N.State) (i : N.Inputs) :
  R.v31458 (state s) (inputs i) = Zmod.unsigned (N.v31458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31458 s i)) at 1.
  unfold R.v31458, N.v31458.
  rewrite ?node_31456.
  rewrite ?node_31457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31459 (s : N.State) (i : N.Inputs) :
  R.v31459 (state s) (inputs i) = Zmod.unsigned (N.v31459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31459 s i)) at 1.
  unfold R.v31459, N.v31459.
  unfold R.v16484, N.v16484.
  rewrite ?node_31458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31460 (s : N.State) (i : N.Inputs) :
  R.v31460 (state s) (inputs i) = Zmod.unsigned (N.v31460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31460 s i)) at 1.
  unfold R.v31460, N.v31460.
  rewrite ?node_31455.
  rewrite ?node_31459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31461 (s : N.State) (i : N.Inputs) :
  R.v31461 (state s) (inputs i) = Zmod.unsigned (N.v31461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31461 s i)) at 1.
  unfold R.v31461, N.v31461.
  unfold R.v6, N.v6.
  rewrite ?node_31460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31462 (s : N.State) (i : N.Inputs) :
  R.v31462 (state s) (inputs i) = Zmod.unsigned (N.v31462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31462 s i)) at 1.
  unfold R.v31462, N.v31462.
  rewrite ?node_12689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31463 (s : N.State) (i : N.Inputs) :
  R.v31463 (state s) (inputs i) = Zmod.unsigned (N.v31463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31463 s i)) at 1.
  unfold R.v31463, N.v31463.
  unfold R.v6, N.v6.
  rewrite ?node_12864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31464 (s : N.State) (i : N.Inputs) :
  R.v31464 (state s) (inputs i) = Zmod.unsigned (N.v31464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31464 s i)) at 1.
  unfold R.v31464, N.v31464.
  rewrite ?node_31462.
  rewrite ?node_31463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31465 (s : N.State) (i : N.Inputs) :
  R.v31465 (state s) (inputs i) = Zmod.unsigned (N.v31465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31465 s i)) at 1.
  unfold R.v31465, N.v31465.
  rewrite ?node_31461.
  rewrite ?node_31464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31466 (s : N.State) (i : N.Inputs) :
  R.v31466 (state s) (inputs i) = Zmod.unsigned (N.v31466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31466 s i)) at 1.
  unfold R.v31466, N.v31466.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31467 (s : N.State) (i : N.Inputs) :
  R.v31467 (state s) (inputs i) = Zmod.unsigned (N.v31467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31467 s i)) at 1.
  unfold R.v31467, N.v31467.
  rewrite ?node_12696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31468 (s : N.State) (i : N.Inputs) :
  R.v31468 (state s) (inputs i) = Zmod.unsigned (N.v31468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31468 s i)) at 1.
  unfold R.v31468, N.v31468.
  unfold R.v16463, N.v16463.
  rewrite !state_r1618_nr_5F1624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1618_nr_5F1624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31469 (s : N.State) (i : N.Inputs) :
  R.v31469 (state s) (inputs i) = Zmod.unsigned (N.v31469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31469 s i)) at 1.
  unfold R.v31469, N.v31469.
  unfold R.v16463, N.v16463.
  rewrite !state_r1617_nr_5F1623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1617_nr_5F1623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31470 (s : N.State) (i : N.Inputs) :
  R.v31470 (state s) (inputs i) = Zmod.unsigned (N.v31470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31470 s i)) at 1.
  unfold R.v31470, N.v31470.
  unfold R.v6, N.v6.
  rewrite !state_r1616_nr_5F1622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1616_nr_5F1622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31471 (s : N.State) (i : N.Inputs) :
  R.v31471 (state s) (inputs i) = Zmod.unsigned (N.v31471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31471 s i)) at 1.
  unfold R.v31471, N.v31471.
  unfold R.v6, N.v6.
  rewrite !state_r1615_nr_5F1621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1615_nr_5F1621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31472 (s : N.State) (i : N.Inputs) :
  R.v31472 (state s) (inputs i) = Zmod.unsigned (N.v31472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31472 s i)) at 1.
  unfold R.v31472, N.v31472.
  rewrite ?node_31470.
  rewrite ?node_31471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31473 (s : N.State) (i : N.Inputs) :
  R.v31473 (state s) (inputs i) = Zmod.unsigned (N.v31473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31473 s i)) at 1.
  unfold R.v31473, N.v31473.
  unfold R.v16484, N.v16484.
  rewrite ?node_31472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31474 (s : N.State) (i : N.Inputs) :
  R.v31474 (state s) (inputs i) = Zmod.unsigned (N.v31474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31474 s i)) at 1.
  unfold R.v31474, N.v31474.
  rewrite ?node_31467.
  rewrite ?node_31468.
  rewrite ?node_31469.
  rewrite ?node_31473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31475 (s : N.State) (i : N.Inputs) :
  R.v31475 (state s) (inputs i) = Zmod.unsigned (N.v31475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31475 s i)) at 1.
  unfold R.v31475, N.v31475.
  unfold R.v6, N.v6.
  rewrite ?node_31474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31476 (s : N.State) (i : N.Inputs) :
  R.v31476 (state s) (inputs i) = Zmod.unsigned (N.v31476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31476 s i)) at 1.
  unfold R.v31476, N.v31476.
  rewrite ?node_12697.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31477 (s : N.State) (i : N.Inputs) :
  R.v31477 (state s) (inputs i) = Zmod.unsigned (N.v31477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31477 s i)) at 1.
  unfold R.v31477, N.v31477.
  unfold R.v6, N.v6.
  rewrite ?node_12826.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31478 (s : N.State) (i : N.Inputs) :
  R.v31478 (state s) (inputs i) = Zmod.unsigned (N.v31478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31478 s i)) at 1.
  unfold R.v31478, N.v31478.
  unfold R.v6, N.v6.
  rewrite ?node_12868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31479 (s : N.State) (i : N.Inputs) :
  R.v31479 (state s) (inputs i) = Zmod.unsigned (N.v31479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31479 s i)) at 1.
  unfold R.v31479, N.v31479.
  rewrite ?node_31476.
  rewrite ?node_31477.
  rewrite ?node_31478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31480 (s : N.State) (i : N.Inputs) :
  R.v31480 (state s) (inputs i) = Zmod.unsigned (N.v31480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31480 s i)) at 1.
  unfold R.v31480, N.v31480.
  rewrite ?node_31475.
  rewrite ?node_31479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31481 (s : N.State) (i : N.Inputs) :
  R.v31481 (state s) (inputs i) = Zmod.unsigned (N.v31481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31481 s i)) at 1.
  unfold R.v31481, N.v31481.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31482 (s : N.State) (i : N.Inputs) :
  R.v31482 (state s) (inputs i) = Zmod.unsigned (N.v31482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31482 s i)) at 1.
  unfold R.v31482, N.v31482.
  unfold R.v16463, N.v16463.
  rewrite !state_r1617_nr_5F1623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1617_nr_5F1623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31483 (s : N.State) (i : N.Inputs) :
  R.v31483 (state s) (inputs i) = Zmod.unsigned (N.v31483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31483 s i)) at 1.
  unfold R.v31483, N.v31483.
  unfold R.v6, N.v6.
  rewrite !state_r1616_nr_5F1622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1616_nr_5F1622 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31484 (s : N.State) (i : N.Inputs) :
  R.v31484 (state s) (inputs i) = Zmod.unsigned (N.v31484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31484 s i)) at 1.
  unfold R.v31484, N.v31484.
  unfold R.v6, N.v6.
  rewrite !state_r1615_nr_5F1621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1615_nr_5F1621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31485 (s : N.State) (i : N.Inputs) :
  R.v31485 (state s) (inputs i) = Zmod.unsigned (N.v31485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31485 s i)) at 1.
  unfold R.v31485, N.v31485.
  rewrite ?node_31483.
  rewrite ?node_31484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31486 (s : N.State) (i : N.Inputs) :
  R.v31486 (state s) (inputs i) = Zmod.unsigned (N.v31486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31486 s i)) at 1.
  unfold R.v31486, N.v31486.
  unfold R.v16484, N.v16484.
  rewrite ?node_31485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31487 (s : N.State) (i : N.Inputs) :
  R.v31487 (state s) (inputs i) = Zmod.unsigned (N.v31487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31487 s i)) at 1.
  unfold R.v31487, N.v31487.
  rewrite ?node_31482.
  rewrite ?node_31486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31488 (s : N.State) (i : N.Inputs) :
  R.v31488 (state s) (inputs i) = Zmod.unsigned (N.v31488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31488 s i)) at 1.
  unfold R.v31488, N.v31488.
  unfold R.v6, N.v6.
  rewrite ?node_31487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31489 (s : N.State) (i : N.Inputs) :
  R.v31489 (state s) (inputs i) = Zmod.unsigned (N.v31489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31489 s i)) at 1.
  unfold R.v31489, N.v31489.
  rewrite ?node_12692.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31490 (s : N.State) (i : N.Inputs) :
  R.v31490 (state s) (inputs i) = Zmod.unsigned (N.v31490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31490 s i)) at 1.
  unfold R.v31490, N.v31490.
  unfold R.v6, N.v6.
  rewrite ?node_12826.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31491 (s : N.State) (i : N.Inputs) :
  R.v31491 (state s) (inputs i) = Zmod.unsigned (N.v31491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31491 s i)) at 1.
  unfold R.v31491, N.v31491.
  rewrite ?node_31489.
  rewrite ?node_31490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31492 (s : N.State) (i : N.Inputs) :
  R.v31492 (state s) (inputs i) = Zmod.unsigned (N.v31492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31492 s i)) at 1.
  unfold R.v31492, N.v31492.
  rewrite ?node_31488.
  rewrite ?node_31491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31493 (s : N.State) (i : N.Inputs) :
  R.v31493 (state s) (inputs i) = Zmod.unsigned (N.v31493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31493 s i)) at 1.
  unfold R.v31493, N.v31493.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31494 (s : N.State) (i : N.Inputs) :
  R.v31494 (state s) (inputs i) = Zmod.unsigned (N.v31494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31494 s i)) at 1.
  unfold R.v31494, N.v31494.
  rewrite ?node_12696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31495 (s : N.State) (i : N.Inputs) :
  R.v31495 (state s) (inputs i) = Zmod.unsigned (N.v31495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31495 s i)) at 1.
  unfold R.v31495, N.v31495.
  unfold R.v6, N.v6.
  rewrite !state_r1618_nr_5F1624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1618_nr_5F1624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31496 (s : N.State) (i : N.Inputs) :
  R.v31496 (state s) (inputs i) = Zmod.unsigned (N.v31496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31496 s i)) at 1.
  unfold R.v31496, N.v31496.
  unfold R.v6, N.v6.
  rewrite ?node_12692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31497 (s : N.State) (i : N.Inputs) :
  R.v31497 (state s) (inputs i) = Zmod.unsigned (N.v31497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31497 s i)) at 1.
  unfold R.v31497, N.v31497.
  rewrite ?node_31495.
  rewrite ?node_31496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31498 (s : N.State) (i : N.Inputs) :
  R.v31498 (state s) (inputs i) = Zmod.unsigned (N.v31498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31498 s i)) at 1.
  unfold R.v31498, N.v31498.
  unfold R.v16484, N.v16484.
  rewrite ?node_31497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31499 (s : N.State) (i : N.Inputs) :
  R.v31499 (state s) (inputs i) = Zmod.unsigned (N.v31499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31499 s i)) at 1.
  unfold R.v31499, N.v31499.
  rewrite ?node_31494.
  rewrite ?node_31498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31500 (s : N.State) (i : N.Inputs) :
  R.v31500 (state s) (inputs i) = Zmod.unsigned (N.v31500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31500 s i)) at 1.
  unfold R.v31500, N.v31500.
  unfold R.v6, N.v6.
  rewrite ?node_31499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31501 (s : N.State) (i : N.Inputs) :
  R.v31501 (state s) (inputs i) = Zmod.unsigned (N.v31501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31501 s i)) at 1.
  unfold R.v31501, N.v31501.
  rewrite ?node_12697.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31502 (s : N.State) (i : N.Inputs) :
  R.v31502 (state s) (inputs i) = Zmod.unsigned (N.v31502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31502 s i)) at 1.
  unfold R.v31502, N.v31502.
  unfold R.v6, N.v6.
  rewrite ?node_12868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31503 (s : N.State) (i : N.Inputs) :
  R.v31503 (state s) (inputs i) = Zmod.unsigned (N.v31503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31503 s i)) at 1.
  unfold R.v31503, N.v31503.
  rewrite ?node_31501.
  rewrite ?node_31502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31504 (s : N.State) (i : N.Inputs) :
  R.v31504 (state s) (inputs i) = Zmod.unsigned (N.v31504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31504 s i)) at 1.
  unfold R.v31504, N.v31504.
  rewrite ?node_31500.
  rewrite ?node_31503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31505 (s : N.State) (i : N.Inputs) :
  R.v31505 (state s) (inputs i) = Zmod.unsigned (N.v31505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31505 s i)) at 1.
  unfold R.v31505, N.v31505.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31506 (s : N.State) (i : N.Inputs) :
  R.v31506 (state s) (inputs i) = Zmod.unsigned (N.v31506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31506 s i)) at 1.
  unfold R.v31506, N.v31506.
  rewrite ?node_12708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31507 (s : N.State) (i : N.Inputs) :
  R.v31507 (state s) (inputs i) = Zmod.unsigned (N.v31507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31507 s i)) at 1.
  unfold R.v31507, N.v31507.
  unfold R.v16463, N.v16463.
  rewrite !state_r1622_nr_5F1628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1622_nr_5F1628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31508 (s : N.State) (i : N.Inputs) :
  R.v31508 (state s) (inputs i) = Zmod.unsigned (N.v31508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31508 s i)) at 1.
  unfold R.v31508, N.v31508.
  unfold R.v16463, N.v16463.
  rewrite !state_r1621_nr_5F1627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1621_nr_5F1627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31509 (s : N.State) (i : N.Inputs) :
  R.v31509 (state s) (inputs i) = Zmod.unsigned (N.v31509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31509 s i)) at 1.
  unfold R.v31509, N.v31509.
  unfold R.v6, N.v6.
  rewrite !state_r1620_nr_5F1626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1620_nr_5F1626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31510 (s : N.State) (i : N.Inputs) :
  R.v31510 (state s) (inputs i) = Zmod.unsigned (N.v31510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31510 s i)) at 1.
  unfold R.v31510, N.v31510.
  unfold R.v6, N.v6.
  rewrite !state_r1619_nr_5F1625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1619_nr_5F1625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31511 (s : N.State) (i : N.Inputs) :
  R.v31511 (state s) (inputs i) = Zmod.unsigned (N.v31511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31511 s i)) at 1.
  unfold R.v31511, N.v31511.
  rewrite ?node_31509.
  rewrite ?node_31510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31512 (s : N.State) (i : N.Inputs) :
  R.v31512 (state s) (inputs i) = Zmod.unsigned (N.v31512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31512 s i)) at 1.
  unfold R.v31512, N.v31512.
  unfold R.v16484, N.v16484.
  rewrite ?node_31511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31513 (s : N.State) (i : N.Inputs) :
  R.v31513 (state s) (inputs i) = Zmod.unsigned (N.v31513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31513 s i)) at 1.
  unfold R.v31513, N.v31513.
  rewrite ?node_31506.
  rewrite ?node_31507.
  rewrite ?node_31508.
  rewrite ?node_31512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31514 (s : N.State) (i : N.Inputs) :
  R.v31514 (state s) (inputs i) = Zmod.unsigned (N.v31514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31514 s i)) at 1.
  unfold R.v31514, N.v31514.
  unfold R.v6, N.v6.
  rewrite ?node_31513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31515 (s : N.State) (i : N.Inputs) :
  R.v31515 (state s) (inputs i) = Zmod.unsigned (N.v31515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31515 s i)) at 1.
  unfold R.v31515, N.v31515.
  rewrite ?node_12709.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31516 (s : N.State) (i : N.Inputs) :
  R.v31516 (state s) (inputs i) = Zmod.unsigned (N.v31516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31516 s i)) at 1.
  unfold R.v31516, N.v31516.
  unfold R.v6, N.v6.
  rewrite ?node_12838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31517 (s : N.State) (i : N.Inputs) :
  R.v31517 (state s) (inputs i) = Zmod.unsigned (N.v31517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31517 s i)) at 1.
  unfold R.v31517, N.v31517.
  unfold R.v6, N.v6.
  rewrite ?node_12872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31518 (s : N.State) (i : N.Inputs) :
  R.v31518 (state s) (inputs i) = Zmod.unsigned (N.v31518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31518 s i)) at 1.
  unfold R.v31518, N.v31518.
  rewrite ?node_31515.
  rewrite ?node_31516.
  rewrite ?node_31517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31519 (s : N.State) (i : N.Inputs) :
  R.v31519 (state s) (inputs i) = Zmod.unsigned (N.v31519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31519 s i)) at 1.
  unfold R.v31519, N.v31519.
  rewrite ?node_31514.
  rewrite ?node_31518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31520 (s : N.State) (i : N.Inputs) :
  R.v31520 (state s) (inputs i) = Zmod.unsigned (N.v31520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31520 s i)) at 1.
  unfold R.v31520, N.v31520.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31521 (s : N.State) (i : N.Inputs) :
  R.v31521 (state s) (inputs i) = Zmod.unsigned (N.v31521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31521 s i)) at 1.
  unfold R.v31521, N.v31521.
  unfold R.v16463, N.v16463.
  rewrite !state_r1621_nr_5F1627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1621_nr_5F1627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31522 (s : N.State) (i : N.Inputs) :
  R.v31522 (state s) (inputs i) = Zmod.unsigned (N.v31522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31522 s i)) at 1.
  unfold R.v31522, N.v31522.
  unfold R.v6, N.v6.
  rewrite !state_r1620_nr_5F1626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1620_nr_5F1626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31523 (s : N.State) (i : N.Inputs) :
  R.v31523 (state s) (inputs i) = Zmod.unsigned (N.v31523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31523 s i)) at 1.
  unfold R.v31523, N.v31523.
  unfold R.v6, N.v6.
  rewrite !state_r1619_nr_5F1625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1619_nr_5F1625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31524 (s : N.State) (i : N.Inputs) :
  R.v31524 (state s) (inputs i) = Zmod.unsigned (N.v31524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31524 s i)) at 1.
  unfold R.v31524, N.v31524.
  rewrite ?node_31522.
  rewrite ?node_31523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31525 (s : N.State) (i : N.Inputs) :
  R.v31525 (state s) (inputs i) = Zmod.unsigned (N.v31525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31525 s i)) at 1.
  unfold R.v31525, N.v31525.
  unfold R.v16484, N.v16484.
  rewrite ?node_31524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31526 (s : N.State) (i : N.Inputs) :
  R.v31526 (state s) (inputs i) = Zmod.unsigned (N.v31526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31526 s i)) at 1.
  unfold R.v31526, N.v31526.
  rewrite ?node_31521.
  rewrite ?node_31525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31527 (s : N.State) (i : N.Inputs) :
  R.v31527 (state s) (inputs i) = Zmod.unsigned (N.v31527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31527 s i)) at 1.
  unfold R.v31527, N.v31527.
  unfold R.v6, N.v6.
  rewrite ?node_31526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31528 (s : N.State) (i : N.Inputs) :
  R.v31528 (state s) (inputs i) = Zmod.unsigned (N.v31528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31528 s i)) at 1.
  unfold R.v31528, N.v31528.
  rewrite ?node_12704.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31529 (s : N.State) (i : N.Inputs) :
  R.v31529 (state s) (inputs i) = Zmod.unsigned (N.v31529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31529 s i)) at 1.
  unfold R.v31529, N.v31529.
  unfold R.v6, N.v6.
  rewrite ?node_12838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31530 (s : N.State) (i : N.Inputs) :
  R.v31530 (state s) (inputs i) = Zmod.unsigned (N.v31530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31530 s i)) at 1.
  unfold R.v31530, N.v31530.
  rewrite ?node_31528.
  rewrite ?node_31529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31531 (s : N.State) (i : N.Inputs) :
  R.v31531 (state s) (inputs i) = Zmod.unsigned (N.v31531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31531 s i)) at 1.
  unfold R.v31531, N.v31531.
  rewrite ?node_31527.
  rewrite ?node_31530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31532 (s : N.State) (i : N.Inputs) :
  R.v31532 (state s) (inputs i) = Zmod.unsigned (N.v31532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31532 s i)) at 1.
  unfold R.v31532, N.v31532.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31533 (s : N.State) (i : N.Inputs) :
  R.v31533 (state s) (inputs i) = Zmod.unsigned (N.v31533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31533 s i)) at 1.
  unfold R.v31533, N.v31533.
  rewrite ?node_12708.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31534 (s : N.State) (i : N.Inputs) :
  R.v31534 (state s) (inputs i) = Zmod.unsigned (N.v31534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31534 s i)) at 1.
  unfold R.v31534, N.v31534.
  unfold R.v6, N.v6.
  rewrite !state_r1622_nr_5F1628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1622_nr_5F1628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31535 (s : N.State) (i : N.Inputs) :
  R.v31535 (state s) (inputs i) = Zmod.unsigned (N.v31535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31535 s i)) at 1.
  unfold R.v31535, N.v31535.
  unfold R.v6, N.v6.
  rewrite ?node_12704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31536 (s : N.State) (i : N.Inputs) :
  R.v31536 (state s) (inputs i) = Zmod.unsigned (N.v31536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31536 s i)) at 1.
  unfold R.v31536, N.v31536.
  rewrite ?node_31534.
  rewrite ?node_31535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31537 (s : N.State) (i : N.Inputs) :
  R.v31537 (state s) (inputs i) = Zmod.unsigned (N.v31537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31537 s i)) at 1.
  unfold R.v31537, N.v31537.
  unfold R.v16484, N.v16484.
  rewrite ?node_31536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31538 (s : N.State) (i : N.Inputs) :
  R.v31538 (state s) (inputs i) = Zmod.unsigned (N.v31538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31538 s i)) at 1.
  unfold R.v31538, N.v31538.
  rewrite ?node_31533.
  rewrite ?node_31537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31539 (s : N.State) (i : N.Inputs) :
  R.v31539 (state s) (inputs i) = Zmod.unsigned (N.v31539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31539 s i)) at 1.
  unfold R.v31539, N.v31539.
  unfold R.v6, N.v6.
  rewrite ?node_31538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31540 (s : N.State) (i : N.Inputs) :
  R.v31540 (state s) (inputs i) = Zmod.unsigned (N.v31540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31540 s i)) at 1.
  unfold R.v31540, N.v31540.
  rewrite ?node_12709.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31541 (s : N.State) (i : N.Inputs) :
  R.v31541 (state s) (inputs i) = Zmod.unsigned (N.v31541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31541 s i)) at 1.
  unfold R.v31541, N.v31541.
  unfold R.v6, N.v6.
  rewrite ?node_12872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31542 (s : N.State) (i : N.Inputs) :
  R.v31542 (state s) (inputs i) = Zmod.unsigned (N.v31542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31542 s i)) at 1.
  unfold R.v31542, N.v31542.
  rewrite ?node_31540.
  rewrite ?node_31541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31543 (s : N.State) (i : N.Inputs) :
  R.v31543 (state s) (inputs i) = Zmod.unsigned (N.v31543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31543 s i)) at 1.
  unfold R.v31543, N.v31543.
  rewrite ?node_31539.
  rewrite ?node_31542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31544 (s : N.State) (i : N.Inputs) :
  R.v31544 (state s) (inputs i) = Zmod.unsigned (N.v31544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31544 s i)) at 1.
  unfold R.v31544, N.v31544.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31545 (s : N.State) (i : N.Inputs) :
  R.v31545 (state s) (inputs i) = Zmod.unsigned (N.v31545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31545 s i)) at 1.
  unfold R.v31545, N.v31545.
  rewrite ?node_12715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31546 (s : N.State) (i : N.Inputs) :
  R.v31546 (state s) (inputs i) = Zmod.unsigned (N.v31546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31546 s i)) at 1.
  unfold R.v31546, N.v31546.
  unfold R.v16463, N.v16463.
  rewrite !state_r1626_nr_5F1632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1626_nr_5F1632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31547 (s : N.State) (i : N.Inputs) :
  R.v31547 (state s) (inputs i) = Zmod.unsigned (N.v31547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31547 s i)) at 1.
  unfold R.v31547, N.v31547.
  unfold R.v16463, N.v16463.
  rewrite !state_r1625_nr_5F1631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1625_nr_5F1631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31548 (s : N.State) (i : N.Inputs) :
  R.v31548 (state s) (inputs i) = Zmod.unsigned (N.v31548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31548 s i)) at 1.
  unfold R.v31548, N.v31548.
  unfold R.v6, N.v6.
  rewrite !state_r1624_nr_5F1630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1624_nr_5F1630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31549 (s : N.State) (i : N.Inputs) :
  R.v31549 (state s) (inputs i) = Zmod.unsigned (N.v31549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31549 s i)) at 1.
  unfold R.v31549, N.v31549.
  unfold R.v6, N.v6.
  rewrite !state_r1623_nr_5F1629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1623_nr_5F1629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31550 (s : N.State) (i : N.Inputs) :
  R.v31550 (state s) (inputs i) = Zmod.unsigned (N.v31550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31550 s i)) at 1.
  unfold R.v31550, N.v31550.
  rewrite ?node_31548.
  rewrite ?node_31549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31551 (s : N.State) (i : N.Inputs) :
  R.v31551 (state s) (inputs i) = Zmod.unsigned (N.v31551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31551 s i)) at 1.
  unfold R.v31551, N.v31551.
  unfold R.v16484, N.v16484.
  rewrite ?node_31550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31552 (s : N.State) (i : N.Inputs) :
  R.v31552 (state s) (inputs i) = Zmod.unsigned (N.v31552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31552 s i)) at 1.
  unfold R.v31552, N.v31552.
  rewrite ?node_31545.
  rewrite ?node_31546.
  rewrite ?node_31547.
  rewrite ?node_31551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31553 (s : N.State) (i : N.Inputs) :
  R.v31553 (state s) (inputs i) = Zmod.unsigned (N.v31553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31553 s i)) at 1.
  unfold R.v31553, N.v31553.
  unfold R.v6, N.v6.
  rewrite ?node_31552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31554 (s : N.State) (i : N.Inputs) :
  R.v31554 (state s) (inputs i) = Zmod.unsigned (N.v31554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31554 s i)) at 1.
  unfold R.v31554, N.v31554.
  rewrite ?node_12716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31555 (s : N.State) (i : N.Inputs) :
  R.v31555 (state s) (inputs i) = Zmod.unsigned (N.v31555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31555 s i)) at 1.
  unfold R.v31555, N.v31555.
  unfold R.v6, N.v6.
  rewrite ?node_12845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31556 (s : N.State) (i : N.Inputs) :
  R.v31556 (state s) (inputs i) = Zmod.unsigned (N.v31556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31556 s i)) at 1.
  unfold R.v31556, N.v31556.
  unfold R.v6, N.v6.
  rewrite ?node_12881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31557 (s : N.State) (i : N.Inputs) :
  R.v31557 (state s) (inputs i) = Zmod.unsigned (N.v31557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31557 s i)) at 1.
  unfold R.v31557, N.v31557.
  rewrite ?node_31554.
  rewrite ?node_31555.
  rewrite ?node_31556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31558 (s : N.State) (i : N.Inputs) :
  R.v31558 (state s) (inputs i) = Zmod.unsigned (N.v31558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31558 s i)) at 1.
  unfold R.v31558, N.v31558.
  rewrite ?node_31553.
  rewrite ?node_31557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31559 (s : N.State) (i : N.Inputs) :
  R.v31559 (state s) (inputs i) = Zmod.unsigned (N.v31559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31559 s i)) at 1.
  unfold R.v31559, N.v31559.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31560 (s : N.State) (i : N.Inputs) :
  R.v31560 (state s) (inputs i) = Zmod.unsigned (N.v31560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31560 s i)) at 1.
  unfold R.v31560, N.v31560.
  unfold R.v16463, N.v16463.
  rewrite !state_r1625_nr_5F1631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1625_nr_5F1631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31561 (s : N.State) (i : N.Inputs) :
  R.v31561 (state s) (inputs i) = Zmod.unsigned (N.v31561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31561 s i)) at 1.
  unfold R.v31561, N.v31561.
  unfold R.v6, N.v6.
  rewrite !state_r1624_nr_5F1630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1624_nr_5F1630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31562 (s : N.State) (i : N.Inputs) :
  R.v31562 (state s) (inputs i) = Zmod.unsigned (N.v31562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31562 s i)) at 1.
  unfold R.v31562, N.v31562.
  unfold R.v6, N.v6.
  rewrite !state_r1623_nr_5F1629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1623_nr_5F1629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31563 (s : N.State) (i : N.Inputs) :
  R.v31563 (state s) (inputs i) = Zmod.unsigned (N.v31563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31563 s i)) at 1.
  unfold R.v31563, N.v31563.
  rewrite ?node_31561.
  rewrite ?node_31562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31564 (s : N.State) (i : N.Inputs) :
  R.v31564 (state s) (inputs i) = Zmod.unsigned (N.v31564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31564 s i)) at 1.
  unfold R.v31564, N.v31564.
  unfold R.v16484, N.v16484.
  rewrite ?node_31563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31565 (s : N.State) (i : N.Inputs) :
  R.v31565 (state s) (inputs i) = Zmod.unsigned (N.v31565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31565 s i)) at 1.
  unfold R.v31565, N.v31565.
  rewrite ?node_31560.
  rewrite ?node_31564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31566 (s : N.State) (i : N.Inputs) :
  R.v31566 (state s) (inputs i) = Zmod.unsigned (N.v31566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31566 s i)) at 1.
  unfold R.v31566, N.v31566.
  unfold R.v6, N.v6.
  rewrite ?node_31565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31567 (s : N.State) (i : N.Inputs) :
  R.v31567 (state s) (inputs i) = Zmod.unsigned (N.v31567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31567 s i)) at 1.
  unfold R.v31567, N.v31567.
  rewrite ?node_12711.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31568 (s : N.State) (i : N.Inputs) :
  R.v31568 (state s) (inputs i) = Zmod.unsigned (N.v31568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31568 s i)) at 1.
  unfold R.v31568, N.v31568.
  unfold R.v6, N.v6.
  rewrite ?node_12845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31569 (s : N.State) (i : N.Inputs) :
  R.v31569 (state s) (inputs i) = Zmod.unsigned (N.v31569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31569 s i)) at 1.
  unfold R.v31569, N.v31569.
  rewrite ?node_31567.
  rewrite ?node_31568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31570 (s : N.State) (i : N.Inputs) :
  R.v31570 (state s) (inputs i) = Zmod.unsigned (N.v31570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31570 s i)) at 1.
  unfold R.v31570, N.v31570.
  rewrite ?node_31566.
  rewrite ?node_31569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31571 (s : N.State) (i : N.Inputs) :
  R.v31571 (state s) (inputs i) = Zmod.unsigned (N.v31571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31571 s i)) at 1.
  unfold R.v31571, N.v31571.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31572 (s : N.State) (i : N.Inputs) :
  R.v31572 (state s) (inputs i) = Zmod.unsigned (N.v31572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31572 s i)) at 1.
  unfold R.v31572, N.v31572.
  rewrite ?node_12715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31573 (s : N.State) (i : N.Inputs) :
  R.v31573 (state s) (inputs i) = Zmod.unsigned (N.v31573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31573 s i)) at 1.
  unfold R.v31573, N.v31573.
  unfold R.v6, N.v6.
  rewrite !state_r1626_nr_5F1632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1626_nr_5F1632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31574 (s : N.State) (i : N.Inputs) :
  R.v31574 (state s) (inputs i) = Zmod.unsigned (N.v31574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31574 s i)) at 1.
  unfold R.v31574, N.v31574.
  unfold R.v6, N.v6.
  rewrite ?node_12711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31575 (s : N.State) (i : N.Inputs) :
  R.v31575 (state s) (inputs i) = Zmod.unsigned (N.v31575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31575 s i)) at 1.
  unfold R.v31575, N.v31575.
  rewrite ?node_31573.
  rewrite ?node_31574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31576 (s : N.State) (i : N.Inputs) :
  R.v31576 (state s) (inputs i) = Zmod.unsigned (N.v31576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31576 s i)) at 1.
  unfold R.v31576, N.v31576.
  unfold R.v16484, N.v16484.
  rewrite ?node_31575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31577 (s : N.State) (i : N.Inputs) :
  R.v31577 (state s) (inputs i) = Zmod.unsigned (N.v31577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31577 s i)) at 1.
  unfold R.v31577, N.v31577.
  rewrite ?node_31572.
  rewrite ?node_31576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31578 (s : N.State) (i : N.Inputs) :
  R.v31578 (state s) (inputs i) = Zmod.unsigned (N.v31578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31578 s i)) at 1.
  unfold R.v31578, N.v31578.
  unfold R.v6, N.v6.
  rewrite ?node_31577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31579 (s : N.State) (i : N.Inputs) :
  R.v31579 (state s) (inputs i) = Zmod.unsigned (N.v31579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31579 s i)) at 1.
  unfold R.v31579, N.v31579.
  rewrite ?node_12716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31580 (s : N.State) (i : N.Inputs) :
  R.v31580 (state s) (inputs i) = Zmod.unsigned (N.v31580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31580 s i)) at 1.
  unfold R.v31580, N.v31580.
  unfold R.v6, N.v6.
  rewrite ?node_12881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31581 (s : N.State) (i : N.Inputs) :
  R.v31581 (state s) (inputs i) = Zmod.unsigned (N.v31581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31581 s i)) at 1.
  unfold R.v31581, N.v31581.
  rewrite ?node_31579.
  rewrite ?node_31580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31582 (s : N.State) (i : N.Inputs) :
  R.v31582 (state s) (inputs i) = Zmod.unsigned (N.v31582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31582 s i)) at 1.
  unfold R.v31582, N.v31582.
  rewrite ?node_31578.
  rewrite ?node_31581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31583 (s : N.State) (i : N.Inputs) :
  R.v31583 (state s) (inputs i) = Zmod.unsigned (N.v31583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31583 s i)) at 1.
  unfold R.v31583, N.v31583.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31584 (s : N.State) (i : N.Inputs) :
  R.v31584 (state s) (inputs i) = Zmod.unsigned (N.v31584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31584 s i)) at 1.
  unfold R.v31584, N.v31584.
  unfold R.v6, N.v6.
  rewrite !state_r1628_nr_5F1634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1628_nr_5F1634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31585 (s : N.State) (i : N.Inputs) :
  R.v31585 (state s) (inputs i) = Zmod.unsigned (N.v31585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31585 s i)) at 1.
  unfold R.v31585, N.v31585.
  unfold R.v6, N.v6.
  rewrite !state_r1627_nr_5F1633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1627_nr_5F1633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31586 (s : N.State) (i : N.Inputs) :
  R.v31586 (state s) (inputs i) = Zmod.unsigned (N.v31586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31586 s i)) at 1.
  unfold R.v31586, N.v31586.
  rewrite ?node_31584.
  rewrite ?node_31585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31587 (s : N.State) (i : N.Inputs) :
  R.v31587 (state s) (inputs i) = Zmod.unsigned (N.v31587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31587 s i)) at 1.
  unfold R.v31587, N.v31587.
  unfold R.v16463, N.v16463.
  rewrite ?node_31586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31588 (s : N.State) (i : N.Inputs) :
  R.v31588 (state s) (inputs i) = Zmod.unsigned (N.v31588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31588 s i)) at 1.
  unfold R.v31588, N.v31588.
  rewrite ?node_12718.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31589 (s : N.State) (i : N.Inputs) :
  R.v31589 (state s) (inputs i) = Zmod.unsigned (N.v31589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31589 s i)) at 1.
  unfold R.v31589, N.v31589.
  unfold R.v6, N.v6.
  rewrite ?node_12882.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31590 (s : N.State) (i : N.Inputs) :
  R.v31590 (state s) (inputs i) = Zmod.unsigned (N.v31590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31590 s i)) at 1.
  unfold R.v31590, N.v31590.
  rewrite ?node_31588.
  rewrite ?node_31589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31591 (s : N.State) (i : N.Inputs) :
  R.v31591 (state s) (inputs i) = Zmod.unsigned (N.v31591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31591 s i)) at 1.
  unfold R.v31591, N.v31591.
  rewrite ?node_31587.
  rewrite ?node_31590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31592 (s : N.State) (i : N.Inputs) :
  R.v31592 (state s) (inputs i) = Zmod.unsigned (N.v31592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31592 s i)) at 1.
  unfold R.v31592, N.v31592.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31593 (s : N.State) (i : N.Inputs) :
  R.v31593 (state s) (inputs i) = Zmod.unsigned (N.v31593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31593 s i)) at 1.
  unfold R.v31593, N.v31593.
  rewrite ?node_12803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31594 (s : N.State) (i : N.Inputs) :
  R.v31594 (state s) (inputs i) = Zmod.unsigned (N.v31594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31594 s i)) at 1.
  unfold R.v31594, N.v31594.
  unfold R.v16463, N.v16463.
  rewrite !state_r1631_nr_5F1638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1631_nr_5F1638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31595 (s : N.State) (i : N.Inputs) :
  R.v31595 (state s) (inputs i) = Zmod.unsigned (N.v31595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31595 s i)) at 1.
  unfold R.v31595, N.v31595.
  unfold R.v16463, N.v16463.
  rewrite !state_r1630_nr_5F1637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1630_nr_5F1637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31596 (s : N.State) (i : N.Inputs) :
  R.v31596 (state s) (inputs i) = Zmod.unsigned (N.v31596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31596 s i)) at 1.
  unfold R.v31596, N.v31596.
  unfold R.v6, N.v6.
  rewrite !state_r1629_nr_5F1636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1629_nr_5F1636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31597 (s : N.State) (i : N.Inputs) :
  R.v31597 (state s) (inputs i) = Zmod.unsigned (N.v31597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31597 s i)) at 1.
  unfold R.v31597, N.v31597.
  unfold R.v19, N.v19.
  rewrite ?node_31596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31598 (s : N.State) (i : N.Inputs) :
  R.v31598 (state s) (inputs i) = Zmod.unsigned (N.v31598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31598 s i)) at 1.
  unfold R.v31598, N.v31598.
  unfold R.v16484, N.v16484.
  rewrite ?node_31597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31599 (s : N.State) (i : N.Inputs) :
  R.v31599 (state s) (inputs i) = Zmod.unsigned (N.v31599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31599 s i)) at 1.
  unfold R.v31599, N.v31599.
  rewrite ?node_31593.
  rewrite ?node_31594.
  rewrite ?node_31595.
  rewrite ?node_31598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31600 (s : N.State) (i : N.Inputs) :
  R.v31600 (state s) (inputs i) = Zmod.unsigned (N.v31600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31600 s i)) at 1.
  unfold R.v31600, N.v31600.
  unfold R.v6, N.v6.
  rewrite ?node_31599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31601 (s : N.State) (i : N.Inputs) :
  R.v31601 (state s) (inputs i) = Zmod.unsigned (N.v31601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31601 s i)) at 1.
  unfold R.v31601, N.v31601.
  rewrite ?node_12804.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31602 (s : N.State) (i : N.Inputs) :
  R.v31602 (state s) (inputs i) = Zmod.unsigned (N.v31602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31602 s i)) at 1.
  unfold R.v31602, N.v31602.
  unfold R.v6, N.v6.
  rewrite ?node_12930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31603 (s : N.State) (i : N.Inputs) :
  R.v31603 (state s) (inputs i) = Zmod.unsigned (N.v31603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31603 s i)) at 1.
  unfold R.v31603, N.v31603.
  unfold R.v6, N.v6.
  rewrite ?node_12978.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31604 (s : N.State) (i : N.Inputs) :
  R.v31604 (state s) (inputs i) = Zmod.unsigned (N.v31604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31604 s i)) at 1.
  unfold R.v31604, N.v31604.
  rewrite ?node_31601.
  rewrite ?node_31602.
  rewrite ?node_31603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31605 (s : N.State) (i : N.Inputs) :
  R.v31605 (state s) (inputs i) = Zmod.unsigned (N.v31605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31605 s i)) at 1.
  unfold R.v31605, N.v31605.
  rewrite ?node_31600.
  rewrite ?node_31604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31606 (s : N.State) (i : N.Inputs) :
  R.v31606 (state s) (inputs i) = Zmod.unsigned (N.v31606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31606 s i)) at 1.
  unfold R.v31606, N.v31606.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31607 (s : N.State) (i : N.Inputs) :
  R.v31607 (state s) (inputs i) = Zmod.unsigned (N.v31607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31607 s i)) at 1.
  unfold R.v31607, N.v31607.
  unfold R.v16463, N.v16463.
  rewrite !state_r1630_nr_5F1637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1630_nr_5F1637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31608 (s : N.State) (i : N.Inputs) :
  R.v31608 (state s) (inputs i) = Zmod.unsigned (N.v31608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31608 s i)) at 1.
  unfold R.v31608, N.v31608.
  unfold R.v6, N.v6.
  rewrite !state_r1629_nr_5F1636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1629_nr_5F1636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31609 (s : N.State) (i : N.Inputs) :
  R.v31609 (state s) (inputs i) = Zmod.unsigned (N.v31609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31609 s i)) at 1.
  unfold R.v31609, N.v31609.
  unfold R.v19, N.v19.
  rewrite ?node_31608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31610 (s : N.State) (i : N.Inputs) :
  R.v31610 (state s) (inputs i) = Zmod.unsigned (N.v31610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31610 s i)) at 1.
  unfold R.v31610, N.v31610.
  unfold R.v16484, N.v16484.
  rewrite ?node_31609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31611 (s : N.State) (i : N.Inputs) :
  R.v31611 (state s) (inputs i) = Zmod.unsigned (N.v31611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31611 s i)) at 1.
  unfold R.v31611, N.v31611.
  rewrite ?node_31607.
  rewrite ?node_31610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31612 (s : N.State) (i : N.Inputs) :
  R.v31612 (state s) (inputs i) = Zmod.unsigned (N.v31612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31612 s i)) at 1.
  unfold R.v31612, N.v31612.
  unfold R.v6, N.v6.
  rewrite ?node_31611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31613 (s : N.State) (i : N.Inputs) :
  R.v31613 (state s) (inputs i) = Zmod.unsigned (N.v31613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31613 s i)) at 1.
  unfold R.v31613, N.v31613.
  rewrite ?node_12799.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31614 (s : N.State) (i : N.Inputs) :
  R.v31614 (state s) (inputs i) = Zmod.unsigned (N.v31614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31614 s i)) at 1.
  unfold R.v31614, N.v31614.
  unfold R.v6, N.v6.
  rewrite ?node_12930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31615 (s : N.State) (i : N.Inputs) :
  R.v31615 (state s) (inputs i) = Zmod.unsigned (N.v31615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31615 s i)) at 1.
  unfold R.v31615, N.v31615.
  rewrite ?node_31613.
  rewrite ?node_31614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31616 (s : N.State) (i : N.Inputs) :
  R.v31616 (state s) (inputs i) = Zmod.unsigned (N.v31616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31616 s i)) at 1.
  unfold R.v31616, N.v31616.
  rewrite ?node_31612.
  rewrite ?node_31615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31617 (s : N.State) (i : N.Inputs) :
  R.v31617 (state s) (inputs i) = Zmod.unsigned (N.v31617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31617 s i)) at 1.
  unfold R.v31617, N.v31617.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31618 (s : N.State) (i : N.Inputs) :
  R.v31618 (state s) (inputs i) = Zmod.unsigned (N.v31618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31618 s i)) at 1.
  unfold R.v31618, N.v31618.
  rewrite ?node_12803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31619 (s : N.State) (i : N.Inputs) :
  R.v31619 (state s) (inputs i) = Zmod.unsigned (N.v31619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31619 s i)) at 1.
  unfold R.v31619, N.v31619.
  unfold R.v6, N.v6.
  rewrite !state_r1631_nr_5F1638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1631_nr_5F1638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31620 (s : N.State) (i : N.Inputs) :
  R.v31620 (state s) (inputs i) = Zmod.unsigned (N.v31620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31620 s i)) at 1.
  unfold R.v31620, N.v31620.
  unfold R.v6, N.v6.
  rewrite ?node_12799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31621 (s : N.State) (i : N.Inputs) :
  R.v31621 (state s) (inputs i) = Zmod.unsigned (N.v31621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31621 s i)) at 1.
  unfold R.v31621, N.v31621.
  rewrite ?node_31619.
  rewrite ?node_31620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31622 (s : N.State) (i : N.Inputs) :
  R.v31622 (state s) (inputs i) = Zmod.unsigned (N.v31622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31622 s i)) at 1.
  unfold R.v31622, N.v31622.
  unfold R.v16484, N.v16484.
  rewrite ?node_31621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31623 (s : N.State) (i : N.Inputs) :
  R.v31623 (state s) (inputs i) = Zmod.unsigned (N.v31623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31623 s i)) at 1.
  unfold R.v31623, N.v31623.
  rewrite ?node_31618.
  rewrite ?node_31622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31624 (s : N.State) (i : N.Inputs) :
  R.v31624 (state s) (inputs i) = Zmod.unsigned (N.v31624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31624 s i)) at 1.
  unfold R.v31624, N.v31624.
  unfold R.v6, N.v6.
  rewrite ?node_31623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31625 (s : N.State) (i : N.Inputs) :
  R.v31625 (state s) (inputs i) = Zmod.unsigned (N.v31625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31625 s i)) at 1.
  unfold R.v31625, N.v31625.
  rewrite ?node_12804.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31626 (s : N.State) (i : N.Inputs) :
  R.v31626 (state s) (inputs i) = Zmod.unsigned (N.v31626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31626 s i)) at 1.
  unfold R.v31626, N.v31626.
  unfold R.v6, N.v6.
  rewrite ?node_12978.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31627 (s : N.State) (i : N.Inputs) :
  R.v31627 (state s) (inputs i) = Zmod.unsigned (N.v31627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31627 s i)) at 1.
  unfold R.v31627, N.v31627.
  rewrite ?node_31625.
  rewrite ?node_31626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31628 (s : N.State) (i : N.Inputs) :
  R.v31628 (state s) (inputs i) = Zmod.unsigned (N.v31628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31628 s i)) at 1.
  unfold R.v31628, N.v31628.
  rewrite ?node_31624.
  rewrite ?node_31627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31629 (s : N.State) (i : N.Inputs) :
  R.v31629 (state s) (inputs i) = Zmod.unsigned (N.v31629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31629 s i)) at 1.
  unfold R.v31629, N.v31629.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31630 (s : N.State) (i : N.Inputs) :
  R.v31630 (state s) (inputs i) = Zmod.unsigned (N.v31630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31630 s i)) at 1.
  unfold R.v31630, N.v31630.
  rewrite ?node_12810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31631 (s : N.State) (i : N.Inputs) :
  R.v31631 (state s) (inputs i) = Zmod.unsigned (N.v31631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31631 s i)) at 1.
  unfold R.v31631, N.v31631.
  unfold R.v16463, N.v16463.
  rewrite !state_r1635_nr_5F1642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1635_nr_5F1642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31632 (s : N.State) (i : N.Inputs) :
  R.v31632 (state s) (inputs i) = Zmod.unsigned (N.v31632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31632 s i)) at 1.
  unfold R.v31632, N.v31632.
  unfold R.v16463, N.v16463.
  rewrite !state_r1634_nr_5F1641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1634_nr_5F1641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31633 (s : N.State) (i : N.Inputs) :
  R.v31633 (state s) (inputs i) = Zmod.unsigned (N.v31633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31633 s i)) at 1.
  unfold R.v31633, N.v31633.
  unfold R.v6, N.v6.
  rewrite !state_r1633_nr_5F1640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1633_nr_5F1640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31634 (s : N.State) (i : N.Inputs) :
  R.v31634 (state s) (inputs i) = Zmod.unsigned (N.v31634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31634 s i)) at 1.
  unfold R.v31634, N.v31634.
  unfold R.v6, N.v6.
  rewrite !state_r1632_nr_5F1639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1632_nr_5F1639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31635 (s : N.State) (i : N.Inputs) :
  R.v31635 (state s) (inputs i) = Zmod.unsigned (N.v31635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31635 s i)) at 1.
  unfold R.v31635, N.v31635.
  rewrite ?node_31633.
  rewrite ?node_31634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31636 (s : N.State) (i : N.Inputs) :
  R.v31636 (state s) (inputs i) = Zmod.unsigned (N.v31636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31636 s i)) at 1.
  unfold R.v31636, N.v31636.
  unfold R.v16484, N.v16484.
  rewrite ?node_31635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31637 (s : N.State) (i : N.Inputs) :
  R.v31637 (state s) (inputs i) = Zmod.unsigned (N.v31637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31637 s i)) at 1.
  unfold R.v31637, N.v31637.
  rewrite ?node_31630.
  rewrite ?node_31631.
  rewrite ?node_31632.
  rewrite ?node_31636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31638 (s : N.State) (i : N.Inputs) :
  R.v31638 (state s) (inputs i) = Zmod.unsigned (N.v31638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31638 s i)) at 1.
  unfold R.v31638, N.v31638.
  unfold R.v6, N.v6.
  rewrite ?node_31637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31639 (s : N.State) (i : N.Inputs) :
  R.v31639 (state s) (inputs i) = Zmod.unsigned (N.v31639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31639 s i)) at 1.
  unfold R.v31639, N.v31639.
  rewrite ?node_12811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31640 (s : N.State) (i : N.Inputs) :
  R.v31640 (state s) (inputs i) = Zmod.unsigned (N.v31640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31640 s i)) at 1.
  unfold R.v31640, N.v31640.
  unfold R.v6, N.v6.
  rewrite ?node_12937.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31641 (s : N.State) (i : N.Inputs) :
  R.v31641 (state s) (inputs i) = Zmod.unsigned (N.v31641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31641 s i)) at 1.
  unfold R.v31641, N.v31641.
  unfold R.v6, N.v6.
  rewrite ?node_12987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31642 (s : N.State) (i : N.Inputs) :
  R.v31642 (state s) (inputs i) = Zmod.unsigned (N.v31642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31642 s i)) at 1.
  unfold R.v31642, N.v31642.
  rewrite ?node_31639.
  rewrite ?node_31640.
  rewrite ?node_31641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31643 (s : N.State) (i : N.Inputs) :
  R.v31643 (state s) (inputs i) = Zmod.unsigned (N.v31643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31643 s i)) at 1.
  unfold R.v31643, N.v31643.
  rewrite ?node_31638.
  rewrite ?node_31642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31644 (s : N.State) (i : N.Inputs) :
  R.v31644 (state s) (inputs i) = Zmod.unsigned (N.v31644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31644 s i)) at 1.
  unfold R.v31644, N.v31644.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31645 (s : N.State) (i : N.Inputs) :
  R.v31645 (state s) (inputs i) = Zmod.unsigned (N.v31645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31645 s i)) at 1.
  unfold R.v31645, N.v31645.
  unfold R.v16463, N.v16463.
  rewrite !state_r1634_nr_5F1641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1634_nr_5F1641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31646 (s : N.State) (i : N.Inputs) :
  R.v31646 (state s) (inputs i) = Zmod.unsigned (N.v31646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31646 s i)) at 1.
  unfold R.v31646, N.v31646.
  unfold R.v6, N.v6.
  rewrite !state_r1633_nr_5F1640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1633_nr_5F1640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31647 (s : N.State) (i : N.Inputs) :
  R.v31647 (state s) (inputs i) = Zmod.unsigned (N.v31647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31647 s i)) at 1.
  unfold R.v31647, N.v31647.
  unfold R.v6, N.v6.
  rewrite !state_r1632_nr_5F1639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1632_nr_5F1639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31648 (s : N.State) (i : N.Inputs) :
  R.v31648 (state s) (inputs i) = Zmod.unsigned (N.v31648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31648 s i)) at 1.
  unfold R.v31648, N.v31648.
  rewrite ?node_31646.
  rewrite ?node_31647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31649 (s : N.State) (i : N.Inputs) :
  R.v31649 (state s) (inputs i) = Zmod.unsigned (N.v31649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31649 s i)) at 1.
  unfold R.v31649, N.v31649.
  unfold R.v16484, N.v16484.
  rewrite ?node_31648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31650 (s : N.State) (i : N.Inputs) :
  R.v31650 (state s) (inputs i) = Zmod.unsigned (N.v31650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31650 s i)) at 1.
  unfold R.v31650, N.v31650.
  rewrite ?node_31645.
  rewrite ?node_31649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31651 (s : N.State) (i : N.Inputs) :
  R.v31651 (state s) (inputs i) = Zmod.unsigned (N.v31651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31651 s i)) at 1.
  unfold R.v31651, N.v31651.
  unfold R.v6, N.v6.
  rewrite ?node_31650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31652 (s : N.State) (i : N.Inputs) :
  R.v31652 (state s) (inputs i) = Zmod.unsigned (N.v31652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31652 s i)) at 1.
  unfold R.v31652, N.v31652.
  rewrite ?node_12806.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31653 (s : N.State) (i : N.Inputs) :
  R.v31653 (state s) (inputs i) = Zmod.unsigned (N.v31653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31653 s i)) at 1.
  unfold R.v31653, N.v31653.
  unfold R.v6, N.v6.
  rewrite ?node_12937.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31654 (s : N.State) (i : N.Inputs) :
  R.v31654 (state s) (inputs i) = Zmod.unsigned (N.v31654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31654 s i)) at 1.
  unfold R.v31654, N.v31654.
  rewrite ?node_31652.
  rewrite ?node_31653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31655 (s : N.State) (i : N.Inputs) :
  R.v31655 (state s) (inputs i) = Zmod.unsigned (N.v31655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31655 s i)) at 1.
  unfold R.v31655, N.v31655.
  rewrite ?node_31651.
  rewrite ?node_31654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31656 (s : N.State) (i : N.Inputs) :
  R.v31656 (state s) (inputs i) = Zmod.unsigned (N.v31656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31656 s i)) at 1.
  unfold R.v31656, N.v31656.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31657 (s : N.State) (i : N.Inputs) :
  R.v31657 (state s) (inputs i) = Zmod.unsigned (N.v31657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31657 s i)) at 1.
  unfold R.v31657, N.v31657.
  rewrite ?node_12810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31658 (s : N.State) (i : N.Inputs) :
  R.v31658 (state s) (inputs i) = Zmod.unsigned (N.v31658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31658 s i)) at 1.
  unfold R.v31658, N.v31658.
  unfold R.v6, N.v6.
  rewrite !state_r1635_nr_5F1642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1635_nr_5F1642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31659 (s : N.State) (i : N.Inputs) :
  R.v31659 (state s) (inputs i) = Zmod.unsigned (N.v31659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31659 s i)) at 1.
  unfold R.v31659, N.v31659.
  unfold R.v6, N.v6.
  rewrite ?node_12806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31660 (s : N.State) (i : N.Inputs) :
  R.v31660 (state s) (inputs i) = Zmod.unsigned (N.v31660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31660 s i)) at 1.
  unfold R.v31660, N.v31660.
  rewrite ?node_31658.
  rewrite ?node_31659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31661 (s : N.State) (i : N.Inputs) :
  R.v31661 (state s) (inputs i) = Zmod.unsigned (N.v31661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31661 s i)) at 1.
  unfold R.v31661, N.v31661.
  unfold R.v16484, N.v16484.
  rewrite ?node_31660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31662 (s : N.State) (i : N.Inputs) :
  R.v31662 (state s) (inputs i) = Zmod.unsigned (N.v31662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31662 s i)) at 1.
  unfold R.v31662, N.v31662.
  rewrite ?node_31657.
  rewrite ?node_31661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31663 (s : N.State) (i : N.Inputs) :
  R.v31663 (state s) (inputs i) = Zmod.unsigned (N.v31663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31663 s i)) at 1.
  unfold R.v31663, N.v31663.
  unfold R.v6, N.v6.
  rewrite ?node_31662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31664 (s : N.State) (i : N.Inputs) :
  R.v31664 (state s) (inputs i) = Zmod.unsigned (N.v31664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31664 s i)) at 1.
  unfold R.v31664, N.v31664.
  rewrite ?node_12811.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31665 (s : N.State) (i : N.Inputs) :
  R.v31665 (state s) (inputs i) = Zmod.unsigned (N.v31665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31665 s i)) at 1.
  unfold R.v31665, N.v31665.
  unfold R.v6, N.v6.
  rewrite ?node_12987.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31666 (s : N.State) (i : N.Inputs) :
  R.v31666 (state s) (inputs i) = Zmod.unsigned (N.v31666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31666 s i)) at 1.
  unfold R.v31666, N.v31666.
  rewrite ?node_31664.
  rewrite ?node_31665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31667 (s : N.State) (i : N.Inputs) :
  R.v31667 (state s) (inputs i) = Zmod.unsigned (N.v31667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31667 s i)) at 1.
  unfold R.v31667, N.v31667.
  rewrite ?node_31663.
  rewrite ?node_31666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31668 (s : N.State) (i : N.Inputs) :
  R.v31668 (state s) (inputs i) = Zmod.unsigned (N.v31668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31668 s i)) at 1.
  unfold R.v31668, N.v31668.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31669 (s : N.State) (i : N.Inputs) :
  R.v31669 (state s) (inputs i) = Zmod.unsigned (N.v31669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31669 s i)) at 1.
  unfold R.v31669, N.v31669.
  rewrite ?node_12818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31670 (s : N.State) (i : N.Inputs) :
  R.v31670 (state s) (inputs i) = Zmod.unsigned (N.v31670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31670 s i)) at 1.
  unfold R.v31670, N.v31670.
  unfold R.v16463, N.v16463.
  rewrite !state_r1639_nr_5F1646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1639_nr_5F1646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31671 (s : N.State) (i : N.Inputs) :
  R.v31671 (state s) (inputs i) = Zmod.unsigned (N.v31671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31671 s i)) at 1.
  unfold R.v31671, N.v31671.
  unfold R.v16463, N.v16463.
  rewrite !state_r1638_nr_5F1645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1638_nr_5F1645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31672 (s : N.State) (i : N.Inputs) :
  R.v31672 (state s) (inputs i) = Zmod.unsigned (N.v31672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31672 s i)) at 1.
  unfold R.v31672, N.v31672.
  unfold R.v6, N.v6.
  rewrite !state_r1637_nr_5F1644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1637_nr_5F1644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31673 (s : N.State) (i : N.Inputs) :
  R.v31673 (state s) (inputs i) = Zmod.unsigned (N.v31673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31673 s i)) at 1.
  unfold R.v31673, N.v31673.
  unfold R.v6, N.v6.
  rewrite !state_r1636_nr_5F1643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1636_nr_5F1643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31674 (s : N.State) (i : N.Inputs) :
  R.v31674 (state s) (inputs i) = Zmod.unsigned (N.v31674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31674 s i)) at 1.
  unfold R.v31674, N.v31674.
  rewrite ?node_31672.
  rewrite ?node_31673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31675 (s : N.State) (i : N.Inputs) :
  R.v31675 (state s) (inputs i) = Zmod.unsigned (N.v31675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31675 s i)) at 1.
  unfold R.v31675, N.v31675.
  unfold R.v16484, N.v16484.
  rewrite ?node_31674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31676 (s : N.State) (i : N.Inputs) :
  R.v31676 (state s) (inputs i) = Zmod.unsigned (N.v31676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31676 s i)) at 1.
  unfold R.v31676, N.v31676.
  rewrite ?node_31669.
  rewrite ?node_31670.
  rewrite ?node_31671.
  rewrite ?node_31675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31677 (s : N.State) (i : N.Inputs) :
  R.v31677 (state s) (inputs i) = Zmod.unsigned (N.v31677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31677 s i)) at 1.
  unfold R.v31677, N.v31677.
  unfold R.v6, N.v6.
  rewrite ?node_31676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31678 (s : N.State) (i : N.Inputs) :
  R.v31678 (state s) (inputs i) = Zmod.unsigned (N.v31678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31678 s i)) at 1.
  unfold R.v31678, N.v31678.
  rewrite ?node_12819.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31679 (s : N.State) (i : N.Inputs) :
  R.v31679 (state s) (inputs i) = Zmod.unsigned (N.v31679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31679 s i)) at 1.
  unfold R.v31679, N.v31679.
  unfold R.v6, N.v6.
  rewrite ?node_12945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31680 (s : N.State) (i : N.Inputs) :
  R.v31680 (state s) (inputs i) = Zmod.unsigned (N.v31680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31680 s i)) at 1.
  unfold R.v31680, N.v31680.
  unfold R.v6, N.v6.
  rewrite ?node_12990.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31681 (s : N.State) (i : N.Inputs) :
  R.v31681 (state s) (inputs i) = Zmod.unsigned (N.v31681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31681 s i)) at 1.
  unfold R.v31681, N.v31681.
  rewrite ?node_31678.
  rewrite ?node_31679.
  rewrite ?node_31680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31682 (s : N.State) (i : N.Inputs) :
  R.v31682 (state s) (inputs i) = Zmod.unsigned (N.v31682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31682 s i)) at 1.
  unfold R.v31682, N.v31682.
  rewrite ?node_31677.
  rewrite ?node_31681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31683 (s : N.State) (i : N.Inputs) :
  R.v31683 (state s) (inputs i) = Zmod.unsigned (N.v31683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31683 s i)) at 1.
  unfold R.v31683, N.v31683.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31684 (s : N.State) (i : N.Inputs) :
  R.v31684 (state s) (inputs i) = Zmod.unsigned (N.v31684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31684 s i)) at 1.
  unfold R.v31684, N.v31684.
  unfold R.v16463, N.v16463.
  rewrite !state_r1638_nr_5F1645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1638_nr_5F1645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31685 (s : N.State) (i : N.Inputs) :
  R.v31685 (state s) (inputs i) = Zmod.unsigned (N.v31685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31685 s i)) at 1.
  unfold R.v31685, N.v31685.
  unfold R.v6, N.v6.
  rewrite !state_r1637_nr_5F1644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1637_nr_5F1644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31686 (s : N.State) (i : N.Inputs) :
  R.v31686 (state s) (inputs i) = Zmod.unsigned (N.v31686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31686 s i)) at 1.
  unfold R.v31686, N.v31686.
  unfold R.v6, N.v6.
  rewrite !state_r1636_nr_5F1643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1636_nr_5F1643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31687 (s : N.State) (i : N.Inputs) :
  R.v31687 (state s) (inputs i) = Zmod.unsigned (N.v31687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31687 s i)) at 1.
  unfold R.v31687, N.v31687.
  rewrite ?node_31685.
  rewrite ?node_31686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31688 (s : N.State) (i : N.Inputs) :
  R.v31688 (state s) (inputs i) = Zmod.unsigned (N.v31688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31688 s i)) at 1.
  unfold R.v31688, N.v31688.
  unfold R.v16484, N.v16484.
  rewrite ?node_31687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31689 (s : N.State) (i : N.Inputs) :
  R.v31689 (state s) (inputs i) = Zmod.unsigned (N.v31689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31689 s i)) at 1.
  unfold R.v31689, N.v31689.
  rewrite ?node_31684.
  rewrite ?node_31688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31690 (s : N.State) (i : N.Inputs) :
  R.v31690 (state s) (inputs i) = Zmod.unsigned (N.v31690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31690 s i)) at 1.
  unfold R.v31690, N.v31690.
  unfold R.v6, N.v6.
  rewrite ?node_31689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31691 (s : N.State) (i : N.Inputs) :
  R.v31691 (state s) (inputs i) = Zmod.unsigned (N.v31691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31691 s i)) at 1.
  unfold R.v31691, N.v31691.
  rewrite ?node_12814.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31692 (s : N.State) (i : N.Inputs) :
  R.v31692 (state s) (inputs i) = Zmod.unsigned (N.v31692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31692 s i)) at 1.
  unfold R.v31692, N.v31692.
  unfold R.v6, N.v6.
  rewrite ?node_12945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31693 (s : N.State) (i : N.Inputs) :
  R.v31693 (state s) (inputs i) = Zmod.unsigned (N.v31693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31693 s i)) at 1.
  unfold R.v31693, N.v31693.
  rewrite ?node_31691.
  rewrite ?node_31692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31694 (s : N.State) (i : N.Inputs) :
  R.v31694 (state s) (inputs i) = Zmod.unsigned (N.v31694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31694 s i)) at 1.
  unfold R.v31694, N.v31694.
  rewrite ?node_31690.
  rewrite ?node_31693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31695 (s : N.State) (i : N.Inputs) :
  R.v31695 (state s) (inputs i) = Zmod.unsigned (N.v31695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31695 s i)) at 1.
  unfold R.v31695, N.v31695.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31696 (s : N.State) (i : N.Inputs) :
  R.v31696 (state s) (inputs i) = Zmod.unsigned (N.v31696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31696 s i)) at 1.
  unfold R.v31696, N.v31696.
  rewrite ?node_12818.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31697 (s : N.State) (i : N.Inputs) :
  R.v31697 (state s) (inputs i) = Zmod.unsigned (N.v31697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31697 s i)) at 1.
  unfold R.v31697, N.v31697.
  unfold R.v6, N.v6.
  rewrite !state_r1639_nr_5F1646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1639_nr_5F1646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31698 (s : N.State) (i : N.Inputs) :
  R.v31698 (state s) (inputs i) = Zmod.unsigned (N.v31698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31698 s i)) at 1.
  unfold R.v31698, N.v31698.
  unfold R.v6, N.v6.
  rewrite ?node_12814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31699 (s : N.State) (i : N.Inputs) :
  R.v31699 (state s) (inputs i) = Zmod.unsigned (N.v31699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31699 s i)) at 1.
  unfold R.v31699, N.v31699.
  rewrite ?node_31697.
  rewrite ?node_31698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31700 (s : N.State) (i : N.Inputs) :
  R.v31700 (state s) (inputs i) = Zmod.unsigned (N.v31700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31700 s i)) at 1.
  unfold R.v31700, N.v31700.
  unfold R.v16484, N.v16484.
  rewrite ?node_31699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31701 (s : N.State) (i : N.Inputs) :
  R.v31701 (state s) (inputs i) = Zmod.unsigned (N.v31701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31701 s i)) at 1.
  unfold R.v31701, N.v31701.
  rewrite ?node_31696.
  rewrite ?node_31700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31702 (s : N.State) (i : N.Inputs) :
  R.v31702 (state s) (inputs i) = Zmod.unsigned (N.v31702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31702 s i)) at 1.
  unfold R.v31702, N.v31702.
  unfold R.v6, N.v6.
  rewrite ?node_31701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31703 (s : N.State) (i : N.Inputs) :
  R.v31703 (state s) (inputs i) = Zmod.unsigned (N.v31703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31703 s i)) at 1.
  unfold R.v31703, N.v31703.
  rewrite ?node_12819.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31704 (s : N.State) (i : N.Inputs) :
  R.v31704 (state s) (inputs i) = Zmod.unsigned (N.v31704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31704 s i)) at 1.
  unfold R.v31704, N.v31704.
  unfold R.v6, N.v6.
  rewrite ?node_12990.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31705 (s : N.State) (i : N.Inputs) :
  R.v31705 (state s) (inputs i) = Zmod.unsigned (N.v31705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31705 s i)) at 1.
  unfold R.v31705, N.v31705.
  rewrite ?node_31703.
  rewrite ?node_31704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31706 (s : N.State) (i : N.Inputs) :
  R.v31706 (state s) (inputs i) = Zmod.unsigned (N.v31706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31706 s i)) at 1.
  unfold R.v31706, N.v31706.
  rewrite ?node_31702.
  rewrite ?node_31705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31707 (s : N.State) (i : N.Inputs) :
  R.v31707 (state s) (inputs i) = Zmod.unsigned (N.v31707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31707 s i)) at 1.
  unfold R.v31707, N.v31707.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31708 (s : N.State) (i : N.Inputs) :
  R.v31708 (state s) (inputs i) = Zmod.unsigned (N.v31708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31708 s i)) at 1.
  unfold R.v31708, N.v31708.
  rewrite ?node_12826.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31709 (s : N.State) (i : N.Inputs) :
  R.v31709 (state s) (inputs i) = Zmod.unsigned (N.v31709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31709 s i)) at 1.
  unfold R.v31709, N.v31709.
  unfold R.v16463, N.v16463.
  rewrite !state_r1643_nr_5F1650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1643_nr_5F1650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31710 (s : N.State) (i : N.Inputs) :
  R.v31710 (state s) (inputs i) = Zmod.unsigned (N.v31710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31710 s i)) at 1.
  unfold R.v31710, N.v31710.
  unfold R.v16463, N.v16463.
  rewrite !state_r1642_nr_5F1649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1642_nr_5F1649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31711 (s : N.State) (i : N.Inputs) :
  R.v31711 (state s) (inputs i) = Zmod.unsigned (N.v31711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31711 s i)) at 1.
  unfold R.v31711, N.v31711.
  unfold R.v6, N.v6.
  rewrite !state_r1641_nr_5F1648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1641_nr_5F1648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31712 (s : N.State) (i : N.Inputs) :
  R.v31712 (state s) (inputs i) = Zmod.unsigned (N.v31712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31712 s i)) at 1.
  unfold R.v31712, N.v31712.
  unfold R.v6, N.v6.
  rewrite !state_r1640_nr_5F1647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1640_nr_5F1647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31713 (s : N.State) (i : N.Inputs) :
  R.v31713 (state s) (inputs i) = Zmod.unsigned (N.v31713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31713 s i)) at 1.
  unfold R.v31713, N.v31713.
  rewrite ?node_31711.
  rewrite ?node_31712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31714 (s : N.State) (i : N.Inputs) :
  R.v31714 (state s) (inputs i) = Zmod.unsigned (N.v31714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31714 s i)) at 1.
  unfold R.v31714, N.v31714.
  unfold R.v16484, N.v16484.
  rewrite ?node_31713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31715 (s : N.State) (i : N.Inputs) :
  R.v31715 (state s) (inputs i) = Zmod.unsigned (N.v31715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31715 s i)) at 1.
  unfold R.v31715, N.v31715.
  rewrite ?node_31708.
  rewrite ?node_31709.
  rewrite ?node_31710.
  rewrite ?node_31714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31716 (s : N.State) (i : N.Inputs) :
  R.v31716 (state s) (inputs i) = Zmod.unsigned (N.v31716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31716 s i)) at 1.
  unfold R.v31716, N.v31716.
  unfold R.v6, N.v6.
  rewrite ?node_31715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31717 (s : N.State) (i : N.Inputs) :
  R.v31717 (state s) (inputs i) = Zmod.unsigned (N.v31717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31717 s i)) at 1.
  unfold R.v31717, N.v31717.
  rewrite ?node_12827.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31718 (s : N.State) (i : N.Inputs) :
  R.v31718 (state s) (inputs i) = Zmod.unsigned (N.v31718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31718 s i)) at 1.
  unfold R.v31718, N.v31718.
  unfold R.v6, N.v6.
  rewrite ?node_12953.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31719 (s : N.State) (i : N.Inputs) :
  R.v31719 (state s) (inputs i) = Zmod.unsigned (N.v31719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31719 s i)) at 1.
  unfold R.v31719, N.v31719.
  unfold R.v6, N.v6.
  rewrite ?node_12994.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31720 (s : N.State) (i : N.Inputs) :
  R.v31720 (state s) (inputs i) = Zmod.unsigned (N.v31720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31720 s i)) at 1.
  unfold R.v31720, N.v31720.
  rewrite ?node_31717.
  rewrite ?node_31718.
  rewrite ?node_31719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31721 (s : N.State) (i : N.Inputs) :
  R.v31721 (state s) (inputs i) = Zmod.unsigned (N.v31721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31721 s i)) at 1.
  unfold R.v31721, N.v31721.
  rewrite ?node_31716.
  rewrite ?node_31720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31722 (s : N.State) (i : N.Inputs) :
  R.v31722 (state s) (inputs i) = Zmod.unsigned (N.v31722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31722 s i)) at 1.
  unfold R.v31722, N.v31722.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31723 (s : N.State) (i : N.Inputs) :
  R.v31723 (state s) (inputs i) = Zmod.unsigned (N.v31723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31723 s i)) at 1.
  unfold R.v31723, N.v31723.
  unfold R.v16463, N.v16463.
  rewrite !state_r1642_nr_5F1649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1642_nr_5F1649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31724 (s : N.State) (i : N.Inputs) :
  R.v31724 (state s) (inputs i) = Zmod.unsigned (N.v31724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31724 s i)) at 1.
  unfold R.v31724, N.v31724.
  unfold R.v6, N.v6.
  rewrite !state_r1641_nr_5F1648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1641_nr_5F1648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31725 (s : N.State) (i : N.Inputs) :
  R.v31725 (state s) (inputs i) = Zmod.unsigned (N.v31725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31725 s i)) at 1.
  unfold R.v31725, N.v31725.
  unfold R.v6, N.v6.
  rewrite !state_r1640_nr_5F1647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1640_nr_5F1647 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31726 (s : N.State) (i : N.Inputs) :
  R.v31726 (state s) (inputs i) = Zmod.unsigned (N.v31726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31726 s i)) at 1.
  unfold R.v31726, N.v31726.
  rewrite ?node_31724.
  rewrite ?node_31725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31727 (s : N.State) (i : N.Inputs) :
  R.v31727 (state s) (inputs i) = Zmod.unsigned (N.v31727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31727 s i)) at 1.
  unfold R.v31727, N.v31727.
  unfold R.v16484, N.v16484.
  rewrite ?node_31726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31728 (s : N.State) (i : N.Inputs) :
  R.v31728 (state s) (inputs i) = Zmod.unsigned (N.v31728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31728 s i)) at 1.
  unfold R.v31728, N.v31728.
  rewrite ?node_31723.
  rewrite ?node_31727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31729 (s : N.State) (i : N.Inputs) :
  R.v31729 (state s) (inputs i) = Zmod.unsigned (N.v31729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31729 s i)) at 1.
  unfold R.v31729, N.v31729.
  unfold R.v6, N.v6.
  rewrite ?node_31728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31730 (s : N.State) (i : N.Inputs) :
  R.v31730 (state s) (inputs i) = Zmod.unsigned (N.v31730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31730 s i)) at 1.
  unfold R.v31730, N.v31730.
  rewrite ?node_12822.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31731 (s : N.State) (i : N.Inputs) :
  R.v31731 (state s) (inputs i) = Zmod.unsigned (N.v31731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31731 s i)) at 1.
  unfold R.v31731, N.v31731.
  unfold R.v6, N.v6.
  rewrite ?node_12953.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31732 (s : N.State) (i : N.Inputs) :
  R.v31732 (state s) (inputs i) = Zmod.unsigned (N.v31732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31732 s i)) at 1.
  unfold R.v31732, N.v31732.
  rewrite ?node_31730.
  rewrite ?node_31731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31733 (s : N.State) (i : N.Inputs) :
  R.v31733 (state s) (inputs i) = Zmod.unsigned (N.v31733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31733 s i)) at 1.
  unfold R.v31733, N.v31733.
  rewrite ?node_31729.
  rewrite ?node_31732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31734 (s : N.State) (i : N.Inputs) :
  R.v31734 (state s) (inputs i) = Zmod.unsigned (N.v31734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31734 s i)) at 1.
  unfold R.v31734, N.v31734.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31735 (s : N.State) (i : N.Inputs) :
  R.v31735 (state s) (inputs i) = Zmod.unsigned (N.v31735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31735 s i)) at 1.
  unfold R.v31735, N.v31735.
  rewrite ?node_12826.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31736 (s : N.State) (i : N.Inputs) :
  R.v31736 (state s) (inputs i) = Zmod.unsigned (N.v31736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31736 s i)) at 1.
  unfold R.v31736, N.v31736.
  unfold R.v6, N.v6.
  rewrite !state_r1643_nr_5F1650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1643_nr_5F1650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31737 (s : N.State) (i : N.Inputs) :
  R.v31737 (state s) (inputs i) = Zmod.unsigned (N.v31737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31737 s i)) at 1.
  unfold R.v31737, N.v31737.
  unfold R.v6, N.v6.
  rewrite ?node_12822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31738 (s : N.State) (i : N.Inputs) :
  R.v31738 (state s) (inputs i) = Zmod.unsigned (N.v31738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31738 s i)) at 1.
  unfold R.v31738, N.v31738.
  rewrite ?node_31736.
  rewrite ?node_31737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31739 (s : N.State) (i : N.Inputs) :
  R.v31739 (state s) (inputs i) = Zmod.unsigned (N.v31739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31739 s i)) at 1.
  unfold R.v31739, N.v31739.
  unfold R.v16484, N.v16484.
  rewrite ?node_31738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31740 (s : N.State) (i : N.Inputs) :
  R.v31740 (state s) (inputs i) = Zmod.unsigned (N.v31740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31740 s i)) at 1.
  unfold R.v31740, N.v31740.
  rewrite ?node_31735.
  rewrite ?node_31739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31741 (s : N.State) (i : N.Inputs) :
  R.v31741 (state s) (inputs i) = Zmod.unsigned (N.v31741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31741 s i)) at 1.
  unfold R.v31741, N.v31741.
  unfold R.v6, N.v6.
  rewrite ?node_31740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31742 (s : N.State) (i : N.Inputs) :
  R.v31742 (state s) (inputs i) = Zmod.unsigned (N.v31742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31742 s i)) at 1.
  unfold R.v31742, N.v31742.
  rewrite ?node_12827.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31743 (s : N.State) (i : N.Inputs) :
  R.v31743 (state s) (inputs i) = Zmod.unsigned (N.v31743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31743 s i)) at 1.
  unfold R.v31743, N.v31743.
  unfold R.v6, N.v6.
  rewrite ?node_12994.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31744 (s : N.State) (i : N.Inputs) :
  R.v31744 (state s) (inputs i) = Zmod.unsigned (N.v31744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31744 s i)) at 1.
  unfold R.v31744, N.v31744.
  rewrite ?node_31742.
  rewrite ?node_31743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31745 (s : N.State) (i : N.Inputs) :
  R.v31745 (state s) (inputs i) = Zmod.unsigned (N.v31745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31745 s i)) at 1.
  unfold R.v31745, N.v31745.
  rewrite ?node_31741.
  rewrite ?node_31744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31746 (s : N.State) (i : N.Inputs) :
  R.v31746 (state s) (inputs i) = Zmod.unsigned (N.v31746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31746 s i)) at 1.
  unfold R.v31746, N.v31746.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31747 (s : N.State) (i : N.Inputs) :
  R.v31747 (state s) (inputs i) = Zmod.unsigned (N.v31747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31747 s i)) at 1.
  unfold R.v31747, N.v31747.
  rewrite ?node_12838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31748 (s : N.State) (i : N.Inputs) :
  R.v31748 (state s) (inputs i) = Zmod.unsigned (N.v31748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31748 s i)) at 1.
  unfold R.v31748, N.v31748.
  unfold R.v16463, N.v16463.
  rewrite !state_r1647_nr_5F1654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1647_nr_5F1654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31749 (s : N.State) (i : N.Inputs) :
  R.v31749 (state s) (inputs i) = Zmod.unsigned (N.v31749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31749 s i)) at 1.
  unfold R.v31749, N.v31749.
  unfold R.v16463, N.v16463.
  rewrite !state_r1646_nr_5F1653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1646_nr_5F1653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31750 (s : N.State) (i : N.Inputs) :
  R.v31750 (state s) (inputs i) = Zmod.unsigned (N.v31750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31750 s i)) at 1.
  unfold R.v31750, N.v31750.
  unfold R.v6, N.v6.
  rewrite !state_r1645_nr_5F1652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1645_nr_5F1652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31751 (s : N.State) (i : N.Inputs) :
  R.v31751 (state s) (inputs i) = Zmod.unsigned (N.v31751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31751 s i)) at 1.
  unfold R.v31751, N.v31751.
  unfold R.v6, N.v6.
  rewrite !state_r1644_nr_5F1651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1644_nr_5F1651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31752 (s : N.State) (i : N.Inputs) :
  R.v31752 (state s) (inputs i) = Zmod.unsigned (N.v31752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31752 s i)) at 1.
  unfold R.v31752, N.v31752.
  rewrite ?node_31750.
  rewrite ?node_31751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31753 (s : N.State) (i : N.Inputs) :
  R.v31753 (state s) (inputs i) = Zmod.unsigned (N.v31753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31753 s i)) at 1.
  unfold R.v31753, N.v31753.
  unfold R.v16484, N.v16484.
  rewrite ?node_31752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31754 (s : N.State) (i : N.Inputs) :
  R.v31754 (state s) (inputs i) = Zmod.unsigned (N.v31754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31754 s i)) at 1.
  unfold R.v31754, N.v31754.
  rewrite ?node_31747.
  rewrite ?node_31748.
  rewrite ?node_31749.
  rewrite ?node_31753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31755 (s : N.State) (i : N.Inputs) :
  R.v31755 (state s) (inputs i) = Zmod.unsigned (N.v31755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31755 s i)) at 1.
  unfold R.v31755, N.v31755.
  unfold R.v6, N.v6.
  rewrite ?node_31754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31756 (s : N.State) (i : N.Inputs) :
  R.v31756 (state s) (inputs i) = Zmod.unsigned (N.v31756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31756 s i)) at 1.
  unfold R.v31756, N.v31756.
  rewrite ?node_12839.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31757 (s : N.State) (i : N.Inputs) :
  R.v31757 (state s) (inputs i) = Zmod.unsigned (N.v31757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31757 s i)) at 1.
  unfold R.v31757, N.v31757.
  unfold R.v6, N.v6.
  rewrite ?node_12965.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31758 (s : N.State) (i : N.Inputs) :
  R.v31758 (state s) (inputs i) = Zmod.unsigned (N.v31758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31758 s i)) at 1.
  unfold R.v31758, N.v31758.
  unfold R.v6, N.v6.
  rewrite ?node_12998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31759 (s : N.State) (i : N.Inputs) :
  R.v31759 (state s) (inputs i) = Zmod.unsigned (N.v31759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31759 s i)) at 1.
  unfold R.v31759, N.v31759.
  rewrite ?node_31756.
  rewrite ?node_31757.
  rewrite ?node_31758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31760 (s : N.State) (i : N.Inputs) :
  R.v31760 (state s) (inputs i) = Zmod.unsigned (N.v31760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31760 s i)) at 1.
  unfold R.v31760, N.v31760.
  rewrite ?node_31755.
  rewrite ?node_31759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31761 (s : N.State) (i : N.Inputs) :
  R.v31761 (state s) (inputs i) = Zmod.unsigned (N.v31761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31761 s i)) at 1.
  unfold R.v31761, N.v31761.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31762 (s : N.State) (i : N.Inputs) :
  R.v31762 (state s) (inputs i) = Zmod.unsigned (N.v31762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31762 s i)) at 1.
  unfold R.v31762, N.v31762.
  unfold R.v16463, N.v16463.
  rewrite !state_r1646_nr_5F1653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1646_nr_5F1653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31763 (s : N.State) (i : N.Inputs) :
  R.v31763 (state s) (inputs i) = Zmod.unsigned (N.v31763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31763 s i)) at 1.
  unfold R.v31763, N.v31763.
  unfold R.v6, N.v6.
  rewrite !state_r1645_nr_5F1652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1645_nr_5F1652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31764 (s : N.State) (i : N.Inputs) :
  R.v31764 (state s) (inputs i) = Zmod.unsigned (N.v31764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31764 s i)) at 1.
  unfold R.v31764, N.v31764.
  unfold R.v6, N.v6.
  rewrite !state_r1644_nr_5F1651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1644_nr_5F1651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31765 (s : N.State) (i : N.Inputs) :
  R.v31765 (state s) (inputs i) = Zmod.unsigned (N.v31765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31765 s i)) at 1.
  unfold R.v31765, N.v31765.
  rewrite ?node_31763.
  rewrite ?node_31764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31766 (s : N.State) (i : N.Inputs) :
  R.v31766 (state s) (inputs i) = Zmod.unsigned (N.v31766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31766 s i)) at 1.
  unfold R.v31766, N.v31766.
  unfold R.v16484, N.v16484.
  rewrite ?node_31765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31767 (s : N.State) (i : N.Inputs) :
  R.v31767 (state s) (inputs i) = Zmod.unsigned (N.v31767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31767 s i)) at 1.
  unfold R.v31767, N.v31767.
  rewrite ?node_31762.
  rewrite ?node_31766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31768 (s : N.State) (i : N.Inputs) :
  R.v31768 (state s) (inputs i) = Zmod.unsigned (N.v31768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31768 s i)) at 1.
  unfold R.v31768, N.v31768.
  unfold R.v6, N.v6.
  rewrite ?node_31767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31769 (s : N.State) (i : N.Inputs) :
  R.v31769 (state s) (inputs i) = Zmod.unsigned (N.v31769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31769 s i)) at 1.
  unfold R.v31769, N.v31769.
  rewrite ?node_12834.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31770 (s : N.State) (i : N.Inputs) :
  R.v31770 (state s) (inputs i) = Zmod.unsigned (N.v31770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31770 s i)) at 1.
  unfold R.v31770, N.v31770.
  unfold R.v6, N.v6.
  rewrite ?node_12965.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31771 (s : N.State) (i : N.Inputs) :
  R.v31771 (state s) (inputs i) = Zmod.unsigned (N.v31771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31771 s i)) at 1.
  unfold R.v31771, N.v31771.
  rewrite ?node_31769.
  rewrite ?node_31770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31772 (s : N.State) (i : N.Inputs) :
  R.v31772 (state s) (inputs i) = Zmod.unsigned (N.v31772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31772 s i)) at 1.
  unfold R.v31772, N.v31772.
  rewrite ?node_31768.
  rewrite ?node_31771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31773 (s : N.State) (i : N.Inputs) :
  R.v31773 (state s) (inputs i) = Zmod.unsigned (N.v31773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31773 s i)) at 1.
  unfold R.v31773, N.v31773.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31774 (s : N.State) (i : N.Inputs) :
  R.v31774 (state s) (inputs i) = Zmod.unsigned (N.v31774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31774 s i)) at 1.
  unfold R.v31774, N.v31774.
  rewrite ?node_12838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31775 (s : N.State) (i : N.Inputs) :
  R.v31775 (state s) (inputs i) = Zmod.unsigned (N.v31775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31775 s i)) at 1.
  unfold R.v31775, N.v31775.
  unfold R.v6, N.v6.
  rewrite !state_r1647_nr_5F1654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1647_nr_5F1654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31776 (s : N.State) (i : N.Inputs) :
  R.v31776 (state s) (inputs i) = Zmod.unsigned (N.v31776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31776 s i)) at 1.
  unfold R.v31776, N.v31776.
  unfold R.v6, N.v6.
  rewrite ?node_12834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31777 (s : N.State) (i : N.Inputs) :
  R.v31777 (state s) (inputs i) = Zmod.unsigned (N.v31777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31777 s i)) at 1.
  unfold R.v31777, N.v31777.
  rewrite ?node_31775.
  rewrite ?node_31776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31778 (s : N.State) (i : N.Inputs) :
  R.v31778 (state s) (inputs i) = Zmod.unsigned (N.v31778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31778 s i)) at 1.
  unfold R.v31778, N.v31778.
  unfold R.v16484, N.v16484.
  rewrite ?node_31777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31779 (s : N.State) (i : N.Inputs) :
  R.v31779 (state s) (inputs i) = Zmod.unsigned (N.v31779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31779 s i)) at 1.
  unfold R.v31779, N.v31779.
  rewrite ?node_31774.
  rewrite ?node_31778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31780 (s : N.State) (i : N.Inputs) :
  R.v31780 (state s) (inputs i) = Zmod.unsigned (N.v31780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31780 s i)) at 1.
  unfold R.v31780, N.v31780.
  unfold R.v6, N.v6.
  rewrite ?node_31779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31781 (s : N.State) (i : N.Inputs) :
  R.v31781 (state s) (inputs i) = Zmod.unsigned (N.v31781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31781 s i)) at 1.
  unfold R.v31781, N.v31781.
  rewrite ?node_12839.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31782 (s : N.State) (i : N.Inputs) :
  R.v31782 (state s) (inputs i) = Zmod.unsigned (N.v31782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31782 s i)) at 1.
  unfold R.v31782, N.v31782.
  unfold R.v6, N.v6.
  rewrite ?node_12998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31783 (s : N.State) (i : N.Inputs) :
  R.v31783 (state s) (inputs i) = Zmod.unsigned (N.v31783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31783 s i)) at 1.
  unfold R.v31783, N.v31783.
  rewrite ?node_31781.
  rewrite ?node_31782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31784 (s : N.State) (i : N.Inputs) :
  R.v31784 (state s) (inputs i) = Zmod.unsigned (N.v31784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31784 s i)) at 1.
  unfold R.v31784, N.v31784.
  rewrite ?node_31780.
  rewrite ?node_31783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31785 (s : N.State) (i : N.Inputs) :
  R.v31785 (state s) (inputs i) = Zmod.unsigned (N.v31785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31785 s i)) at 1.
  unfold R.v31785, N.v31785.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31786 (s : N.State) (i : N.Inputs) :
  R.v31786 (state s) (inputs i) = Zmod.unsigned (N.v31786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31786 s i)) at 1.
  unfold R.v31786, N.v31786.
  rewrite ?node_12845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31787 (s : N.State) (i : N.Inputs) :
  R.v31787 (state s) (inputs i) = Zmod.unsigned (N.v31787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31787 s i)) at 1.
  unfold R.v31787, N.v31787.
  unfold R.v16463, N.v16463.
  rewrite !state_r1651_nr_5F1658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1651_nr_5F1658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31788 (s : N.State) (i : N.Inputs) :
  R.v31788 (state s) (inputs i) = Zmod.unsigned (N.v31788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31788 s i)) at 1.
  unfold R.v31788, N.v31788.
  unfold R.v16463, N.v16463.
  rewrite !state_r1650_nr_5F1657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1650_nr_5F1657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31789 (s : N.State) (i : N.Inputs) :
  R.v31789 (state s) (inputs i) = Zmod.unsigned (N.v31789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31789 s i)) at 1.
  unfold R.v31789, N.v31789.
  unfold R.v6, N.v6.
  rewrite !state_r1649_nr_5F1656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1649_nr_5F1656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31790 (s : N.State) (i : N.Inputs) :
  R.v31790 (state s) (inputs i) = Zmod.unsigned (N.v31790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31790 s i)) at 1.
  unfold R.v31790, N.v31790.
  unfold R.v6, N.v6.
  rewrite !state_r1648_nr_5F1655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1648_nr_5F1655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31791 (s : N.State) (i : N.Inputs) :
  R.v31791 (state s) (inputs i) = Zmod.unsigned (N.v31791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31791 s i)) at 1.
  unfold R.v31791, N.v31791.
  rewrite ?node_31789.
  rewrite ?node_31790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31792 (s : N.State) (i : N.Inputs) :
  R.v31792 (state s) (inputs i) = Zmod.unsigned (N.v31792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31792 s i)) at 1.
  unfold R.v31792, N.v31792.
  unfold R.v16484, N.v16484.
  rewrite ?node_31791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31793 (s : N.State) (i : N.Inputs) :
  R.v31793 (state s) (inputs i) = Zmod.unsigned (N.v31793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31793 s i)) at 1.
  unfold R.v31793, N.v31793.
  rewrite ?node_31786.
  rewrite ?node_31787.
  rewrite ?node_31788.
  rewrite ?node_31792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31794 (s : N.State) (i : N.Inputs) :
  R.v31794 (state s) (inputs i) = Zmod.unsigned (N.v31794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31794 s i)) at 1.
  unfold R.v31794, N.v31794.
  unfold R.v6, N.v6.
  rewrite ?node_31793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31795 (s : N.State) (i : N.Inputs) :
  R.v31795 (state s) (inputs i) = Zmod.unsigned (N.v31795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31795 s i)) at 1.
  unfold R.v31795, N.v31795.
  rewrite ?node_12846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31796 (s : N.State) (i : N.Inputs) :
  R.v31796 (state s) (inputs i) = Zmod.unsigned (N.v31796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31796 s i)) at 1.
  unfold R.v31796, N.v31796.
  unfold R.v6, N.v6.
  rewrite ?node_12972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31797 (s : N.State) (i : N.Inputs) :
  R.v31797 (state s) (inputs i) = Zmod.unsigned (N.v31797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31797 s i)) at 1.
  unfold R.v31797, N.v31797.
  unfold R.v6, N.v6.
  rewrite ?node_13007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31798 (s : N.State) (i : N.Inputs) :
  R.v31798 (state s) (inputs i) = Zmod.unsigned (N.v31798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31798 s i)) at 1.
  unfold R.v31798, N.v31798.
  rewrite ?node_31795.
  rewrite ?node_31796.
  rewrite ?node_31797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31799 (s : N.State) (i : N.Inputs) :
  R.v31799 (state s) (inputs i) = Zmod.unsigned (N.v31799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31799 s i)) at 1.
  unfold R.v31799, N.v31799.
  rewrite ?node_31794.
  rewrite ?node_31798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31800 (s : N.State) (i : N.Inputs) :
  R.v31800 (state s) (inputs i) = Zmod.unsigned (N.v31800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31800 s i)) at 1.
  unfold R.v31800, N.v31800.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31801 (s : N.State) (i : N.Inputs) :
  R.v31801 (state s) (inputs i) = Zmod.unsigned (N.v31801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31801 s i)) at 1.
  unfold R.v31801, N.v31801.
  unfold R.v16463, N.v16463.
  rewrite !state_r1650_nr_5F1657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1650_nr_5F1657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31802 (s : N.State) (i : N.Inputs) :
  R.v31802 (state s) (inputs i) = Zmod.unsigned (N.v31802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31802 s i)) at 1.
  unfold R.v31802, N.v31802.
  unfold R.v6, N.v6.
  rewrite !state_r1649_nr_5F1656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1649_nr_5F1656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31803 (s : N.State) (i : N.Inputs) :
  R.v31803 (state s) (inputs i) = Zmod.unsigned (N.v31803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31803 s i)) at 1.
  unfold R.v31803, N.v31803.
  unfold R.v6, N.v6.
  rewrite !state_r1648_nr_5F1655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1648_nr_5F1655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31804 (s : N.State) (i : N.Inputs) :
  R.v31804 (state s) (inputs i) = Zmod.unsigned (N.v31804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31804 s i)) at 1.
  unfold R.v31804, N.v31804.
  rewrite ?node_31802.
  rewrite ?node_31803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31805 (s : N.State) (i : N.Inputs) :
  R.v31805 (state s) (inputs i) = Zmod.unsigned (N.v31805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31805 s i)) at 1.
  unfold R.v31805, N.v31805.
  unfold R.v16484, N.v16484.
  rewrite ?node_31804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31806 (s : N.State) (i : N.Inputs) :
  R.v31806 (state s) (inputs i) = Zmod.unsigned (N.v31806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31806 s i)) at 1.
  unfold R.v31806, N.v31806.
  rewrite ?node_31801.
  rewrite ?node_31805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31807 (s : N.State) (i : N.Inputs) :
  R.v31807 (state s) (inputs i) = Zmod.unsigned (N.v31807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31807 s i)) at 1.
  unfold R.v31807, N.v31807.
  unfold R.v6, N.v6.
  rewrite ?node_31806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31808 (s : N.State) (i : N.Inputs) :
  R.v31808 (state s) (inputs i) = Zmod.unsigned (N.v31808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31808 s i)) at 1.
  unfold R.v31808, N.v31808.
  rewrite ?node_12841.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31809 (s : N.State) (i : N.Inputs) :
  R.v31809 (state s) (inputs i) = Zmod.unsigned (N.v31809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31809 s i)) at 1.
  unfold R.v31809, N.v31809.
  unfold R.v6, N.v6.
  rewrite ?node_12972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31810 (s : N.State) (i : N.Inputs) :
  R.v31810 (state s) (inputs i) = Zmod.unsigned (N.v31810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31810 s i)) at 1.
  unfold R.v31810, N.v31810.
  rewrite ?node_31808.
  rewrite ?node_31809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31811 (s : N.State) (i : N.Inputs) :
  R.v31811 (state s) (inputs i) = Zmod.unsigned (N.v31811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31811 s i)) at 1.
  unfold R.v31811, N.v31811.
  rewrite ?node_31807.
  rewrite ?node_31810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31812 (s : N.State) (i : N.Inputs) :
  R.v31812 (state s) (inputs i) = Zmod.unsigned (N.v31812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31812 s i)) at 1.
  unfold R.v31812, N.v31812.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31813 (s : N.State) (i : N.Inputs) :
  R.v31813 (state s) (inputs i) = Zmod.unsigned (N.v31813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31813 s i)) at 1.
  unfold R.v31813, N.v31813.
  rewrite ?node_12845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31814 (s : N.State) (i : N.Inputs) :
  R.v31814 (state s) (inputs i) = Zmod.unsigned (N.v31814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31814 s i)) at 1.
  unfold R.v31814, N.v31814.
  unfold R.v6, N.v6.
  rewrite !state_r1651_nr_5F1658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1651_nr_5F1658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31815 (s : N.State) (i : N.Inputs) :
  R.v31815 (state s) (inputs i) = Zmod.unsigned (N.v31815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31815 s i)) at 1.
  unfold R.v31815, N.v31815.
  unfold R.v6, N.v6.
  rewrite ?node_12841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31816 (s : N.State) (i : N.Inputs) :
  R.v31816 (state s) (inputs i) = Zmod.unsigned (N.v31816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31816 s i)) at 1.
  unfold R.v31816, N.v31816.
  rewrite ?node_31814.
  rewrite ?node_31815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31817 (s : N.State) (i : N.Inputs) :
  R.v31817 (state s) (inputs i) = Zmod.unsigned (N.v31817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31817 s i)) at 1.
  unfold R.v31817, N.v31817.
  unfold R.v16484, N.v16484.
  rewrite ?node_31816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31818 (s : N.State) (i : N.Inputs) :
  R.v31818 (state s) (inputs i) = Zmod.unsigned (N.v31818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31818 s i)) at 1.
  unfold R.v31818, N.v31818.
  rewrite ?node_31813.
  rewrite ?node_31817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31819 (s : N.State) (i : N.Inputs) :
  R.v31819 (state s) (inputs i) = Zmod.unsigned (N.v31819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31819 s i)) at 1.
  unfold R.v31819, N.v31819.
  unfold R.v6, N.v6.
  rewrite ?node_31818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31820 (s : N.State) (i : N.Inputs) :
  R.v31820 (state s) (inputs i) = Zmod.unsigned (N.v31820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31820 s i)) at 1.
  unfold R.v31820, N.v31820.
  rewrite ?node_12846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31821 (s : N.State) (i : N.Inputs) :
  R.v31821 (state s) (inputs i) = Zmod.unsigned (N.v31821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31821 s i)) at 1.
  unfold R.v31821, N.v31821.
  unfold R.v6, N.v6.
  rewrite ?node_13007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31822 (s : N.State) (i : N.Inputs) :
  R.v31822 (state s) (inputs i) = Zmod.unsigned (N.v31822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31822 s i)) at 1.
  unfold R.v31822, N.v31822.
  rewrite ?node_31820.
  rewrite ?node_31821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31823 (s : N.State) (i : N.Inputs) :
  R.v31823 (state s) (inputs i) = Zmod.unsigned (N.v31823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31823 s i)) at 1.
  unfold R.v31823, N.v31823.
  rewrite ?node_31819.
  rewrite ?node_31822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31824 (s : N.State) (i : N.Inputs) :
  R.v31824 (state s) (inputs i) = Zmod.unsigned (N.v31824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31824 s i)) at 1.
  unfold R.v31824, N.v31824.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31825 (s : N.State) (i : N.Inputs) :
  R.v31825 (state s) (inputs i) = Zmod.unsigned (N.v31825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31825 s i)) at 1.
  unfold R.v31825, N.v31825.
  unfold R.v6, N.v6.
  rewrite !state_r1653_nr_5F1660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1653_nr_5F1660 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31826 (s : N.State) (i : N.Inputs) :
  R.v31826 (state s) (inputs i) = Zmod.unsigned (N.v31826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31826 s i)) at 1.
  unfold R.v31826, N.v31826.
  unfold R.v6, N.v6.
  rewrite !state_r1652_nr_5F1659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1652_nr_5F1659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31827 (s : N.State) (i : N.Inputs) :
  R.v31827 (state s) (inputs i) = Zmod.unsigned (N.v31827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31827 s i)) at 1.
  unfold R.v31827, N.v31827.
  rewrite ?node_31825.
  rewrite ?node_31826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31828 (s : N.State) (i : N.Inputs) :
  R.v31828 (state s) (inputs i) = Zmod.unsigned (N.v31828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31828 s i)) at 1.
  unfold R.v31828, N.v31828.
  unfold R.v16463, N.v16463.
  rewrite ?node_31827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31829 (s : N.State) (i : N.Inputs) :
  R.v31829 (state s) (inputs i) = Zmod.unsigned (N.v31829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31829 s i)) at 1.
  unfold R.v31829, N.v31829.
  rewrite ?node_12848.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31830 (s : N.State) (i : N.Inputs) :
  R.v31830 (state s) (inputs i) = Zmod.unsigned (N.v31830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31830 s i)) at 1.
  unfold R.v31830, N.v31830.
  unfold R.v6, N.v6.
  rewrite ?node_13008.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31831 (s : N.State) (i : N.Inputs) :
  R.v31831 (state s) (inputs i) = Zmod.unsigned (N.v31831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31831 s i)) at 1.
  unfold R.v31831, N.v31831.
  rewrite ?node_31829.
  rewrite ?node_31830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31832 (s : N.State) (i : N.Inputs) :
  R.v31832 (state s) (inputs i) = Zmod.unsigned (N.v31832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31832 s i)) at 1.
  unfold R.v31832, N.v31832.
  rewrite ?node_31828.
  rewrite ?node_31831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31833 (s : N.State) (i : N.Inputs) :
  R.v31833 (state s) (inputs i) = Zmod.unsigned (N.v31833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31833 s i)) at 1.
  unfold R.v31833, N.v31833.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31834 (s : N.State) (i : N.Inputs) :
  R.v31834 (state s) (inputs i) = Zmod.unsigned (N.v31834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31834 s i)) at 1.
  unfold R.v31834, N.v31834.
  rewrite ?node_12930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31835 (s : N.State) (i : N.Inputs) :
  R.v31835 (state s) (inputs i) = Zmod.unsigned (N.v31835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31835 s i)) at 1.
  unfold R.v31835, N.v31835.
  unfold R.v16463, N.v16463.
  rewrite !state_r1657_nr_5F1664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1657_nr_5F1664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31836 (s : N.State) (i : N.Inputs) :
  R.v31836 (state s) (inputs i) = Zmod.unsigned (N.v31836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31836 s i)) at 1.
  unfold R.v31836, N.v31836.
  unfold R.v16463, N.v16463.
  rewrite !state_r1656_nr_5F1663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1656_nr_5F1663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31837 (s : N.State) (i : N.Inputs) :
  R.v31837 (state s) (inputs i) = Zmod.unsigned (N.v31837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31837 s i)) at 1.
  unfold R.v31837, N.v31837.
  unfold R.v6, N.v6.
  rewrite !state_r1655_nr_5F1662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1655_nr_5F1662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31838 (s : N.State) (i : N.Inputs) :
  R.v31838 (state s) (inputs i) = Zmod.unsigned (N.v31838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31838 s i)) at 1.
  unfold R.v31838, N.v31838.
  unfold R.v6, N.v6.
  rewrite !state_r1654_nr_5F1661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1654_nr_5F1661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31839 (s : N.State) (i : N.Inputs) :
  R.v31839 (state s) (inputs i) = Zmod.unsigned (N.v31839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31839 s i)) at 1.
  unfold R.v31839, N.v31839.
  rewrite ?node_31837.
  rewrite ?node_31838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31840 (s : N.State) (i : N.Inputs) :
  R.v31840 (state s) (inputs i) = Zmod.unsigned (N.v31840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31840 s i)) at 1.
  unfold R.v31840, N.v31840.
  unfold R.v16484, N.v16484.
  rewrite ?node_31839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31841 (s : N.State) (i : N.Inputs) :
  R.v31841 (state s) (inputs i) = Zmod.unsigned (N.v31841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31841 s i)) at 1.
  unfold R.v31841, N.v31841.
  rewrite ?node_31834.
  rewrite ?node_31835.
  rewrite ?node_31836.
  rewrite ?node_31840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31842 (s : N.State) (i : N.Inputs) :
  R.v31842 (state s) (inputs i) = Zmod.unsigned (N.v31842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31842 s i)) at 1.
  unfold R.v31842, N.v31842.
  unfold R.v6, N.v6.
  rewrite ?node_31841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31843 (s : N.State) (i : N.Inputs) :
  R.v31843 (state s) (inputs i) = Zmod.unsigned (N.v31843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31843 s i)) at 1.
  unfold R.v31843, N.v31843.
  rewrite ?node_12931.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31844 (s : N.State) (i : N.Inputs) :
  R.v31844 (state s) (inputs i) = Zmod.unsigned (N.v31844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31844 s i)) at 1.
  unfold R.v31844, N.v31844.
  unfold R.v6, N.v6.
  rewrite ?node_13057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31845 (s : N.State) (i : N.Inputs) :
  R.v31845 (state s) (inputs i) = Zmod.unsigned (N.v31845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31845 s i)) at 1.
  unfold R.v31845, N.v31845.
  unfold R.v6, N.v6.
  rewrite ?node_13105.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31846 (s : N.State) (i : N.Inputs) :
  R.v31846 (state s) (inputs i) = Zmod.unsigned (N.v31846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31846 s i)) at 1.
  unfold R.v31846, N.v31846.
  rewrite ?node_31843.
  rewrite ?node_31844.
  rewrite ?node_31845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31847 (s : N.State) (i : N.Inputs) :
  R.v31847 (state s) (inputs i) = Zmod.unsigned (N.v31847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31847 s i)) at 1.
  unfold R.v31847, N.v31847.
  rewrite ?node_31842.
  rewrite ?node_31846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31848 (s : N.State) (i : N.Inputs) :
  R.v31848 (state s) (inputs i) = Zmod.unsigned (N.v31848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31848 s i)) at 1.
  unfold R.v31848, N.v31848.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31849 (s : N.State) (i : N.Inputs) :
  R.v31849 (state s) (inputs i) = Zmod.unsigned (N.v31849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31849 s i)) at 1.
  unfold R.v31849, N.v31849.
  unfold R.v16463, N.v16463.
  rewrite !state_r1656_nr_5F1663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1656_nr_5F1663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31850 (s : N.State) (i : N.Inputs) :
  R.v31850 (state s) (inputs i) = Zmod.unsigned (N.v31850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31850 s i)) at 1.
  unfold R.v31850, N.v31850.
  unfold R.v6, N.v6.
  rewrite !state_r1655_nr_5F1662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1655_nr_5F1662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31851 (s : N.State) (i : N.Inputs) :
  R.v31851 (state s) (inputs i) = Zmod.unsigned (N.v31851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31851 s i)) at 1.
  unfold R.v31851, N.v31851.
  unfold R.v6, N.v6.
  rewrite !state_r1654_nr_5F1661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1654_nr_5F1661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31852 (s : N.State) (i : N.Inputs) :
  R.v31852 (state s) (inputs i) = Zmod.unsigned (N.v31852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31852 s i)) at 1.
  unfold R.v31852, N.v31852.
  rewrite ?node_31850.
  rewrite ?node_31851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31853 (s : N.State) (i : N.Inputs) :
  R.v31853 (state s) (inputs i) = Zmod.unsigned (N.v31853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31853 s i)) at 1.
  unfold R.v31853, N.v31853.
  unfold R.v16484, N.v16484.
  rewrite ?node_31852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31854 (s : N.State) (i : N.Inputs) :
  R.v31854 (state s) (inputs i) = Zmod.unsigned (N.v31854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31854 s i)) at 1.
  unfold R.v31854, N.v31854.
  rewrite ?node_31849.
  rewrite ?node_31853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31855 (s : N.State) (i : N.Inputs) :
  R.v31855 (state s) (inputs i) = Zmod.unsigned (N.v31855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31855 s i)) at 1.
  unfold R.v31855, N.v31855.
  unfold R.v6, N.v6.
  rewrite ?node_31854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31856 (s : N.State) (i : N.Inputs) :
  R.v31856 (state s) (inputs i) = Zmod.unsigned (N.v31856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31856 s i)) at 1.
  unfold R.v31856, N.v31856.
  rewrite ?node_12927.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31857 (s : N.State) (i : N.Inputs) :
  R.v31857 (state s) (inputs i) = Zmod.unsigned (N.v31857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31857 s i)) at 1.
  unfold R.v31857, N.v31857.
  unfold R.v6, N.v6.
  rewrite ?node_13057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31858 (s : N.State) (i : N.Inputs) :
  R.v31858 (state s) (inputs i) = Zmod.unsigned (N.v31858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31858 s i)) at 1.
  unfold R.v31858, N.v31858.
  rewrite ?node_31856.
  rewrite ?node_31857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31859 (s : N.State) (i : N.Inputs) :
  R.v31859 (state s) (inputs i) = Zmod.unsigned (N.v31859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31859 s i)) at 1.
  unfold R.v31859, N.v31859.
  rewrite ?node_31855.
  rewrite ?node_31858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31860 (s : N.State) (i : N.Inputs) :
  R.v31860 (state s) (inputs i) = Zmod.unsigned (N.v31860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31860 s i)) at 1.
  unfold R.v31860, N.v31860.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31861 (s : N.State) (i : N.Inputs) :
  R.v31861 (state s) (inputs i) = Zmod.unsigned (N.v31861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31861 s i)) at 1.
  unfold R.v31861, N.v31861.
  rewrite ?node_12930.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31862 (s : N.State) (i : N.Inputs) :
  R.v31862 (state s) (inputs i) = Zmod.unsigned (N.v31862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31862 s i)) at 1.
  unfold R.v31862, N.v31862.
  unfold R.v6, N.v6.
  rewrite !state_r1657_nr_5F1664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1657_nr_5F1664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31863 (s : N.State) (i : N.Inputs) :
  R.v31863 (state s) (inputs i) = Zmod.unsigned (N.v31863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31863 s i)) at 1.
  unfold R.v31863, N.v31863.
  unfold R.v6, N.v6.
  rewrite ?node_12927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31864 (s : N.State) (i : N.Inputs) :
  R.v31864 (state s) (inputs i) = Zmod.unsigned (N.v31864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31864 s i)) at 1.
  unfold R.v31864, N.v31864.
  rewrite ?node_31862.
  rewrite ?node_31863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31865 (s : N.State) (i : N.Inputs) :
  R.v31865 (state s) (inputs i) = Zmod.unsigned (N.v31865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31865 s i)) at 1.
  unfold R.v31865, N.v31865.
  unfold R.v16484, N.v16484.
  rewrite ?node_31864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31866 (s : N.State) (i : N.Inputs) :
  R.v31866 (state s) (inputs i) = Zmod.unsigned (N.v31866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31866 s i)) at 1.
  unfold R.v31866, N.v31866.
  rewrite ?node_31861.
  rewrite ?node_31865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31867 (s : N.State) (i : N.Inputs) :
  R.v31867 (state s) (inputs i) = Zmod.unsigned (N.v31867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31867 s i)) at 1.
  unfold R.v31867, N.v31867.
  unfold R.v6, N.v6.
  rewrite ?node_31866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31868 (s : N.State) (i : N.Inputs) :
  R.v31868 (state s) (inputs i) = Zmod.unsigned (N.v31868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31868 s i)) at 1.
  unfold R.v31868, N.v31868.
  rewrite ?node_12931.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31869 (s : N.State) (i : N.Inputs) :
  R.v31869 (state s) (inputs i) = Zmod.unsigned (N.v31869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31869 s i)) at 1.
  unfold R.v31869, N.v31869.
  unfold R.v6, N.v6.
  rewrite ?node_13105.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31870 (s : N.State) (i : N.Inputs) :
  R.v31870 (state s) (inputs i) = Zmod.unsigned (N.v31870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31870 s i)) at 1.
  unfold R.v31870, N.v31870.
  rewrite ?node_31868.
  rewrite ?node_31869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31871 (s : N.State) (i : N.Inputs) :
  R.v31871 (state s) (inputs i) = Zmod.unsigned (N.v31871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31871 s i)) at 1.
  unfold R.v31871, N.v31871.
  rewrite ?node_31867.
  rewrite ?node_31870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31872 (s : N.State) (i : N.Inputs) :
  R.v31872 (state s) (inputs i) = Zmod.unsigned (N.v31872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31872 s i)) at 1.
  unfold R.v31872, N.v31872.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31873 (s : N.State) (i : N.Inputs) :
  R.v31873 (state s) (inputs i) = Zmod.unsigned (N.v31873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31873 s i)) at 1.
  unfold R.v31873, N.v31873.
  rewrite ?node_12937.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31874 (s : N.State) (i : N.Inputs) :
  R.v31874 (state s) (inputs i) = Zmod.unsigned (N.v31874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31874 s i)) at 1.
  unfold R.v31874, N.v31874.
  unfold R.v16463, N.v16463.
  rewrite !state_r1661_nr_5F1668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1661_nr_5F1668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31875 (s : N.State) (i : N.Inputs) :
  R.v31875 (state s) (inputs i) = Zmod.unsigned (N.v31875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31875 s i)) at 1.
  unfold R.v31875, N.v31875.
  unfold R.v16463, N.v16463.
  rewrite !state_r1660_nr_5F1667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1660_nr_5F1667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31876 (s : N.State) (i : N.Inputs) :
  R.v31876 (state s) (inputs i) = Zmod.unsigned (N.v31876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31876 s i)) at 1.
  unfold R.v31876, N.v31876.
  unfold R.v6, N.v6.
  rewrite !state_r1659_nr_5F1666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1659_nr_5F1666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31877 (s : N.State) (i : N.Inputs) :
  R.v31877 (state s) (inputs i) = Zmod.unsigned (N.v31877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31877 s i)) at 1.
  unfold R.v31877, N.v31877.
  unfold R.v6, N.v6.
  rewrite !state_r1658_nr_5F1665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1658_nr_5F1665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31878 (s : N.State) (i : N.Inputs) :
  R.v31878 (state s) (inputs i) = Zmod.unsigned (N.v31878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31878 s i)) at 1.
  unfold R.v31878, N.v31878.
  rewrite ?node_31876.
  rewrite ?node_31877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31879 (s : N.State) (i : N.Inputs) :
  R.v31879 (state s) (inputs i) = Zmod.unsigned (N.v31879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31879 s i)) at 1.
  unfold R.v31879, N.v31879.
  unfold R.v16484, N.v16484.
  rewrite ?node_31878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31880 (s : N.State) (i : N.Inputs) :
  R.v31880 (state s) (inputs i) = Zmod.unsigned (N.v31880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31880 s i)) at 1.
  unfold R.v31880, N.v31880.
  rewrite ?node_31873.
  rewrite ?node_31874.
  rewrite ?node_31875.
  rewrite ?node_31879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31881 (s : N.State) (i : N.Inputs) :
  R.v31881 (state s) (inputs i) = Zmod.unsigned (N.v31881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31881 s i)) at 1.
  unfold R.v31881, N.v31881.
  unfold R.v6, N.v6.
  rewrite ?node_31880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31882 (s : N.State) (i : N.Inputs) :
  R.v31882 (state s) (inputs i) = Zmod.unsigned (N.v31882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31882 s i)) at 1.
  unfold R.v31882, N.v31882.
  rewrite ?node_12938.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31883 (s : N.State) (i : N.Inputs) :
  R.v31883 (state s) (inputs i) = Zmod.unsigned (N.v31883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31883 s i)) at 1.
  unfold R.v31883, N.v31883.
  unfold R.v6, N.v6.
  rewrite ?node_13064.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31884 (s : N.State) (i : N.Inputs) :
  R.v31884 (state s) (inputs i) = Zmod.unsigned (N.v31884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31884 s i)) at 1.
  unfold R.v31884, N.v31884.
  unfold R.v6, N.v6.
  rewrite ?node_13114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31885 (s : N.State) (i : N.Inputs) :
  R.v31885 (state s) (inputs i) = Zmod.unsigned (N.v31885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31885 s i)) at 1.
  unfold R.v31885, N.v31885.
  rewrite ?node_31882.
  rewrite ?node_31883.
  rewrite ?node_31884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31886 (s : N.State) (i : N.Inputs) :
  R.v31886 (state s) (inputs i) = Zmod.unsigned (N.v31886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31886 s i)) at 1.
  unfold R.v31886, N.v31886.
  rewrite ?node_31881.
  rewrite ?node_31885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31887 (s : N.State) (i : N.Inputs) :
  R.v31887 (state s) (inputs i) = Zmod.unsigned (N.v31887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31887 s i)) at 1.
  unfold R.v31887, N.v31887.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31888 (s : N.State) (i : N.Inputs) :
  R.v31888 (state s) (inputs i) = Zmod.unsigned (N.v31888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31888 s i)) at 1.
  unfold R.v31888, N.v31888.
  unfold R.v16463, N.v16463.
  rewrite !state_r1660_nr_5F1667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1660_nr_5F1667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31889 (s : N.State) (i : N.Inputs) :
  R.v31889 (state s) (inputs i) = Zmod.unsigned (N.v31889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31889 s i)) at 1.
  unfold R.v31889, N.v31889.
  unfold R.v6, N.v6.
  rewrite !state_r1659_nr_5F1666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1659_nr_5F1666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31890 (s : N.State) (i : N.Inputs) :
  R.v31890 (state s) (inputs i) = Zmod.unsigned (N.v31890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31890 s i)) at 1.
  unfold R.v31890, N.v31890.
  unfold R.v6, N.v6.
  rewrite !state_r1658_nr_5F1665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1658_nr_5F1665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31891 (s : N.State) (i : N.Inputs) :
  R.v31891 (state s) (inputs i) = Zmod.unsigned (N.v31891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31891 s i)) at 1.
  unfold R.v31891, N.v31891.
  rewrite ?node_31889.
  rewrite ?node_31890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31892 (s : N.State) (i : N.Inputs) :
  R.v31892 (state s) (inputs i) = Zmod.unsigned (N.v31892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31892 s i)) at 1.
  unfold R.v31892, N.v31892.
  unfold R.v16484, N.v16484.
  rewrite ?node_31891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31893 (s : N.State) (i : N.Inputs) :
  R.v31893 (state s) (inputs i) = Zmod.unsigned (N.v31893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31893 s i)) at 1.
  unfold R.v31893, N.v31893.
  rewrite ?node_31888.
  rewrite ?node_31892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31894 (s : N.State) (i : N.Inputs) :
  R.v31894 (state s) (inputs i) = Zmod.unsigned (N.v31894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31894 s i)) at 1.
  unfold R.v31894, N.v31894.
  unfold R.v6, N.v6.
  rewrite ?node_31893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31895 (s : N.State) (i : N.Inputs) :
  R.v31895 (state s) (inputs i) = Zmod.unsigned (N.v31895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31895 s i)) at 1.
  unfold R.v31895, N.v31895.
  rewrite ?node_12933.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31896 (s : N.State) (i : N.Inputs) :
  R.v31896 (state s) (inputs i) = Zmod.unsigned (N.v31896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31896 s i)) at 1.
  unfold R.v31896, N.v31896.
  unfold R.v6, N.v6.
  rewrite ?node_13064.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31897 (s : N.State) (i : N.Inputs) :
  R.v31897 (state s) (inputs i) = Zmod.unsigned (N.v31897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31897 s i)) at 1.
  unfold R.v31897, N.v31897.
  rewrite ?node_31895.
  rewrite ?node_31896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31898 (s : N.State) (i : N.Inputs) :
  R.v31898 (state s) (inputs i) = Zmod.unsigned (N.v31898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31898 s i)) at 1.
  unfold R.v31898, N.v31898.
  rewrite ?node_31894.
  rewrite ?node_31897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31899 (s : N.State) (i : N.Inputs) :
  R.v31899 (state s) (inputs i) = Zmod.unsigned (N.v31899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31899 s i)) at 1.
  unfold R.v31899, N.v31899.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31900 (s : N.State) (i : N.Inputs) :
  R.v31900 (state s) (inputs i) = Zmod.unsigned (N.v31900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31900 s i)) at 1.
  unfold R.v31900, N.v31900.
  rewrite ?node_12937.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31901 (s : N.State) (i : N.Inputs) :
  R.v31901 (state s) (inputs i) = Zmod.unsigned (N.v31901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31901 s i)) at 1.
  unfold R.v31901, N.v31901.
  unfold R.v6, N.v6.
  rewrite !state_r1661_nr_5F1668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1661_nr_5F1668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31902 (s : N.State) (i : N.Inputs) :
  R.v31902 (state s) (inputs i) = Zmod.unsigned (N.v31902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31902 s i)) at 1.
  unfold R.v31902, N.v31902.
  unfold R.v6, N.v6.
  rewrite ?node_12933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31903 (s : N.State) (i : N.Inputs) :
  R.v31903 (state s) (inputs i) = Zmod.unsigned (N.v31903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31903 s i)) at 1.
  unfold R.v31903, N.v31903.
  rewrite ?node_31901.
  rewrite ?node_31902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31904 (s : N.State) (i : N.Inputs) :
  R.v31904 (state s) (inputs i) = Zmod.unsigned (N.v31904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31904 s i)) at 1.
  unfold R.v31904, N.v31904.
  unfold R.v16484, N.v16484.
  rewrite ?node_31903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31905 (s : N.State) (i : N.Inputs) :
  R.v31905 (state s) (inputs i) = Zmod.unsigned (N.v31905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31905 s i)) at 1.
  unfold R.v31905, N.v31905.
  rewrite ?node_31900.
  rewrite ?node_31904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31906 (s : N.State) (i : N.Inputs) :
  R.v31906 (state s) (inputs i) = Zmod.unsigned (N.v31906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31906 s i)) at 1.
  unfold R.v31906, N.v31906.
  unfold R.v6, N.v6.
  rewrite ?node_31905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31907 (s : N.State) (i : N.Inputs) :
  R.v31907 (state s) (inputs i) = Zmod.unsigned (N.v31907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31907 s i)) at 1.
  unfold R.v31907, N.v31907.
  rewrite ?node_12938.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31908 (s : N.State) (i : N.Inputs) :
  R.v31908 (state s) (inputs i) = Zmod.unsigned (N.v31908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31908 s i)) at 1.
  unfold R.v31908, N.v31908.
  unfold R.v6, N.v6.
  rewrite ?node_13114.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31909 (s : N.State) (i : N.Inputs) :
  R.v31909 (state s) (inputs i) = Zmod.unsigned (N.v31909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31909 s i)) at 1.
  unfold R.v31909, N.v31909.
  rewrite ?node_31907.
  rewrite ?node_31908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31910 (s : N.State) (i : N.Inputs) :
  R.v31910 (state s) (inputs i) = Zmod.unsigned (N.v31910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31910 s i)) at 1.
  unfold R.v31910, N.v31910.
  rewrite ?node_31906.
  rewrite ?node_31909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31911 (s : N.State) (i : N.Inputs) :
  R.v31911 (state s) (inputs i) = Zmod.unsigned (N.v31911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31911 s i)) at 1.
  unfold R.v31911, N.v31911.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31912 (s : N.State) (i : N.Inputs) :
  R.v31912 (state s) (inputs i) = Zmod.unsigned (N.v31912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31912 s i)) at 1.
  unfold R.v31912, N.v31912.
  rewrite ?node_12945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31913 (s : N.State) (i : N.Inputs) :
  R.v31913 (state s) (inputs i) = Zmod.unsigned (N.v31913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31913 s i)) at 1.
  unfold R.v31913, N.v31913.
  unfold R.v16463, N.v16463.
  rewrite !state_r1665_nr_5F1672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1665_nr_5F1672 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31914 (s : N.State) (i : N.Inputs) :
  R.v31914 (state s) (inputs i) = Zmod.unsigned (N.v31914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31914 s i)) at 1.
  unfold R.v31914, N.v31914.
  unfold R.v16463, N.v16463.
  rewrite !state_r1664_nr_5F1671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1664_nr_5F1671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31915 (s : N.State) (i : N.Inputs) :
  R.v31915 (state s) (inputs i) = Zmod.unsigned (N.v31915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31915 s i)) at 1.
  unfold R.v31915, N.v31915.
  unfold R.v6, N.v6.
  rewrite !state_r1663_nr_5F1670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1663_nr_5F1670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31916 (s : N.State) (i : N.Inputs) :
  R.v31916 (state s) (inputs i) = Zmod.unsigned (N.v31916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31916 s i)) at 1.
  unfold R.v31916, N.v31916.
  unfold R.v6, N.v6.
  rewrite !state_r1662_nr_5F1669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1662_nr_5F1669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31917 (s : N.State) (i : N.Inputs) :
  R.v31917 (state s) (inputs i) = Zmod.unsigned (N.v31917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31917 s i)) at 1.
  unfold R.v31917, N.v31917.
  rewrite ?node_31915.
  rewrite ?node_31916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31918 (s : N.State) (i : N.Inputs) :
  R.v31918 (state s) (inputs i) = Zmod.unsigned (N.v31918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31918 s i)) at 1.
  unfold R.v31918, N.v31918.
  unfold R.v16484, N.v16484.
  rewrite ?node_31917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31919 (s : N.State) (i : N.Inputs) :
  R.v31919 (state s) (inputs i) = Zmod.unsigned (N.v31919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31919 s i)) at 1.
  unfold R.v31919, N.v31919.
  rewrite ?node_31912.
  rewrite ?node_31913.
  rewrite ?node_31914.
  rewrite ?node_31918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31920 (s : N.State) (i : N.Inputs) :
  R.v31920 (state s) (inputs i) = Zmod.unsigned (N.v31920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31920 s i)) at 1.
  unfold R.v31920, N.v31920.
  unfold R.v6, N.v6.
  rewrite ?node_31919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31921 (s : N.State) (i : N.Inputs) :
  R.v31921 (state s) (inputs i) = Zmod.unsigned (N.v31921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31921 s i)) at 1.
  unfold R.v31921, N.v31921.
  rewrite ?node_12946.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31922 (s : N.State) (i : N.Inputs) :
  R.v31922 (state s) (inputs i) = Zmod.unsigned (N.v31922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31922 s i)) at 1.
  unfold R.v31922, N.v31922.
  unfold R.v6, N.v6.
  rewrite ?node_13072.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31923 (s : N.State) (i : N.Inputs) :
  R.v31923 (state s) (inputs i) = Zmod.unsigned (N.v31923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31923 s i)) at 1.
  unfold R.v31923, N.v31923.
  unfold R.v6, N.v6.
  rewrite ?node_13117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31924 (s : N.State) (i : N.Inputs) :
  R.v31924 (state s) (inputs i) = Zmod.unsigned (N.v31924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31924 s i)) at 1.
  unfold R.v31924, N.v31924.
  rewrite ?node_31921.
  rewrite ?node_31922.
  rewrite ?node_31923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31925 (s : N.State) (i : N.Inputs) :
  R.v31925 (state s) (inputs i) = Zmod.unsigned (N.v31925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31925 s i)) at 1.
  unfold R.v31925, N.v31925.
  rewrite ?node_31920.
  rewrite ?node_31924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31926 (s : N.State) (i : N.Inputs) :
  R.v31926 (state s) (inputs i) = Zmod.unsigned (N.v31926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31926 s i)) at 1.
  unfold R.v31926, N.v31926.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31927 (s : N.State) (i : N.Inputs) :
  R.v31927 (state s) (inputs i) = Zmod.unsigned (N.v31927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31927 s i)) at 1.
  unfold R.v31927, N.v31927.
  unfold R.v16463, N.v16463.
  rewrite !state_r1664_nr_5F1671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1664_nr_5F1671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31928 (s : N.State) (i : N.Inputs) :
  R.v31928 (state s) (inputs i) = Zmod.unsigned (N.v31928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31928 s i)) at 1.
  unfold R.v31928, N.v31928.
  unfold R.v6, N.v6.
  rewrite !state_r1663_nr_5F1670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1663_nr_5F1670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31929 (s : N.State) (i : N.Inputs) :
  R.v31929 (state s) (inputs i) = Zmod.unsigned (N.v31929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31929 s i)) at 1.
  unfold R.v31929, N.v31929.
  unfold R.v6, N.v6.
  rewrite !state_r1662_nr_5F1669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1662_nr_5F1669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31930 (s : N.State) (i : N.Inputs) :
  R.v31930 (state s) (inputs i) = Zmod.unsigned (N.v31930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31930 s i)) at 1.
  unfold R.v31930, N.v31930.
  rewrite ?node_31928.
  rewrite ?node_31929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31931 (s : N.State) (i : N.Inputs) :
  R.v31931 (state s) (inputs i) = Zmod.unsigned (N.v31931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31931 s i)) at 1.
  unfold R.v31931, N.v31931.
  unfold R.v16484, N.v16484.
  rewrite ?node_31930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31932 (s : N.State) (i : N.Inputs) :
  R.v31932 (state s) (inputs i) = Zmod.unsigned (N.v31932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31932 s i)) at 1.
  unfold R.v31932, N.v31932.
  rewrite ?node_31927.
  rewrite ?node_31931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31933 (s : N.State) (i : N.Inputs) :
  R.v31933 (state s) (inputs i) = Zmod.unsigned (N.v31933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31933 s i)) at 1.
  unfold R.v31933, N.v31933.
  unfold R.v6, N.v6.
  rewrite ?node_31932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31934 (s : N.State) (i : N.Inputs) :
  R.v31934 (state s) (inputs i) = Zmod.unsigned (N.v31934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31934 s i)) at 1.
  unfold R.v31934, N.v31934.
  rewrite ?node_12941.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31935 (s : N.State) (i : N.Inputs) :
  R.v31935 (state s) (inputs i) = Zmod.unsigned (N.v31935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31935 s i)) at 1.
  unfold R.v31935, N.v31935.
  unfold R.v6, N.v6.
  rewrite ?node_13072.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31936 (s : N.State) (i : N.Inputs) :
  R.v31936 (state s) (inputs i) = Zmod.unsigned (N.v31936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31936 s i)) at 1.
  unfold R.v31936, N.v31936.
  rewrite ?node_31934.
  rewrite ?node_31935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31937 (s : N.State) (i : N.Inputs) :
  R.v31937 (state s) (inputs i) = Zmod.unsigned (N.v31937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31937 s i)) at 1.
  unfold R.v31937, N.v31937.
  rewrite ?node_31933.
  rewrite ?node_31936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31938 (s : N.State) (i : N.Inputs) :
  R.v31938 (state s) (inputs i) = Zmod.unsigned (N.v31938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31938 s i)) at 1.
  unfold R.v31938, N.v31938.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31939 (s : N.State) (i : N.Inputs) :
  R.v31939 (state s) (inputs i) = Zmod.unsigned (N.v31939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31939 s i)) at 1.
  unfold R.v31939, N.v31939.
  rewrite ?node_12945.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31940 (s : N.State) (i : N.Inputs) :
  R.v31940 (state s) (inputs i) = Zmod.unsigned (N.v31940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31940 s i)) at 1.
  unfold R.v31940, N.v31940.
  unfold R.v6, N.v6.
  rewrite !state_r1665_nr_5F1672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1665_nr_5F1672 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31941 (s : N.State) (i : N.Inputs) :
  R.v31941 (state s) (inputs i) = Zmod.unsigned (N.v31941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31941 s i)) at 1.
  unfold R.v31941, N.v31941.
  unfold R.v6, N.v6.
  rewrite ?node_12941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31942 (s : N.State) (i : N.Inputs) :
  R.v31942 (state s) (inputs i) = Zmod.unsigned (N.v31942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31942 s i)) at 1.
  unfold R.v31942, N.v31942.
  rewrite ?node_31940.
  rewrite ?node_31941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31943 (s : N.State) (i : N.Inputs) :
  R.v31943 (state s) (inputs i) = Zmod.unsigned (N.v31943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31943 s i)) at 1.
  unfold R.v31943, N.v31943.
  unfold R.v16484, N.v16484.
  rewrite ?node_31942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31944 (s : N.State) (i : N.Inputs) :
  R.v31944 (state s) (inputs i) = Zmod.unsigned (N.v31944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31944 s i)) at 1.
  unfold R.v31944, N.v31944.
  rewrite ?node_31939.
  rewrite ?node_31943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31945 (s : N.State) (i : N.Inputs) :
  R.v31945 (state s) (inputs i) = Zmod.unsigned (N.v31945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31945 s i)) at 1.
  unfold R.v31945, N.v31945.
  unfold R.v6, N.v6.
  rewrite ?node_31944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31946 (s : N.State) (i : N.Inputs) :
  R.v31946 (state s) (inputs i) = Zmod.unsigned (N.v31946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31946 s i)) at 1.
  unfold R.v31946, N.v31946.
  rewrite ?node_12946.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31947 (s : N.State) (i : N.Inputs) :
  R.v31947 (state s) (inputs i) = Zmod.unsigned (N.v31947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31947 s i)) at 1.
  unfold R.v31947, N.v31947.
  unfold R.v6, N.v6.
  rewrite ?node_13117.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31948 (s : N.State) (i : N.Inputs) :
  R.v31948 (state s) (inputs i) = Zmod.unsigned (N.v31948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31948 s i)) at 1.
  unfold R.v31948, N.v31948.
  rewrite ?node_31946.
  rewrite ?node_31947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31949 (s : N.State) (i : N.Inputs) :
  R.v31949 (state s) (inputs i) = Zmod.unsigned (N.v31949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31949 s i)) at 1.
  unfold R.v31949, N.v31949.
  rewrite ?node_31945.
  rewrite ?node_31948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31950 (s : N.State) (i : N.Inputs) :
  R.v31950 (state s) (inputs i) = Zmod.unsigned (N.v31950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31950 s i)) at 1.
  unfold R.v31950, N.v31950.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31951 (s : N.State) (i : N.Inputs) :
  R.v31951 (state s) (inputs i) = Zmod.unsigned (N.v31951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31951 s i)) at 1.
  unfold R.v31951, N.v31951.
  rewrite ?node_12953.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31952 (s : N.State) (i : N.Inputs) :
  R.v31952 (state s) (inputs i) = Zmod.unsigned (N.v31952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31952 s i)) at 1.
  unfold R.v31952, N.v31952.
  unfold R.v16463, N.v16463.
  rewrite !state_r1669_nr_5F1676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1669_nr_5F1676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31953 (s : N.State) (i : N.Inputs) :
  R.v31953 (state s) (inputs i) = Zmod.unsigned (N.v31953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31953 s i)) at 1.
  unfold R.v31953, N.v31953.
  unfold R.v16463, N.v16463.
  rewrite !state_r1668_nr_5F1675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1668_nr_5F1675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31954 (s : N.State) (i : N.Inputs) :
  R.v31954 (state s) (inputs i) = Zmod.unsigned (N.v31954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31954 s i)) at 1.
  unfold R.v31954, N.v31954.
  unfold R.v6, N.v6.
  rewrite !state_r1667_nr_5F1674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1667_nr_5F1674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31955 (s : N.State) (i : N.Inputs) :
  R.v31955 (state s) (inputs i) = Zmod.unsigned (N.v31955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31955 s i)) at 1.
  unfold R.v31955, N.v31955.
  unfold R.v6, N.v6.
  rewrite !state_r1666_nr_5F1673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1666_nr_5F1673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31956 (s : N.State) (i : N.Inputs) :
  R.v31956 (state s) (inputs i) = Zmod.unsigned (N.v31956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31956 s i)) at 1.
  unfold R.v31956, N.v31956.
  rewrite ?node_31954.
  rewrite ?node_31955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31957 (s : N.State) (i : N.Inputs) :
  R.v31957 (state s) (inputs i) = Zmod.unsigned (N.v31957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31957 s i)) at 1.
  unfold R.v31957, N.v31957.
  unfold R.v16484, N.v16484.
  rewrite ?node_31956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31958 (s : N.State) (i : N.Inputs) :
  R.v31958 (state s) (inputs i) = Zmod.unsigned (N.v31958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31958 s i)) at 1.
  unfold R.v31958, N.v31958.
  rewrite ?node_31951.
  rewrite ?node_31952.
  rewrite ?node_31953.
  rewrite ?node_31957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31959 (s : N.State) (i : N.Inputs) :
  R.v31959 (state s) (inputs i) = Zmod.unsigned (N.v31959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31959 s i)) at 1.
  unfold R.v31959, N.v31959.
  unfold R.v6, N.v6.
  rewrite ?node_31958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31960 (s : N.State) (i : N.Inputs) :
  R.v31960 (state s) (inputs i) = Zmod.unsigned (N.v31960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31960 s i)) at 1.
  unfold R.v31960, N.v31960.
  rewrite ?node_12954.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31961 (s : N.State) (i : N.Inputs) :
  R.v31961 (state s) (inputs i) = Zmod.unsigned (N.v31961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31961 s i)) at 1.
  unfold R.v31961, N.v31961.
  unfold R.v6, N.v6.
  rewrite ?node_13080.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31962 (s : N.State) (i : N.Inputs) :
  R.v31962 (state s) (inputs i) = Zmod.unsigned (N.v31962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31962 s i)) at 1.
  unfold R.v31962, N.v31962.
  unfold R.v6, N.v6.
  rewrite ?node_13121.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31963 (s : N.State) (i : N.Inputs) :
  R.v31963 (state s) (inputs i) = Zmod.unsigned (N.v31963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31963 s i)) at 1.
  unfold R.v31963, N.v31963.
  rewrite ?node_31960.
  rewrite ?node_31961.
  rewrite ?node_31962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31964 (s : N.State) (i : N.Inputs) :
  R.v31964 (state s) (inputs i) = Zmod.unsigned (N.v31964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31964 s i)) at 1.
  unfold R.v31964, N.v31964.
  rewrite ?node_31959.
  rewrite ?node_31963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31965 (s : N.State) (i : N.Inputs) :
  R.v31965 (state s) (inputs i) = Zmod.unsigned (N.v31965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31965 s i)) at 1.
  unfold R.v31965, N.v31965.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31966 (s : N.State) (i : N.Inputs) :
  R.v31966 (state s) (inputs i) = Zmod.unsigned (N.v31966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31966 s i)) at 1.
  unfold R.v31966, N.v31966.
  unfold R.v16463, N.v16463.
  rewrite !state_r1668_nr_5F1675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1668_nr_5F1675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31967 (s : N.State) (i : N.Inputs) :
  R.v31967 (state s) (inputs i) = Zmod.unsigned (N.v31967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31967 s i)) at 1.
  unfold R.v31967, N.v31967.
  unfold R.v6, N.v6.
  rewrite !state_r1667_nr_5F1674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1667_nr_5F1674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31968 (s : N.State) (i : N.Inputs) :
  R.v31968 (state s) (inputs i) = Zmod.unsigned (N.v31968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31968 s i)) at 1.
  unfold R.v31968, N.v31968.
  unfold R.v6, N.v6.
  rewrite !state_r1666_nr_5F1673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1666_nr_5F1673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31969 (s : N.State) (i : N.Inputs) :
  R.v31969 (state s) (inputs i) = Zmod.unsigned (N.v31969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31969 s i)) at 1.
  unfold R.v31969, N.v31969.
  rewrite ?node_31967.
  rewrite ?node_31968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31970 (s : N.State) (i : N.Inputs) :
  R.v31970 (state s) (inputs i) = Zmod.unsigned (N.v31970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31970 s i)) at 1.
  unfold R.v31970, N.v31970.
  unfold R.v16484, N.v16484.
  rewrite ?node_31969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31971 (s : N.State) (i : N.Inputs) :
  R.v31971 (state s) (inputs i) = Zmod.unsigned (N.v31971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31971 s i)) at 1.
  unfold R.v31971, N.v31971.
  rewrite ?node_31966.
  rewrite ?node_31970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31972 (s : N.State) (i : N.Inputs) :
  R.v31972 (state s) (inputs i) = Zmod.unsigned (N.v31972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31972 s i)) at 1.
  unfold R.v31972, N.v31972.
  unfold R.v6, N.v6.
  rewrite ?node_31971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31973 (s : N.State) (i : N.Inputs) :
  R.v31973 (state s) (inputs i) = Zmod.unsigned (N.v31973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31973 s i)) at 1.
  unfold R.v31973, N.v31973.
  rewrite ?node_12949.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31974 (s : N.State) (i : N.Inputs) :
  R.v31974 (state s) (inputs i) = Zmod.unsigned (N.v31974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31974 s i)) at 1.
  unfold R.v31974, N.v31974.
  unfold R.v6, N.v6.
  rewrite ?node_13080.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31975 (s : N.State) (i : N.Inputs) :
  R.v31975 (state s) (inputs i) = Zmod.unsigned (N.v31975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31975 s i)) at 1.
  unfold R.v31975, N.v31975.
  rewrite ?node_31973.
  rewrite ?node_31974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31976 (s : N.State) (i : N.Inputs) :
  R.v31976 (state s) (inputs i) = Zmod.unsigned (N.v31976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31976 s i)) at 1.
  unfold R.v31976, N.v31976.
  rewrite ?node_31972.
  rewrite ?node_31975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31977 (s : N.State) (i : N.Inputs) :
  R.v31977 (state s) (inputs i) = Zmod.unsigned (N.v31977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31977 s i)) at 1.
  unfold R.v31977, N.v31977.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31978 (s : N.State) (i : N.Inputs) :
  R.v31978 (state s) (inputs i) = Zmod.unsigned (N.v31978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31978 s i)) at 1.
  unfold R.v31978, N.v31978.
  rewrite ?node_12953.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31979 (s : N.State) (i : N.Inputs) :
  R.v31979 (state s) (inputs i) = Zmod.unsigned (N.v31979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31979 s i)) at 1.
  unfold R.v31979, N.v31979.
  unfold R.v6, N.v6.
  rewrite !state_r1669_nr_5F1676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1669_nr_5F1676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31980 (s : N.State) (i : N.Inputs) :
  R.v31980 (state s) (inputs i) = Zmod.unsigned (N.v31980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31980 s i)) at 1.
  unfold R.v31980, N.v31980.
  unfold R.v6, N.v6.
  rewrite ?node_12949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31981 (s : N.State) (i : N.Inputs) :
  R.v31981 (state s) (inputs i) = Zmod.unsigned (N.v31981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31981 s i)) at 1.
  unfold R.v31981, N.v31981.
  rewrite ?node_31979.
  rewrite ?node_31980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31982 (s : N.State) (i : N.Inputs) :
  R.v31982 (state s) (inputs i) = Zmod.unsigned (N.v31982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31982 s i)) at 1.
  unfold R.v31982, N.v31982.
  unfold R.v16484, N.v16484.
  rewrite ?node_31981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31983 (s : N.State) (i : N.Inputs) :
  R.v31983 (state s) (inputs i) = Zmod.unsigned (N.v31983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31983 s i)) at 1.
  unfold R.v31983, N.v31983.
  rewrite ?node_31978.
  rewrite ?node_31982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31984 (s : N.State) (i : N.Inputs) :
  R.v31984 (state s) (inputs i) = Zmod.unsigned (N.v31984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31984 s i)) at 1.
  unfold R.v31984, N.v31984.
  unfold R.v6, N.v6.
  rewrite ?node_31983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31985 (s : N.State) (i : N.Inputs) :
  R.v31985 (state s) (inputs i) = Zmod.unsigned (N.v31985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31985 s i)) at 1.
  unfold R.v31985, N.v31985.
  rewrite ?node_12954.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31986 (s : N.State) (i : N.Inputs) :
  R.v31986 (state s) (inputs i) = Zmod.unsigned (N.v31986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31986 s i)) at 1.
  unfold R.v31986, N.v31986.
  unfold R.v6, N.v6.
  rewrite ?node_13121.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31987 (s : N.State) (i : N.Inputs) :
  R.v31987 (state s) (inputs i) = Zmod.unsigned (N.v31987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31987 s i)) at 1.
  unfold R.v31987, N.v31987.
  rewrite ?node_31985.
  rewrite ?node_31986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31988 (s : N.State) (i : N.Inputs) :
  R.v31988 (state s) (inputs i) = Zmod.unsigned (N.v31988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31988 s i)) at 1.
  unfold R.v31988, N.v31988.
  rewrite ?node_31984.
  rewrite ?node_31987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31989 (s : N.State) (i : N.Inputs) :
  R.v31989 (state s) (inputs i) = Zmod.unsigned (N.v31989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31989 s i)) at 1.
  unfold R.v31989, N.v31989.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31990 (s : N.State) (i : N.Inputs) :
  R.v31990 (state s) (inputs i) = Zmod.unsigned (N.v31990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31990 s i)) at 1.
  unfold R.v31990, N.v31990.
  rewrite ?node_12965.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31991 (s : N.State) (i : N.Inputs) :
  R.v31991 (state s) (inputs i) = Zmod.unsigned (N.v31991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31991 s i)) at 1.
  unfold R.v31991, N.v31991.
  unfold R.v16463, N.v16463.
  rewrite !state_r1673_nr_5F1680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1673_nr_5F1680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31992 (s : N.State) (i : N.Inputs) :
  R.v31992 (state s) (inputs i) = Zmod.unsigned (N.v31992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31992 s i)) at 1.
  unfold R.v31992, N.v31992.
  unfold R.v16463, N.v16463.
  rewrite !state_r1672_nr_5F1679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1672_nr_5F1679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31993 (s : N.State) (i : N.Inputs) :
  R.v31993 (state s) (inputs i) = Zmod.unsigned (N.v31993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31993 s i)) at 1.
  unfold R.v31993, N.v31993.
  unfold R.v6, N.v6.
  rewrite !state_r1671_nr_5F1678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1671_nr_5F1678 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31994 (s : N.State) (i : N.Inputs) :
  R.v31994 (state s) (inputs i) = Zmod.unsigned (N.v31994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31994 s i)) at 1.
  unfold R.v31994, N.v31994.
  unfold R.v6, N.v6.
  rewrite !state_r1670_nr_5F1677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1670_nr_5F1677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31995 (s : N.State) (i : N.Inputs) :
  R.v31995 (state s) (inputs i) = Zmod.unsigned (N.v31995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31995 s i)) at 1.
  unfold R.v31995, N.v31995.
  rewrite ?node_31993.
  rewrite ?node_31994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31996 (s : N.State) (i : N.Inputs) :
  R.v31996 (state s) (inputs i) = Zmod.unsigned (N.v31996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31996 s i)) at 1.
  unfold R.v31996, N.v31996.
  unfold R.v16484, N.v16484.
  rewrite ?node_31995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31997 (s : N.State) (i : N.Inputs) :
  R.v31997 (state s) (inputs i) = Zmod.unsigned (N.v31997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31997 s i)) at 1.
  unfold R.v31997, N.v31997.
  rewrite ?node_31990.
  rewrite ?node_31991.
  rewrite ?node_31992.
  rewrite ?node_31996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31998 (s : N.State) (i : N.Inputs) :
  R.v31998 (state s) (inputs i) = Zmod.unsigned (N.v31998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31998 s i)) at 1.
  unfold R.v31998, N.v31998.
  unfold R.v6, N.v6.
  rewrite ?node_31997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31999 (s : N.State) (i : N.Inputs) :
  R.v31999 (state s) (inputs i) = Zmod.unsigned (N.v31999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31999 s i)) at 1.
  unfold R.v31999, N.v31999.
  rewrite ?node_12966.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
