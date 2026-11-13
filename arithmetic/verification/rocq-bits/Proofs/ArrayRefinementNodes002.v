(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes001.
Lemma node_2000 (s : N.State) (i : N.Inputs) :
  R.v2000 (state s) (inputs i) = Zmod.unsigned (N.v2000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2000 s i)) at 1.
  unfold R.v2000, N.v2000.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2001 (s : N.State) (i : N.Inputs) :
  R.v2001 (state s) (inputs i) = Zmod.unsigned (N.v2001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2001 s i)) at 1.
  unfold R.v2001, N.v2001.
  rewrite ?node_2000.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r789_nr_5F789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r789_nr_5F789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2002 (s : N.State) (i : N.Inputs) :
  R.v2002 (state s) (inputs i) = Zmod.unsigned (N.v2002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2002 s i)) at 1.
  unfold R.v2002, N.v2002.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2003 (s : N.State) (i : N.Inputs) :
  R.v2003 (state s) (inputs i) = Zmod.unsigned (N.v2003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2003 s i)) at 1.
  unfold R.v2003, N.v2003.
  rewrite ?node_2002.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r790_nr_5F790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r790_nr_5F790 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2004 (s : N.State) (i : N.Inputs) :
  R.v2004 (state s) (inputs i) = Zmod.unsigned (N.v2004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2004 s i)) at 1.
  unfold R.v2004, N.v2004.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2005 (s : N.State) (i : N.Inputs) :
  R.v2005 (state s) (inputs i) = Zmod.unsigned (N.v2005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2005 s i)) at 1.
  unfold R.v2005, N.v2005.
  rewrite ?node_2004.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r791_nr_5F791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r791_nr_5F791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2006 (s : N.State) (i : N.Inputs) :
  R.v2006 (state s) (inputs i) = Zmod.unsigned (N.v2006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2006 s i)) at 1.
  unfold R.v2006, N.v2006.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2007 (s : N.State) (i : N.Inputs) :
  R.v2007 (state s) (inputs i) = Zmod.unsigned (N.v2007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2007 s i)) at 1.
  unfold R.v2007, N.v2007.
  rewrite ?node_2006.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r792_nr_5F792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r792_nr_5F792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2008 (s : N.State) (i : N.Inputs) :
  R.v2008 (state s) (inputs i) = Zmod.unsigned (N.v2008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2008 s i)) at 1.
  unfold R.v2008, N.v2008.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2009 (s : N.State) (i : N.Inputs) :
  R.v2009 (state s) (inputs i) = Zmod.unsigned (N.v2009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2009 s i)) at 1.
  unfold R.v2009, N.v2009.
  rewrite ?node_2008.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r793_nr_5F793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r793_nr_5F793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2010 (s : N.State) (i : N.Inputs) :
  R.v2010 (state s) (inputs i) = Zmod.unsigned (N.v2010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2010 s i)) at 1.
  unfold R.v2010, N.v2010.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2011 (s : N.State) (i : N.Inputs) :
  R.v2011 (state s) (inputs i) = Zmod.unsigned (N.v2011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2011 s i)) at 1.
  unfold R.v2011, N.v2011.
  rewrite ?node_2010.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r794_nr_5F794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r794_nr_5F794 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2012 (s : N.State) (i : N.Inputs) :
  R.v2012 (state s) (inputs i) = Zmod.unsigned (N.v2012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2012 s i)) at 1.
  unfold R.v2012, N.v2012.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2013 (s : N.State) (i : N.Inputs) :
  R.v2013 (state s) (inputs i) = Zmod.unsigned (N.v2013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2013 s i)) at 1.
  unfold R.v2013, N.v2013.
  rewrite ?node_2012.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r795_nr_5F795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r795_nr_5F795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2014 (s : N.State) (i : N.Inputs) :
  R.v2014 (state s) (inputs i) = Zmod.unsigned (N.v2014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2014 s i)) at 1.
  unfold R.v2014, N.v2014.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2015 (s : N.State) (i : N.Inputs) :
  R.v2015 (state s) (inputs i) = Zmod.unsigned (N.v2015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2015 s i)) at 1.
  unfold R.v2015, N.v2015.
  rewrite ?node_2014.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r796_nr_5F796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r796_nr_5F796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2016 (s : N.State) (i : N.Inputs) :
  R.v2016 (state s) (inputs i) = Zmod.unsigned (N.v2016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2016 s i)) at 1.
  unfold R.v2016, N.v2016.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2017 (s : N.State) (i : N.Inputs) :
  R.v2017 (state s) (inputs i) = Zmod.unsigned (N.v2017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2017 s i)) at 1.
  unfold R.v2017, N.v2017.
  rewrite ?node_2016.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r797_nr_5F797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r797_nr_5F797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2018 (s : N.State) (i : N.Inputs) :
  R.v2018 (state s) (inputs i) = Zmod.unsigned (N.v2018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2018 s i)) at 1.
  unfold R.v2018, N.v2018.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2019 (s : N.State) (i : N.Inputs) :
  R.v2019 (state s) (inputs i) = Zmod.unsigned (N.v2019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2019 s i)) at 1.
  unfold R.v2019, N.v2019.
  rewrite ?node_2018.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r798_nr_5F798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r798_nr_5F798 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2020 (s : N.State) (i : N.Inputs) :
  R.v2020 (state s) (inputs i) = Zmod.unsigned (N.v2020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2020 s i)) at 1.
  unfold R.v2020, N.v2020.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2021 (s : N.State) (i : N.Inputs) :
  R.v2021 (state s) (inputs i) = Zmod.unsigned (N.v2021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2021 s i)) at 1.
  unfold R.v2021, N.v2021.
  rewrite ?node_2020.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r799_nr_5F799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r799_nr_5F799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2022 (s : N.State) (i : N.Inputs) :
  R.v2022 (state s) (inputs i) = Zmod.unsigned (N.v2022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2022 s i)) at 1.
  unfold R.v2022, N.v2022.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2023 (s : N.State) (i : N.Inputs) :
  R.v2023 (state s) (inputs i) = Zmod.unsigned (N.v2023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2023 s i)) at 1.
  unfold R.v2023, N.v2023.
  rewrite ?node_2022.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r800_nr_5F800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r800_nr_5F800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2024 (s : N.State) (i : N.Inputs) :
  R.v2024 (state s) (inputs i) = Zmod.unsigned (N.v2024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2024 s i)) at 1.
  unfold R.v2024, N.v2024.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2025 (s : N.State) (i : N.Inputs) :
  R.v2025 (state s) (inputs i) = Zmod.unsigned (N.v2025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2025 s i)) at 1.
  unfold R.v2025, N.v2025.
  rewrite ?node_2024.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r801_nr_5F801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r801_nr_5F801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2026 (s : N.State) (i : N.Inputs) :
  R.v2026 (state s) (inputs i) = Zmod.unsigned (N.v2026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2026 s i)) at 1.
  unfold R.v2026, N.v2026.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2027 (s : N.State) (i : N.Inputs) :
  R.v2027 (state s) (inputs i) = Zmod.unsigned (N.v2027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2027 s i)) at 1.
  unfold R.v2027, N.v2027.
  rewrite ?node_2026.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r802_nr_5F802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r802_nr_5F802 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2028 (s : N.State) (i : N.Inputs) :
  R.v2028 (state s) (inputs i) = Zmod.unsigned (N.v2028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2028 s i)) at 1.
  unfold R.v2028, N.v2028.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2029 (s : N.State) (i : N.Inputs) :
  R.v2029 (state s) (inputs i) = Zmod.unsigned (N.v2029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2029 s i)) at 1.
  unfold R.v2029, N.v2029.
  rewrite ?node_2028.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r803_nr_5F803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r803_nr_5F803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2030 (s : N.State) (i : N.Inputs) :
  R.v2030 (state s) (inputs i) = Zmod.unsigned (N.v2030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2030 s i)) at 1.
  unfold R.v2030, N.v2030.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2031 (s : N.State) (i : N.Inputs) :
  R.v2031 (state s) (inputs i) = Zmod.unsigned (N.v2031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2031 s i)) at 1.
  unfold R.v2031, N.v2031.
  rewrite ?node_2030.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r804_nr_5F804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r804_nr_5F804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2032 (s : N.State) (i : N.Inputs) :
  R.v2032 (state s) (inputs i) = Zmod.unsigned (N.v2032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2032 s i)) at 1.
  unfold R.v2032, N.v2032.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2033 (s : N.State) (i : N.Inputs) :
  R.v2033 (state s) (inputs i) = Zmod.unsigned (N.v2033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2033 s i)) at 1.
  unfold R.v2033, N.v2033.
  rewrite ?node_2032.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r805_nr_5F805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r805_nr_5F805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2034 (s : N.State) (i : N.Inputs) :
  R.v2034 (state s) (inputs i) = Zmod.unsigned (N.v2034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2034 s i)) at 1.
  unfold R.v2034, N.v2034.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2035 (s : N.State) (i : N.Inputs) :
  R.v2035 (state s) (inputs i) = Zmod.unsigned (N.v2035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2035 s i)) at 1.
  unfold R.v2035, N.v2035.
  rewrite ?node_2034.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r806_nr_5F806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r806_nr_5F806 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2036 (s : N.State) (i : N.Inputs) :
  R.v2036 (state s) (inputs i) = Zmod.unsigned (N.v2036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2036 s i)) at 1.
  unfold R.v2036, N.v2036.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2037 (s : N.State) (i : N.Inputs) :
  R.v2037 (state s) (inputs i) = Zmod.unsigned (N.v2037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2037 s i)) at 1.
  unfold R.v2037, N.v2037.
  rewrite ?node_2036.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r807_nr_5F807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r807_nr_5F807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2038 (s : N.State) (i : N.Inputs) :
  R.v2038 (state s) (inputs i) = Zmod.unsigned (N.v2038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2038 s i)) at 1.
  unfold R.v2038, N.v2038.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2039 (s : N.State) (i : N.Inputs) :
  R.v2039 (state s) (inputs i) = Zmod.unsigned (N.v2039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2039 s i)) at 1.
  unfold R.v2039, N.v2039.
  rewrite ?node_2038.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r808_nr_5F808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r808_nr_5F808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2040 (s : N.State) (i : N.Inputs) :
  R.v2040 (state s) (inputs i) = Zmod.unsigned (N.v2040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2040 s i)) at 1.
  unfold R.v2040, N.v2040.
  rewrite ?node_1983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2041 (s : N.State) (i : N.Inputs) :
  R.v2041 (state s) (inputs i) = Zmod.unsigned (N.v2041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2041 s i)) at 1.
  unfold R.v2041, N.v2041.
  rewrite ?node_2040.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r809_nr_5F809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r809_nr_5F809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2042 (s : N.State) (i : N.Inputs) :
  R.v2042 (state s) (inputs i) = Zmod.unsigned (N.v2042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2042 s i)) at 1.
  unfold R.v2042, N.v2042.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2043 (s : N.State) (i : N.Inputs) :
  R.v2043 (state s) (inputs i) = Zmod.unsigned (N.v2043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2043 s i)) at 1.
  unfold R.v2043, N.v2043.
  rewrite ?node_2042.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r810_nr_5F810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r810_nr_5F810 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2044 (s : N.State) (i : N.Inputs) :
  R.v2044 (state s) (inputs i) = Zmod.unsigned (N.v2044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2044 s i)) at 1.
  unfold R.v2044, N.v2044.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2045 (s : N.State) (i : N.Inputs) :
  R.v2045 (state s) (inputs i) = Zmod.unsigned (N.v2045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2045 s i)) at 1.
  unfold R.v2045, N.v2045.
  rewrite ?node_2044.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r811_nr_5F811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r811_nr_5F811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2046 (s : N.State) (i : N.Inputs) :
  R.v2046 (state s) (inputs i) = Zmod.unsigned (N.v2046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2046 s i)) at 1.
  unfold R.v2046, N.v2046.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2047 (s : N.State) (i : N.Inputs) :
  R.v2047 (state s) (inputs i) = Zmod.unsigned (N.v2047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2047 s i)) at 1.
  unfold R.v2047, N.v2047.
  rewrite ?node_2046.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r812_nr_5F812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r812_nr_5F812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2048 (s : N.State) (i : N.Inputs) :
  R.v2048 (state s) (inputs i) = Zmod.unsigned (N.v2048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2048 s i)) at 1.
  unfold R.v2048, N.v2048.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2049 (s : N.State) (i : N.Inputs) :
  R.v2049 (state s) (inputs i) = Zmod.unsigned (N.v2049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2049 s i)) at 1.
  unfold R.v2049, N.v2049.
  rewrite ?node_2048.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r813_nr_5F813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r813_nr_5F813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2050 (s : N.State) (i : N.Inputs) :
  R.v2050 (state s) (inputs i) = Zmod.unsigned (N.v2050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2050 s i)) at 1.
  unfold R.v2050, N.v2050.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2051 (s : N.State) (i : N.Inputs) :
  R.v2051 (state s) (inputs i) = Zmod.unsigned (N.v2051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2051 s i)) at 1.
  unfold R.v2051, N.v2051.
  rewrite ?node_2050.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r814_nr_5F814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r814_nr_5F814 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2052 (s : N.State) (i : N.Inputs) :
  R.v2052 (state s) (inputs i) = Zmod.unsigned (N.v2052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2052 s i)) at 1.
  unfold R.v2052, N.v2052.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2053 (s : N.State) (i : N.Inputs) :
  R.v2053 (state s) (inputs i) = Zmod.unsigned (N.v2053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2053 s i)) at 1.
  unfold R.v2053, N.v2053.
  rewrite ?node_2052.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r815_nr_5F815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r815_nr_5F815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2054 (s : N.State) (i : N.Inputs) :
  R.v2054 (state s) (inputs i) = Zmod.unsigned (N.v2054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2054 s i)) at 1.
  unfold R.v2054, N.v2054.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2055 (s : N.State) (i : N.Inputs) :
  R.v2055 (state s) (inputs i) = Zmod.unsigned (N.v2055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2055 s i)) at 1.
  unfold R.v2055, N.v2055.
  rewrite ?node_2054.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r816_nr_5F816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r816_nr_5F816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2056 (s : N.State) (i : N.Inputs) :
  R.v2056 (state s) (inputs i) = Zmod.unsigned (N.v2056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2056 s i)) at 1.
  unfold R.v2056, N.v2056.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2057 (s : N.State) (i : N.Inputs) :
  R.v2057 (state s) (inputs i) = Zmod.unsigned (N.v2057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2057 s i)) at 1.
  unfold R.v2057, N.v2057.
  rewrite ?node_2056.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r817_nr_5F817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r817_nr_5F817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2058 (s : N.State) (i : N.Inputs) :
  R.v2058 (state s) (inputs i) = Zmod.unsigned (N.v2058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2058 s i)) at 1.
  unfold R.v2058, N.v2058.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2059 (s : N.State) (i : N.Inputs) :
  R.v2059 (state s) (inputs i) = Zmod.unsigned (N.v2059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2059 s i)) at 1.
  unfold R.v2059, N.v2059.
  rewrite ?node_2058.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r818_nr_5F818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r818_nr_5F818 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2060 (s : N.State) (i : N.Inputs) :
  R.v2060 (state s) (inputs i) = Zmod.unsigned (N.v2060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2060 s i)) at 1.
  unfold R.v2060, N.v2060.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2061 (s : N.State) (i : N.Inputs) :
  R.v2061 (state s) (inputs i) = Zmod.unsigned (N.v2061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2061 s i)) at 1.
  unfold R.v2061, N.v2061.
  rewrite ?node_2060.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r819_nr_5F819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r819_nr_5F819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2062 (s : N.State) (i : N.Inputs) :
  R.v2062 (state s) (inputs i) = Zmod.unsigned (N.v2062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2062 s i)) at 1.
  unfold R.v2062, N.v2062.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2063 (s : N.State) (i : N.Inputs) :
  R.v2063 (state s) (inputs i) = Zmod.unsigned (N.v2063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2063 s i)) at 1.
  unfold R.v2063, N.v2063.
  rewrite ?node_2062.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r820_nr_5F820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r820_nr_5F820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2064 (s : N.State) (i : N.Inputs) :
  R.v2064 (state s) (inputs i) = Zmod.unsigned (N.v2064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2064 s i)) at 1.
  unfold R.v2064, N.v2064.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2065 (s : N.State) (i : N.Inputs) :
  R.v2065 (state s) (inputs i) = Zmod.unsigned (N.v2065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2065 s i)) at 1.
  unfold R.v2065, N.v2065.
  rewrite ?node_2064.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r821_nr_5F821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r821_nr_5F821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2066 (s : N.State) (i : N.Inputs) :
  R.v2066 (state s) (inputs i) = Zmod.unsigned (N.v2066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2066 s i)) at 1.
  unfold R.v2066, N.v2066.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2067 (s : N.State) (i : N.Inputs) :
  R.v2067 (state s) (inputs i) = Zmod.unsigned (N.v2067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2067 s i)) at 1.
  unfold R.v2067, N.v2067.
  rewrite ?node_2066.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r822_nr_5F822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r822_nr_5F822 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2068 (s : N.State) (i : N.Inputs) :
  R.v2068 (state s) (inputs i) = Zmod.unsigned (N.v2068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2068 s i)) at 1.
  unfold R.v2068, N.v2068.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2069 (s : N.State) (i : N.Inputs) :
  R.v2069 (state s) (inputs i) = Zmod.unsigned (N.v2069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2069 s i)) at 1.
  unfold R.v2069, N.v2069.
  rewrite ?node_2068.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r823_nr_5F823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r823_nr_5F823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2070 (s : N.State) (i : N.Inputs) :
  R.v2070 (state s) (inputs i) = Zmod.unsigned (N.v2070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2070 s i)) at 1.
  unfold R.v2070, N.v2070.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2071 (s : N.State) (i : N.Inputs) :
  R.v2071 (state s) (inputs i) = Zmod.unsigned (N.v2071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2071 s i)) at 1.
  unfold R.v2071, N.v2071.
  rewrite ?node_2070.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r824_nr_5F824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r824_nr_5F824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2072 (s : N.State) (i : N.Inputs) :
  R.v2072 (state s) (inputs i) = Zmod.unsigned (N.v2072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2072 s i)) at 1.
  unfold R.v2072, N.v2072.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2073 (s : N.State) (i : N.Inputs) :
  R.v2073 (state s) (inputs i) = Zmod.unsigned (N.v2073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2073 s i)) at 1.
  unfold R.v2073, N.v2073.
  rewrite ?node_2072.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r825_nr_5F825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r825_nr_5F825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2074 (s : N.State) (i : N.Inputs) :
  R.v2074 (state s) (inputs i) = Zmod.unsigned (N.v2074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2074 s i)) at 1.
  unfold R.v2074, N.v2074.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2075 (s : N.State) (i : N.Inputs) :
  R.v2075 (state s) (inputs i) = Zmod.unsigned (N.v2075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2075 s i)) at 1.
  unfold R.v2075, N.v2075.
  rewrite ?node_2074.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r826_nr_5F826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r826_nr_5F826 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2076 (s : N.State) (i : N.Inputs) :
  R.v2076 (state s) (inputs i) = Zmod.unsigned (N.v2076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2076 s i)) at 1.
  unfold R.v2076, N.v2076.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2077 (s : N.State) (i : N.Inputs) :
  R.v2077 (state s) (inputs i) = Zmod.unsigned (N.v2077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2077 s i)) at 1.
  unfold R.v2077, N.v2077.
  rewrite ?node_2076.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r827_nr_5F827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r827_nr_5F827 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2078 (s : N.State) (i : N.Inputs) :
  R.v2078 (state s) (inputs i) = Zmod.unsigned (N.v2078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2078 s i)) at 1.
  unfold R.v2078, N.v2078.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2079 (s : N.State) (i : N.Inputs) :
  R.v2079 (state s) (inputs i) = Zmod.unsigned (N.v2079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2079 s i)) at 1.
  unfold R.v2079, N.v2079.
  rewrite ?node_2078.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r828_nr_5F828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r828_nr_5F828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2080 (s : N.State) (i : N.Inputs) :
  R.v2080 (state s) (inputs i) = Zmod.unsigned (N.v2080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2080 s i)) at 1.
  unfold R.v2080, N.v2080.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2081 (s : N.State) (i : N.Inputs) :
  R.v2081 (state s) (inputs i) = Zmod.unsigned (N.v2081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2081 s i)) at 1.
  unfold R.v2081, N.v2081.
  rewrite ?node_2080.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r829_nr_5F829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r829_nr_5F829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2082 (s : N.State) (i : N.Inputs) :
  R.v2082 (state s) (inputs i) = Zmod.unsigned (N.v2082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2082 s i)) at 1.
  unfold R.v2082, N.v2082.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2083 (s : N.State) (i : N.Inputs) :
  R.v2083 (state s) (inputs i) = Zmod.unsigned (N.v2083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2083 s i)) at 1.
  unfold R.v2083, N.v2083.
  rewrite ?node_2082.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r830_nr_5F830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r830_nr_5F830 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2084 (s : N.State) (i : N.Inputs) :
  R.v2084 (state s) (inputs i) = Zmod.unsigned (N.v2084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2084 s i)) at 1.
  unfold R.v2084, N.v2084.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2085 (s : N.State) (i : N.Inputs) :
  R.v2085 (state s) (inputs i) = Zmod.unsigned (N.v2085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2085 s i)) at 1.
  unfold R.v2085, N.v2085.
  rewrite ?node_2084.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r831_nr_5F831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r831_nr_5F831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2086 (s : N.State) (i : N.Inputs) :
  R.v2086 (state s) (inputs i) = Zmod.unsigned (N.v2086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2086 s i)) at 1.
  unfold R.v2086, N.v2086.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2087 (s : N.State) (i : N.Inputs) :
  R.v2087 (state s) (inputs i) = Zmod.unsigned (N.v2087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2087 s i)) at 1.
  unfold R.v2087, N.v2087.
  rewrite ?node_2086.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r832_nr_5F832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r832_nr_5F832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2088 (s : N.State) (i : N.Inputs) :
  R.v2088 (state s) (inputs i) = Zmod.unsigned (N.v2088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2088 s i)) at 1.
  unfold R.v2088, N.v2088.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2089 (s : N.State) (i : N.Inputs) :
  R.v2089 (state s) (inputs i) = Zmod.unsigned (N.v2089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2089 s i)) at 1.
  unfold R.v2089, N.v2089.
  rewrite ?node_2088.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r833_nr_5F833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r833_nr_5F833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2090 (s : N.State) (i : N.Inputs) :
  R.v2090 (state s) (inputs i) = Zmod.unsigned (N.v2090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2090 s i)) at 1.
  unfold R.v2090, N.v2090.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2091 (s : N.State) (i : N.Inputs) :
  R.v2091 (state s) (inputs i) = Zmod.unsigned (N.v2091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2091 s i)) at 1.
  unfold R.v2091, N.v2091.
  rewrite ?node_2090.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r834_nr_5F834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r834_nr_5F834 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2092 (s : N.State) (i : N.Inputs) :
  R.v2092 (state s) (inputs i) = Zmod.unsigned (N.v2092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2092 s i)) at 1.
  unfold R.v2092, N.v2092.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2093 (s : N.State) (i : N.Inputs) :
  R.v2093 (state s) (inputs i) = Zmod.unsigned (N.v2093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2093 s i)) at 1.
  unfold R.v2093, N.v2093.
  rewrite ?node_2092.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r835_nr_5F835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r835_nr_5F835 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2094 (s : N.State) (i : N.Inputs) :
  R.v2094 (state s) (inputs i) = Zmod.unsigned (N.v2094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2094 s i)) at 1.
  unfold R.v2094, N.v2094.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2095 (s : N.State) (i : N.Inputs) :
  R.v2095 (state s) (inputs i) = Zmod.unsigned (N.v2095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2095 s i)) at 1.
  unfold R.v2095, N.v2095.
  rewrite ?node_2094.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r836_nr_5F836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r836_nr_5F836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2096 (s : N.State) (i : N.Inputs) :
  R.v2096 (state s) (inputs i) = Zmod.unsigned (N.v2096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2096 s i)) at 1.
  unfold R.v2096, N.v2096.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2097 (s : N.State) (i : N.Inputs) :
  R.v2097 (state s) (inputs i) = Zmod.unsigned (N.v2097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2097 s i)) at 1.
  unfold R.v2097, N.v2097.
  unfold R.v33, N.v33.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2098 (s : N.State) (i : N.Inputs) :
  R.v2098 (state s) (inputs i) = Zmod.unsigned (N.v2098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2098 s i)) at 1.
  unfold R.v2098, N.v2098.
  unfold R.v35, N.v35.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2099 (s : N.State) (i : N.Inputs) :
  R.v2099 (state s) (inputs i) = Zmod.unsigned (N.v2099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2099 s i)) at 1.
  unfold R.v2099, N.v2099.
  rewrite ?node_2097.
  rewrite ?node_2098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2100 (s : N.State) (i : N.Inputs) :
  R.v2100 (state s) (inputs i) = Zmod.unsigned (N.v2100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2100 s i)) at 1.
  unfold R.v2100, N.v2100.
  unfold R.v39, N.v39.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2101 (s : N.State) (i : N.Inputs) :
  R.v2101 (state s) (inputs i) = Zmod.unsigned (N.v2101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2101 s i)) at 1.
  unfold R.v2101, N.v2101.
  unfold R.v42, N.v42.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2102 (s : N.State) (i : N.Inputs) :
  R.v2102 (state s) (inputs i) = Zmod.unsigned (N.v2102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2102 s i)) at 1.
  unfold R.v2102, N.v2102.
  unfold R.v45, N.v45.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2103 (s : N.State) (i : N.Inputs) :
  R.v2103 (state s) (inputs i) = Zmod.unsigned (N.v2103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2103 s i)) at 1.
  unfold R.v2103, N.v2103.
  unfold R.v47, N.v47.
  rewrite ?node_2096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2104 (s : N.State) (i : N.Inputs) :
  R.v2104 (state s) (inputs i) = Zmod.unsigned (N.v2104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2104 s i)) at 1.
  unfold R.v2104, N.v2104.
  rewrite ?node_2102.
  rewrite ?node_2103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2105 (s : N.State) (i : N.Inputs) :
  R.v2105 (state s) (inputs i) = Zmod.unsigned (N.v2105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2105 s i)) at 1.
  unfold R.v2105, N.v2105.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2106 (s : N.State) (i : N.Inputs) :
  R.v2106 (state s) (inputs i) = Zmod.unsigned (N.v2106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2106 s i)) at 1.
  unfold R.v2106, N.v2106.
  rewrite ?node_44.
  rewrite ?node_2101.
  rewrite ?node_2105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2107 (s : N.State) (i : N.Inputs) :
  R.v2107 (state s) (inputs i) = Zmod.unsigned (N.v2107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2107 s i)) at 1.
  unfold R.v2107, N.v2107.
  rewrite ?node_41.
  rewrite ?node_2100.
  rewrite ?node_2106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2108 (s : N.State) (i : N.Inputs) :
  R.v2108 (state s) (inputs i) = Zmod.unsigned (N.v2108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2108 s i)) at 1.
  unfold R.v2108, N.v2108.
  rewrite ?node_38.
  rewrite ?node_2099.
  rewrite ?node_2107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2109 (s : N.State) (i : N.Inputs) :
  R.v2109 (state s) (inputs i) = Zmod.unsigned (N.v2109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2109 s i)) at 1.
  unfold R.v2109, N.v2109.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2110 (s : N.State) (i : N.Inputs) :
  R.v2110 (state s) (inputs i) = Zmod.unsigned (N.v2110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2110 s i)) at 1.
  unfold R.v2110, N.v2110.
  rewrite ?node_2109.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r837_nr_5F837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r837_nr_5F837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2111 (s : N.State) (i : N.Inputs) :
  R.v2111 (state s) (inputs i) = Zmod.unsigned (N.v2111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2111 s i)) at 1.
  unfold R.v2111, N.v2111.
  unfold R.v6, N.v6.
  rewrite ?node_2100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2112 (s : N.State) (i : N.Inputs) :
  R.v2112 (state s) (inputs i) = Zmod.unsigned (N.v2112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2112 s i)) at 1.
  unfold R.v2112, N.v2112.
  unfold R.v19, N.v19.
  rewrite ?node_2099.
  rewrite ?node_2111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2113 (s : N.State) (i : N.Inputs) :
  R.v2113 (state s) (inputs i) = Zmod.unsigned (N.v2113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2113 s i)) at 1.
  unfold R.v2113, N.v2113.
  rewrite ?node_2112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2114 (s : N.State) (i : N.Inputs) :
  R.v2114 (state s) (inputs i) = Zmod.unsigned (N.v2114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2114 s i)) at 1.
  unfold R.v2114, N.v2114.
  rewrite ?node_2113.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r838_nr_5F838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r838_nr_5F838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2115 (s : N.State) (i : N.Inputs) :
  R.v2115 (state s) (inputs i) = Zmod.unsigned (N.v2115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2115 s i)) at 1.
  unfold R.v2115, N.v2115.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2116 (s : N.State) (i : N.Inputs) :
  R.v2116 (state s) (inputs i) = Zmod.unsigned (N.v2116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2116 s i)) at 1.
  unfold R.v2116, N.v2116.
  rewrite ?node_2115.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r839_nr_5F839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r839_nr_5F839 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2117 (s : N.State) (i : N.Inputs) :
  R.v2117 (state s) (inputs i) = Zmod.unsigned (N.v2117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2117 s i)) at 1.
  unfold R.v2117, N.v2117.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2118 (s : N.State) (i : N.Inputs) :
  R.v2118 (state s) (inputs i) = Zmod.unsigned (N.v2118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2118 s i)) at 1.
  unfold R.v2118, N.v2118.
  rewrite ?node_2117.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r840_nr_5F840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r840_nr_5F840 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2119 (s : N.State) (i : N.Inputs) :
  R.v2119 (state s) (inputs i) = Zmod.unsigned (N.v2119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2119 s i)) at 1.
  unfold R.v2119, N.v2119.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2120 (s : N.State) (i : N.Inputs) :
  R.v2120 (state s) (inputs i) = Zmod.unsigned (N.v2120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2120 s i)) at 1.
  unfold R.v2120, N.v2120.
  rewrite ?node_2119.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r841_nr_5F841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r841_nr_5F841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2121 (s : N.State) (i : N.Inputs) :
  R.v2121 (state s) (inputs i) = Zmod.unsigned (N.v2121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2121 s i)) at 1.
  unfold R.v2121, N.v2121.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2122 (s : N.State) (i : N.Inputs) :
  R.v2122 (state s) (inputs i) = Zmod.unsigned (N.v2122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2122 s i)) at 1.
  unfold R.v2122, N.v2122.
  rewrite ?node_2121.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r842_nr_5F842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r842_nr_5F842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2123 (s : N.State) (i : N.Inputs) :
  R.v2123 (state s) (inputs i) = Zmod.unsigned (N.v2123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2123 s i)) at 1.
  unfold R.v2123, N.v2123.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2124 (s : N.State) (i : N.Inputs) :
  R.v2124 (state s) (inputs i) = Zmod.unsigned (N.v2124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2124 s i)) at 1.
  unfold R.v2124, N.v2124.
  rewrite ?node_2123.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r843_nr_5F843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r843_nr_5F843 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2125 (s : N.State) (i : N.Inputs) :
  R.v2125 (state s) (inputs i) = Zmod.unsigned (N.v2125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2125 s i)) at 1.
  unfold R.v2125, N.v2125.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2126 (s : N.State) (i : N.Inputs) :
  R.v2126 (state s) (inputs i) = Zmod.unsigned (N.v2126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2126 s i)) at 1.
  unfold R.v2126, N.v2126.
  rewrite ?node_2125.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r844_nr_5F844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r844_nr_5F844 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2127 (s : N.State) (i : N.Inputs) :
  R.v2127 (state s) (inputs i) = Zmod.unsigned (N.v2127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2127 s i)) at 1.
  unfold R.v2127, N.v2127.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2128 (s : N.State) (i : N.Inputs) :
  R.v2128 (state s) (inputs i) = Zmod.unsigned (N.v2128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2128 s i)) at 1.
  unfold R.v2128, N.v2128.
  rewrite ?node_2127.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r845_nr_5F845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r845_nr_5F845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2129 (s : N.State) (i : N.Inputs) :
  R.v2129 (state s) (inputs i) = Zmod.unsigned (N.v2129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2129 s i)) at 1.
  unfold R.v2129, N.v2129.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2130 (s : N.State) (i : N.Inputs) :
  R.v2130 (state s) (inputs i) = Zmod.unsigned (N.v2130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2130 s i)) at 1.
  unfold R.v2130, N.v2130.
  rewrite ?node_2129.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r846_nr_5F846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r846_nr_5F846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2131 (s : N.State) (i : N.Inputs) :
  R.v2131 (state s) (inputs i) = Zmod.unsigned (N.v2131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2131 s i)) at 1.
  unfold R.v2131, N.v2131.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2132 (s : N.State) (i : N.Inputs) :
  R.v2132 (state s) (inputs i) = Zmod.unsigned (N.v2132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2132 s i)) at 1.
  unfold R.v2132, N.v2132.
  rewrite ?node_2131.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r847_nr_5F847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r847_nr_5F847 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2133 (s : N.State) (i : N.Inputs) :
  R.v2133 (state s) (inputs i) = Zmod.unsigned (N.v2133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2133 s i)) at 1.
  unfold R.v2133, N.v2133.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2134 (s : N.State) (i : N.Inputs) :
  R.v2134 (state s) (inputs i) = Zmod.unsigned (N.v2134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2134 s i)) at 1.
  unfold R.v2134, N.v2134.
  rewrite ?node_2133.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r848_nr_5F848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r848_nr_5F848 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2135 (s : N.State) (i : N.Inputs) :
  R.v2135 (state s) (inputs i) = Zmod.unsigned (N.v2135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2135 s i)) at 1.
  unfold R.v2135, N.v2135.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2136 (s : N.State) (i : N.Inputs) :
  R.v2136 (state s) (inputs i) = Zmod.unsigned (N.v2136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2136 s i)) at 1.
  unfold R.v2136, N.v2136.
  rewrite ?node_2135.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r849_nr_5F849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r849_nr_5F849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2137 (s : N.State) (i : N.Inputs) :
  R.v2137 (state s) (inputs i) = Zmod.unsigned (N.v2137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2137 s i)) at 1.
  unfold R.v2137, N.v2137.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2138 (s : N.State) (i : N.Inputs) :
  R.v2138 (state s) (inputs i) = Zmod.unsigned (N.v2138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2138 s i)) at 1.
  unfold R.v2138, N.v2138.
  rewrite ?node_2137.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r850_nr_5F850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r850_nr_5F850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2139 (s : N.State) (i : N.Inputs) :
  R.v2139 (state s) (inputs i) = Zmod.unsigned (N.v2139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2139 s i)) at 1.
  unfold R.v2139, N.v2139.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2140 (s : N.State) (i : N.Inputs) :
  R.v2140 (state s) (inputs i) = Zmod.unsigned (N.v2140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2140 s i)) at 1.
  unfold R.v2140, N.v2140.
  rewrite ?node_2139.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r851_nr_5F851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r851_nr_5F851 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2141 (s : N.State) (i : N.Inputs) :
  R.v2141 (state s) (inputs i) = Zmod.unsigned (N.v2141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2141 s i)) at 1.
  unfold R.v2141, N.v2141.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2142 (s : N.State) (i : N.Inputs) :
  R.v2142 (state s) (inputs i) = Zmod.unsigned (N.v2142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2142 s i)) at 1.
  unfold R.v2142, N.v2142.
  rewrite ?node_2141.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r852_nr_5F852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r852_nr_5F852 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2143 (s : N.State) (i : N.Inputs) :
  R.v2143 (state s) (inputs i) = Zmod.unsigned (N.v2143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2143 s i)) at 1.
  unfold R.v2143, N.v2143.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2144 (s : N.State) (i : N.Inputs) :
  R.v2144 (state s) (inputs i) = Zmod.unsigned (N.v2144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2144 s i)) at 1.
  unfold R.v2144, N.v2144.
  rewrite ?node_2143.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r853_nr_5F853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r853_nr_5F853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2145 (s : N.State) (i : N.Inputs) :
  R.v2145 (state s) (inputs i) = Zmod.unsigned (N.v2145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2145 s i)) at 1.
  unfold R.v2145, N.v2145.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2146 (s : N.State) (i : N.Inputs) :
  R.v2146 (state s) (inputs i) = Zmod.unsigned (N.v2146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2146 s i)) at 1.
  unfold R.v2146, N.v2146.
  rewrite ?node_2145.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r854_nr_5F854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r854_nr_5F854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2147 (s : N.State) (i : N.Inputs) :
  R.v2147 (state s) (inputs i) = Zmod.unsigned (N.v2147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2147 s i)) at 1.
  unfold R.v2147, N.v2147.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2148 (s : N.State) (i : N.Inputs) :
  R.v2148 (state s) (inputs i) = Zmod.unsigned (N.v2148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2148 s i)) at 1.
  unfold R.v2148, N.v2148.
  rewrite ?node_2147.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r855_nr_5F855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r855_nr_5F855 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2149 (s : N.State) (i : N.Inputs) :
  R.v2149 (state s) (inputs i) = Zmod.unsigned (N.v2149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2149 s i)) at 1.
  unfold R.v2149, N.v2149.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2150 (s : N.State) (i : N.Inputs) :
  R.v2150 (state s) (inputs i) = Zmod.unsigned (N.v2150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2150 s i)) at 1.
  unfold R.v2150, N.v2150.
  rewrite ?node_2149.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r856_nr_5F856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r856_nr_5F856 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2151 (s : N.State) (i : N.Inputs) :
  R.v2151 (state s) (inputs i) = Zmod.unsigned (N.v2151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2151 s i)) at 1.
  unfold R.v2151, N.v2151.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2152 (s : N.State) (i : N.Inputs) :
  R.v2152 (state s) (inputs i) = Zmod.unsigned (N.v2152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2152 s i)) at 1.
  unfold R.v2152, N.v2152.
  rewrite ?node_2151.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r857_nr_5F857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r857_nr_5F857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2153 (s : N.State) (i : N.Inputs) :
  R.v2153 (state s) (inputs i) = Zmod.unsigned (N.v2153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2153 s i)) at 1.
  unfold R.v2153, N.v2153.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2154 (s : N.State) (i : N.Inputs) :
  R.v2154 (state s) (inputs i) = Zmod.unsigned (N.v2154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2154 s i)) at 1.
  unfold R.v2154, N.v2154.
  rewrite ?node_2153.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r858_nr_5F858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r858_nr_5F858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2155 (s : N.State) (i : N.Inputs) :
  R.v2155 (state s) (inputs i) = Zmod.unsigned (N.v2155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2155 s i)) at 1.
  unfold R.v2155, N.v2155.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2156 (s : N.State) (i : N.Inputs) :
  R.v2156 (state s) (inputs i) = Zmod.unsigned (N.v2156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2156 s i)) at 1.
  unfold R.v2156, N.v2156.
  rewrite ?node_2155.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r859_nr_5F859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r859_nr_5F859 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2157 (s : N.State) (i : N.Inputs) :
  R.v2157 (state s) (inputs i) = Zmod.unsigned (N.v2157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2157 s i)) at 1.
  unfold R.v2157, N.v2157.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2158 (s : N.State) (i : N.Inputs) :
  R.v2158 (state s) (inputs i) = Zmod.unsigned (N.v2158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2158 s i)) at 1.
  unfold R.v2158, N.v2158.
  rewrite ?node_2157.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r860_nr_5F860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r860_nr_5F860 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2159 (s : N.State) (i : N.Inputs) :
  R.v2159 (state s) (inputs i) = Zmod.unsigned (N.v2159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2159 s i)) at 1.
  unfold R.v2159, N.v2159.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2160 (s : N.State) (i : N.Inputs) :
  R.v2160 (state s) (inputs i) = Zmod.unsigned (N.v2160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2160 s i)) at 1.
  unfold R.v2160, N.v2160.
  rewrite ?node_2159.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r861_nr_5F861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r861_nr_5F861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2161 (s : N.State) (i : N.Inputs) :
  R.v2161 (state s) (inputs i) = Zmod.unsigned (N.v2161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2161 s i)) at 1.
  unfold R.v2161, N.v2161.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2162 (s : N.State) (i : N.Inputs) :
  R.v2162 (state s) (inputs i) = Zmod.unsigned (N.v2162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2162 s i)) at 1.
  unfold R.v2162, N.v2162.
  rewrite ?node_2161.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r862_nr_5F862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r862_nr_5F862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2163 (s : N.State) (i : N.Inputs) :
  R.v2163 (state s) (inputs i) = Zmod.unsigned (N.v2163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2163 s i)) at 1.
  unfold R.v2163, N.v2163.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2164 (s : N.State) (i : N.Inputs) :
  R.v2164 (state s) (inputs i) = Zmod.unsigned (N.v2164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2164 s i)) at 1.
  unfold R.v2164, N.v2164.
  rewrite ?node_2163.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r863_nr_5F863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r863_nr_5F863 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2165 (s : N.State) (i : N.Inputs) :
  R.v2165 (state s) (inputs i) = Zmod.unsigned (N.v2165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2165 s i)) at 1.
  unfold R.v2165, N.v2165.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2166 (s : N.State) (i : N.Inputs) :
  R.v2166 (state s) (inputs i) = Zmod.unsigned (N.v2166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2166 s i)) at 1.
  unfold R.v2166, N.v2166.
  rewrite ?node_2165.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r864_nr_5F864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r864_nr_5F864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2167 (s : N.State) (i : N.Inputs) :
  R.v2167 (state s) (inputs i) = Zmod.unsigned (N.v2167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2167 s i)) at 1.
  unfold R.v2167, N.v2167.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2168 (s : N.State) (i : N.Inputs) :
  R.v2168 (state s) (inputs i) = Zmod.unsigned (N.v2168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2168 s i)) at 1.
  unfold R.v2168, N.v2168.
  rewrite ?node_2167.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r865_nr_5F865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r865_nr_5F865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2169 (s : N.State) (i : N.Inputs) :
  R.v2169 (state s) (inputs i) = Zmod.unsigned (N.v2169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2169 s i)) at 1.
  unfold R.v2169, N.v2169.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2170 (s : N.State) (i : N.Inputs) :
  R.v2170 (state s) (inputs i) = Zmod.unsigned (N.v2170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2170 s i)) at 1.
  unfold R.v2170, N.v2170.
  rewrite ?node_2169.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r866_nr_5F866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r866_nr_5F866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2171 (s : N.State) (i : N.Inputs) :
  R.v2171 (state s) (inputs i) = Zmod.unsigned (N.v2171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2171 s i)) at 1.
  unfold R.v2171, N.v2171.
  rewrite ?node_2112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2172 (s : N.State) (i : N.Inputs) :
  R.v2172 (state s) (inputs i) = Zmod.unsigned (N.v2172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2172 s i)) at 1.
  unfold R.v2172, N.v2172.
  rewrite ?node_2171.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r867_nr_5F867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r867_nr_5F867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2173 (s : N.State) (i : N.Inputs) :
  R.v2173 (state s) (inputs i) = Zmod.unsigned (N.v2173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2173 s i)) at 1.
  unfold R.v2173, N.v2173.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2174 (s : N.State) (i : N.Inputs) :
  R.v2174 (state s) (inputs i) = Zmod.unsigned (N.v2174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2174 s i)) at 1.
  unfold R.v2174, N.v2174.
  rewrite ?node_2173.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r868_nr_5F868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r868_nr_5F868 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2175 (s : N.State) (i : N.Inputs) :
  R.v2175 (state s) (inputs i) = Zmod.unsigned (N.v2175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2175 s i)) at 1.
  unfold R.v2175, N.v2175.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2176 (s : N.State) (i : N.Inputs) :
  R.v2176 (state s) (inputs i) = Zmod.unsigned (N.v2176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2176 s i)) at 1.
  unfold R.v2176, N.v2176.
  rewrite ?node_2175.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r869_nr_5F869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r869_nr_5F869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2177 (s : N.State) (i : N.Inputs) :
  R.v2177 (state s) (inputs i) = Zmod.unsigned (N.v2177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2177 s i)) at 1.
  unfold R.v2177, N.v2177.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2178 (s : N.State) (i : N.Inputs) :
  R.v2178 (state s) (inputs i) = Zmod.unsigned (N.v2178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2178 s i)) at 1.
  unfold R.v2178, N.v2178.
  rewrite ?node_2177.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r870_nr_5F870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r870_nr_5F870 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2179 (s : N.State) (i : N.Inputs) :
  R.v2179 (state s) (inputs i) = Zmod.unsigned (N.v2179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2179 s i)) at 1.
  unfold R.v2179, N.v2179.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2180 (s : N.State) (i : N.Inputs) :
  R.v2180 (state s) (inputs i) = Zmod.unsigned (N.v2180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2180 s i)) at 1.
  unfold R.v2180, N.v2180.
  rewrite ?node_2179.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r871_nr_5F871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r871_nr_5F871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2181 (s : N.State) (i : N.Inputs) :
  R.v2181 (state s) (inputs i) = Zmod.unsigned (N.v2181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2181 s i)) at 1.
  unfold R.v2181, N.v2181.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2182 (s : N.State) (i : N.Inputs) :
  R.v2182 (state s) (inputs i) = Zmod.unsigned (N.v2182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2182 s i)) at 1.
  unfold R.v2182, N.v2182.
  rewrite ?node_2181.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r872_nr_5F872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r872_nr_5F872 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2183 (s : N.State) (i : N.Inputs) :
  R.v2183 (state s) (inputs i) = Zmod.unsigned (N.v2183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2183 s i)) at 1.
  unfold R.v2183, N.v2183.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2184 (s : N.State) (i : N.Inputs) :
  R.v2184 (state s) (inputs i) = Zmod.unsigned (N.v2184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2184 s i)) at 1.
  unfold R.v2184, N.v2184.
  rewrite ?node_2183.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r873_nr_5F873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r873_nr_5F873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2185 (s : N.State) (i : N.Inputs) :
  R.v2185 (state s) (inputs i) = Zmod.unsigned (N.v2185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2185 s i)) at 1.
  unfold R.v2185, N.v2185.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2186 (s : N.State) (i : N.Inputs) :
  R.v2186 (state s) (inputs i) = Zmod.unsigned (N.v2186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2186 s i)) at 1.
  unfold R.v2186, N.v2186.
  rewrite ?node_2185.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r874_nr_5F874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r874_nr_5F874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2187 (s : N.State) (i : N.Inputs) :
  R.v2187 (state s) (inputs i) = Zmod.unsigned (N.v2187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2187 s i)) at 1.
  unfold R.v2187, N.v2187.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2188 (s : N.State) (i : N.Inputs) :
  R.v2188 (state s) (inputs i) = Zmod.unsigned (N.v2188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2188 s i)) at 1.
  unfold R.v2188, N.v2188.
  rewrite ?node_2187.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r875_nr_5F875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r875_nr_5F875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2189 (s : N.State) (i : N.Inputs) :
  R.v2189 (state s) (inputs i) = Zmod.unsigned (N.v2189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2189 s i)) at 1.
  unfold R.v2189, N.v2189.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2190 (s : N.State) (i : N.Inputs) :
  R.v2190 (state s) (inputs i) = Zmod.unsigned (N.v2190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2190 s i)) at 1.
  unfold R.v2190, N.v2190.
  rewrite ?node_2189.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r876_nr_5F876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r876_nr_5F876 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2191 (s : N.State) (i : N.Inputs) :
  R.v2191 (state s) (inputs i) = Zmod.unsigned (N.v2191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2191 s i)) at 1.
  unfold R.v2191, N.v2191.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2192 (s : N.State) (i : N.Inputs) :
  R.v2192 (state s) (inputs i) = Zmod.unsigned (N.v2192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2192 s i)) at 1.
  unfold R.v2192, N.v2192.
  rewrite ?node_2191.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r877_nr_5F877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r877_nr_5F877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2193 (s : N.State) (i : N.Inputs) :
  R.v2193 (state s) (inputs i) = Zmod.unsigned (N.v2193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2193 s i)) at 1.
  unfold R.v2193, N.v2193.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2194 (s : N.State) (i : N.Inputs) :
  R.v2194 (state s) (inputs i) = Zmod.unsigned (N.v2194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2194 s i)) at 1.
  unfold R.v2194, N.v2194.
  rewrite ?node_2193.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r878_nr_5F878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r878_nr_5F878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2195 (s : N.State) (i : N.Inputs) :
  R.v2195 (state s) (inputs i) = Zmod.unsigned (N.v2195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2195 s i)) at 1.
  unfold R.v2195, N.v2195.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2196 (s : N.State) (i : N.Inputs) :
  R.v2196 (state s) (inputs i) = Zmod.unsigned (N.v2196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2196 s i)) at 1.
  unfold R.v2196, N.v2196.
  rewrite ?node_2195.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r879_nr_5F879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r879_nr_5F879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2197 (s : N.State) (i : N.Inputs) :
  R.v2197 (state s) (inputs i) = Zmod.unsigned (N.v2197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2197 s i)) at 1.
  unfold R.v2197, N.v2197.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2198 (s : N.State) (i : N.Inputs) :
  R.v2198 (state s) (inputs i) = Zmod.unsigned (N.v2198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2198 s i)) at 1.
  unfold R.v2198, N.v2198.
  rewrite ?node_2197.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r880_nr_5F880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r880_nr_5F880 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2199 (s : N.State) (i : N.Inputs) :
  R.v2199 (state s) (inputs i) = Zmod.unsigned (N.v2199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2199 s i)) at 1.
  unfold R.v2199, N.v2199.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2200 (s : N.State) (i : N.Inputs) :
  R.v2200 (state s) (inputs i) = Zmod.unsigned (N.v2200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2200 s i)) at 1.
  unfold R.v2200, N.v2200.
  rewrite ?node_2199.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r881_nr_5F881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r881_nr_5F881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2201 (s : N.State) (i : N.Inputs) :
  R.v2201 (state s) (inputs i) = Zmod.unsigned (N.v2201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2201 s i)) at 1.
  unfold R.v2201, N.v2201.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2202 (s : N.State) (i : N.Inputs) :
  R.v2202 (state s) (inputs i) = Zmod.unsigned (N.v2202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2202 s i)) at 1.
  unfold R.v2202, N.v2202.
  rewrite ?node_2201.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r882_nr_5F882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r882_nr_5F882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2203 (s : N.State) (i : N.Inputs) :
  R.v2203 (state s) (inputs i) = Zmod.unsigned (N.v2203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2203 s i)) at 1.
  unfold R.v2203, N.v2203.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2204 (s : N.State) (i : N.Inputs) :
  R.v2204 (state s) (inputs i) = Zmod.unsigned (N.v2204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2204 s i)) at 1.
  unfold R.v2204, N.v2204.
  rewrite ?node_2203.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r883_nr_5F883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r883_nr_5F883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2205 (s : N.State) (i : N.Inputs) :
  R.v2205 (state s) (inputs i) = Zmod.unsigned (N.v2205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2205 s i)) at 1.
  unfold R.v2205, N.v2205.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2206 (s : N.State) (i : N.Inputs) :
  R.v2206 (state s) (inputs i) = Zmod.unsigned (N.v2206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2206 s i)) at 1.
  unfold R.v2206, N.v2206.
  rewrite ?node_2205.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r884_nr_5F884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r884_nr_5F884 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2207 (s : N.State) (i : N.Inputs) :
  R.v2207 (state s) (inputs i) = Zmod.unsigned (N.v2207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2207 s i)) at 1.
  unfold R.v2207, N.v2207.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2208 (s : N.State) (i : N.Inputs) :
  R.v2208 (state s) (inputs i) = Zmod.unsigned (N.v2208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2208 s i)) at 1.
  unfold R.v2208, N.v2208.
  rewrite ?node_2207.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r885_nr_5F885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r885_nr_5F885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2209 (s : N.State) (i : N.Inputs) :
  R.v2209 (state s) (inputs i) = Zmod.unsigned (N.v2209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2209 s i)) at 1.
  unfold R.v2209, N.v2209.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2210 (s : N.State) (i : N.Inputs) :
  R.v2210 (state s) (inputs i) = Zmod.unsigned (N.v2210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2210 s i)) at 1.
  unfold R.v2210, N.v2210.
  rewrite ?node_2209.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r886_nr_5F886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r886_nr_5F886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2211 (s : N.State) (i : N.Inputs) :
  R.v2211 (state s) (inputs i) = Zmod.unsigned (N.v2211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2211 s i)) at 1.
  unfold R.v2211, N.v2211.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2212 (s : N.State) (i : N.Inputs) :
  R.v2212 (state s) (inputs i) = Zmod.unsigned (N.v2212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2212 s i)) at 1.
  unfold R.v2212, N.v2212.
  rewrite ?node_2211.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r887_nr_5F887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r887_nr_5F887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2213 (s : N.State) (i : N.Inputs) :
  R.v2213 (state s) (inputs i) = Zmod.unsigned (N.v2213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2213 s i)) at 1.
  unfold R.v2213, N.v2213.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2214 (s : N.State) (i : N.Inputs) :
  R.v2214 (state s) (inputs i) = Zmod.unsigned (N.v2214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2214 s i)) at 1.
  unfold R.v2214, N.v2214.
  rewrite ?node_2213.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r888_nr_5F888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r888_nr_5F888 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2215 (s : N.State) (i : N.Inputs) :
  R.v2215 (state s) (inputs i) = Zmod.unsigned (N.v2215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2215 s i)) at 1.
  unfold R.v2215, N.v2215.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2216 (s : N.State) (i : N.Inputs) :
  R.v2216 (state s) (inputs i) = Zmod.unsigned (N.v2216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2216 s i)) at 1.
  unfold R.v2216, N.v2216.
  rewrite ?node_2215.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r889_nr_5F889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r889_nr_5F889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2217 (s : N.State) (i : N.Inputs) :
  R.v2217 (state s) (inputs i) = Zmod.unsigned (N.v2217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2217 s i)) at 1.
  unfold R.v2217, N.v2217.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2218 (s : N.State) (i : N.Inputs) :
  R.v2218 (state s) (inputs i) = Zmod.unsigned (N.v2218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2218 s i)) at 1.
  unfold R.v2218, N.v2218.
  rewrite ?node_2217.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r890_nr_5F890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r890_nr_5F890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2219 (s : N.State) (i : N.Inputs) :
  R.v2219 (state s) (inputs i) = Zmod.unsigned (N.v2219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2219 s i)) at 1.
  unfold R.v2219, N.v2219.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2220 (s : N.State) (i : N.Inputs) :
  R.v2220 (state s) (inputs i) = Zmod.unsigned (N.v2220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2220 s i)) at 1.
  unfold R.v2220, N.v2220.
  rewrite ?node_2219.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r891_nr_5F891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r891_nr_5F891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2221 (s : N.State) (i : N.Inputs) :
  R.v2221 (state s) (inputs i) = Zmod.unsigned (N.v2221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2221 s i)) at 1.
  unfold R.v2221, N.v2221.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2222 (s : N.State) (i : N.Inputs) :
  R.v2222 (state s) (inputs i) = Zmod.unsigned (N.v2222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2222 s i)) at 1.
  unfold R.v2222, N.v2222.
  rewrite ?node_2221.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r892_nr_5F892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r892_nr_5F892 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2223 (s : N.State) (i : N.Inputs) :
  R.v2223 (state s) (inputs i) = Zmod.unsigned (N.v2223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2223 s i)) at 1.
  unfold R.v2223, N.v2223.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2224 (s : N.State) (i : N.Inputs) :
  R.v2224 (state s) (inputs i) = Zmod.unsigned (N.v2224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2224 s i)) at 1.
  unfold R.v2224, N.v2224.
  rewrite ?node_2223.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r893_nr_5F893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r893_nr_5F893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2225 (s : N.State) (i : N.Inputs) :
  R.v2225 (state s) (inputs i) = Zmod.unsigned (N.v2225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2225 s i)) at 1.
  unfold R.v2225, N.v2225.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2226 (s : N.State) (i : N.Inputs) :
  R.v2226 (state s) (inputs i) = Zmod.unsigned (N.v2226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2226 s i)) at 1.
  unfold R.v2226, N.v2226.
  rewrite ?node_2225.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r894_nr_5F894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r894_nr_5F894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2227 (s : N.State) (i : N.Inputs) :
  R.v2227 (state s) (inputs i) = Zmod.unsigned (N.v2227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2227 s i)) at 1.
  unfold R.v2227, N.v2227.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2228 (s : N.State) (i : N.Inputs) :
  R.v2228 (state s) (inputs i) = Zmod.unsigned (N.v2228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2228 s i)) at 1.
  unfold R.v2228, N.v2228.
  rewrite ?node_2227.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r895_nr_5F895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r895_nr_5F895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2229 (s : N.State) (i : N.Inputs) :
  R.v2229 (state s) (inputs i) = Zmod.unsigned (N.v2229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2229 s i)) at 1.
  unfold R.v2229, N.v2229.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2230 (s : N.State) (i : N.Inputs) :
  R.v2230 (state s) (inputs i) = Zmod.unsigned (N.v2230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2230 s i)) at 1.
  unfold R.v2230, N.v2230.
  unfold R.v33, N.v33.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2231 (s : N.State) (i : N.Inputs) :
  R.v2231 (state s) (inputs i) = Zmod.unsigned (N.v2231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2231 s i)) at 1.
  unfold R.v2231, N.v2231.
  unfold R.v35, N.v35.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2232 (s : N.State) (i : N.Inputs) :
  R.v2232 (state s) (inputs i) = Zmod.unsigned (N.v2232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2232 s i)) at 1.
  unfold R.v2232, N.v2232.
  rewrite ?node_2230.
  rewrite ?node_2231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2233 (s : N.State) (i : N.Inputs) :
  R.v2233 (state s) (inputs i) = Zmod.unsigned (N.v2233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2233 s i)) at 1.
  unfold R.v2233, N.v2233.
  unfold R.v39, N.v39.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2234 (s : N.State) (i : N.Inputs) :
  R.v2234 (state s) (inputs i) = Zmod.unsigned (N.v2234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2234 s i)) at 1.
  unfold R.v2234, N.v2234.
  unfold R.v42, N.v42.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2235 (s : N.State) (i : N.Inputs) :
  R.v2235 (state s) (inputs i) = Zmod.unsigned (N.v2235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2235 s i)) at 1.
  unfold R.v2235, N.v2235.
  unfold R.v45, N.v45.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2236 (s : N.State) (i : N.Inputs) :
  R.v2236 (state s) (inputs i) = Zmod.unsigned (N.v2236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2236 s i)) at 1.
  unfold R.v2236, N.v2236.
  unfold R.v47, N.v47.
  rewrite ?node_2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2237 (s : N.State) (i : N.Inputs) :
  R.v2237 (state s) (inputs i) = Zmod.unsigned (N.v2237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2237 s i)) at 1.
  unfold R.v2237, N.v2237.
  rewrite ?node_2235.
  rewrite ?node_2236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2238 (s : N.State) (i : N.Inputs) :
  R.v2238 (state s) (inputs i) = Zmod.unsigned (N.v2238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2238 s i)) at 1.
  unfold R.v2238, N.v2238.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2239 (s : N.State) (i : N.Inputs) :
  R.v2239 (state s) (inputs i) = Zmod.unsigned (N.v2239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2239 s i)) at 1.
  unfold R.v2239, N.v2239.
  rewrite ?node_44.
  rewrite ?node_2234.
  rewrite ?node_2238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2240 (s : N.State) (i : N.Inputs) :
  R.v2240 (state s) (inputs i) = Zmod.unsigned (N.v2240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2240 s i)) at 1.
  unfold R.v2240, N.v2240.
  rewrite ?node_41.
  rewrite ?node_2233.
  rewrite ?node_2239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2241 (s : N.State) (i : N.Inputs) :
  R.v2241 (state s) (inputs i) = Zmod.unsigned (N.v2241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2241 s i)) at 1.
  unfold R.v2241, N.v2241.
  rewrite ?node_38.
  rewrite ?node_2232.
  rewrite ?node_2240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2242 (s : N.State) (i : N.Inputs) :
  R.v2242 (state s) (inputs i) = Zmod.unsigned (N.v2242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2242 s i)) at 1.
  unfold R.v2242, N.v2242.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2243 (s : N.State) (i : N.Inputs) :
  R.v2243 (state s) (inputs i) = Zmod.unsigned (N.v2243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2243 s i)) at 1.
  unfold R.v2243, N.v2243.
  rewrite ?node_2242.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r896_nr_5F896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r896_nr_5F896 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2244 (s : N.State) (i : N.Inputs) :
  R.v2244 (state s) (inputs i) = Zmod.unsigned (N.v2244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2244 s i)) at 1.
  unfold R.v2244, N.v2244.
  unfold R.v6, N.v6.
  rewrite ?node_2233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2245 (s : N.State) (i : N.Inputs) :
  R.v2245 (state s) (inputs i) = Zmod.unsigned (N.v2245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2245 s i)) at 1.
  unfold R.v2245, N.v2245.
  unfold R.v19, N.v19.
  rewrite ?node_2232.
  rewrite ?node_2244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2246 (s : N.State) (i : N.Inputs) :
  R.v2246 (state s) (inputs i) = Zmod.unsigned (N.v2246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2246 s i)) at 1.
  unfold R.v2246, N.v2246.
  rewrite ?node_2245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2247 (s : N.State) (i : N.Inputs) :
  R.v2247 (state s) (inputs i) = Zmod.unsigned (N.v2247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2247 s i)) at 1.
  unfold R.v2247, N.v2247.
  rewrite ?node_2246.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r897_nr_5F897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r897_nr_5F897 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2248 (s : N.State) (i : N.Inputs) :
  R.v2248 (state s) (inputs i) = Zmod.unsigned (N.v2248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2248 s i)) at 1.
  unfold R.v2248, N.v2248.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2249 (s : N.State) (i : N.Inputs) :
  R.v2249 (state s) (inputs i) = Zmod.unsigned (N.v2249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2249 s i)) at 1.
  unfold R.v2249, N.v2249.
  rewrite ?node_2248.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r898_nr_5F898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r898_nr_5F898 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2250 (s : N.State) (i : N.Inputs) :
  R.v2250 (state s) (inputs i) = Zmod.unsigned (N.v2250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2250 s i)) at 1.
  unfold R.v2250, N.v2250.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2251 (s : N.State) (i : N.Inputs) :
  R.v2251 (state s) (inputs i) = Zmod.unsigned (N.v2251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2251 s i)) at 1.
  unfold R.v2251, N.v2251.
  rewrite ?node_2250.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r899_nr_5F899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r899_nr_5F899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2252 (s : N.State) (i : N.Inputs) :
  R.v2252 (state s) (inputs i) = Zmod.unsigned (N.v2252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2252 s i)) at 1.
  unfold R.v2252, N.v2252.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2253 (s : N.State) (i : N.Inputs) :
  R.v2253 (state s) (inputs i) = Zmod.unsigned (N.v2253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2253 s i)) at 1.
  unfold R.v2253, N.v2253.
  rewrite ?node_2252.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r900_nr_5F900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r900_nr_5F900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2254 (s : N.State) (i : N.Inputs) :
  R.v2254 (state s) (inputs i) = Zmod.unsigned (N.v2254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2254 s i)) at 1.
  unfold R.v2254, N.v2254.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2255 (s : N.State) (i : N.Inputs) :
  R.v2255 (state s) (inputs i) = Zmod.unsigned (N.v2255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2255 s i)) at 1.
  unfold R.v2255, N.v2255.
  rewrite ?node_2254.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r901_nr_5F901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r901_nr_5F901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2256 (s : N.State) (i : N.Inputs) :
  R.v2256 (state s) (inputs i) = Zmod.unsigned (N.v2256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2256 s i)) at 1.
  unfold R.v2256, N.v2256.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2257 (s : N.State) (i : N.Inputs) :
  R.v2257 (state s) (inputs i) = Zmod.unsigned (N.v2257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2257 s i)) at 1.
  unfold R.v2257, N.v2257.
  rewrite ?node_2256.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r902_nr_5F902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r902_nr_5F902 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2258 (s : N.State) (i : N.Inputs) :
  R.v2258 (state s) (inputs i) = Zmod.unsigned (N.v2258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2258 s i)) at 1.
  unfold R.v2258, N.v2258.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2259 (s : N.State) (i : N.Inputs) :
  R.v2259 (state s) (inputs i) = Zmod.unsigned (N.v2259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2259 s i)) at 1.
  unfold R.v2259, N.v2259.
  rewrite ?node_2258.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r903_nr_5F903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r903_nr_5F903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2260 (s : N.State) (i : N.Inputs) :
  R.v2260 (state s) (inputs i) = Zmod.unsigned (N.v2260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2260 s i)) at 1.
  unfold R.v2260, N.v2260.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2261 (s : N.State) (i : N.Inputs) :
  R.v2261 (state s) (inputs i) = Zmod.unsigned (N.v2261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2261 s i)) at 1.
  unfold R.v2261, N.v2261.
  rewrite ?node_2260.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r904_nr_5F904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r904_nr_5F904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2262 (s : N.State) (i : N.Inputs) :
  R.v2262 (state s) (inputs i) = Zmod.unsigned (N.v2262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2262 s i)) at 1.
  unfold R.v2262, N.v2262.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2263 (s : N.State) (i : N.Inputs) :
  R.v2263 (state s) (inputs i) = Zmod.unsigned (N.v2263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2263 s i)) at 1.
  unfold R.v2263, N.v2263.
  rewrite ?node_2262.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r905_nr_5F905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r905_nr_5F905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2264 (s : N.State) (i : N.Inputs) :
  R.v2264 (state s) (inputs i) = Zmod.unsigned (N.v2264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2264 s i)) at 1.
  unfold R.v2264, N.v2264.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2265 (s : N.State) (i : N.Inputs) :
  R.v2265 (state s) (inputs i) = Zmod.unsigned (N.v2265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2265 s i)) at 1.
  unfold R.v2265, N.v2265.
  rewrite ?node_2264.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r906_nr_5F906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r906_nr_5F906 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2266 (s : N.State) (i : N.Inputs) :
  R.v2266 (state s) (inputs i) = Zmod.unsigned (N.v2266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2266 s i)) at 1.
  unfold R.v2266, N.v2266.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2267 (s : N.State) (i : N.Inputs) :
  R.v2267 (state s) (inputs i) = Zmod.unsigned (N.v2267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2267 s i)) at 1.
  unfold R.v2267, N.v2267.
  rewrite ?node_2266.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r907_nr_5F907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r907_nr_5F907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2268 (s : N.State) (i : N.Inputs) :
  R.v2268 (state s) (inputs i) = Zmod.unsigned (N.v2268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2268 s i)) at 1.
  unfold R.v2268, N.v2268.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2269 (s : N.State) (i : N.Inputs) :
  R.v2269 (state s) (inputs i) = Zmod.unsigned (N.v2269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2269 s i)) at 1.
  unfold R.v2269, N.v2269.
  rewrite ?node_2268.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r908_nr_5F908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r908_nr_5F908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2270 (s : N.State) (i : N.Inputs) :
  R.v2270 (state s) (inputs i) = Zmod.unsigned (N.v2270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2270 s i)) at 1.
  unfold R.v2270, N.v2270.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2271 (s : N.State) (i : N.Inputs) :
  R.v2271 (state s) (inputs i) = Zmod.unsigned (N.v2271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2271 s i)) at 1.
  unfold R.v2271, N.v2271.
  rewrite ?node_2270.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r909_nr_5F909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r909_nr_5F909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2272 (s : N.State) (i : N.Inputs) :
  R.v2272 (state s) (inputs i) = Zmod.unsigned (N.v2272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2272 s i)) at 1.
  unfold R.v2272, N.v2272.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2273 (s : N.State) (i : N.Inputs) :
  R.v2273 (state s) (inputs i) = Zmod.unsigned (N.v2273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2273 s i)) at 1.
  unfold R.v2273, N.v2273.
  rewrite ?node_2272.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r910_nr_5F910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r910_nr_5F910 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2274 (s : N.State) (i : N.Inputs) :
  R.v2274 (state s) (inputs i) = Zmod.unsigned (N.v2274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2274 s i)) at 1.
  unfold R.v2274, N.v2274.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2275 (s : N.State) (i : N.Inputs) :
  R.v2275 (state s) (inputs i) = Zmod.unsigned (N.v2275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2275 s i)) at 1.
  unfold R.v2275, N.v2275.
  rewrite ?node_2274.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r911_nr_5F911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r911_nr_5F911 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2276 (s : N.State) (i : N.Inputs) :
  R.v2276 (state s) (inputs i) = Zmod.unsigned (N.v2276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2276 s i)) at 1.
  unfold R.v2276, N.v2276.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2277 (s : N.State) (i : N.Inputs) :
  R.v2277 (state s) (inputs i) = Zmod.unsigned (N.v2277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2277 s i)) at 1.
  unfold R.v2277, N.v2277.
  rewrite ?node_2276.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r912_nr_5F912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r912_nr_5F912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2278 (s : N.State) (i : N.Inputs) :
  R.v2278 (state s) (inputs i) = Zmod.unsigned (N.v2278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2278 s i)) at 1.
  unfold R.v2278, N.v2278.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2279 (s : N.State) (i : N.Inputs) :
  R.v2279 (state s) (inputs i) = Zmod.unsigned (N.v2279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2279 s i)) at 1.
  unfold R.v2279, N.v2279.
  rewrite ?node_2278.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r913_nr_5F913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r913_nr_5F913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2280 (s : N.State) (i : N.Inputs) :
  R.v2280 (state s) (inputs i) = Zmod.unsigned (N.v2280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2280 s i)) at 1.
  unfold R.v2280, N.v2280.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2281 (s : N.State) (i : N.Inputs) :
  R.v2281 (state s) (inputs i) = Zmod.unsigned (N.v2281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2281 s i)) at 1.
  unfold R.v2281, N.v2281.
  rewrite ?node_2280.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r914_nr_5F914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r914_nr_5F914 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2282 (s : N.State) (i : N.Inputs) :
  R.v2282 (state s) (inputs i) = Zmod.unsigned (N.v2282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2282 s i)) at 1.
  unfold R.v2282, N.v2282.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2283 (s : N.State) (i : N.Inputs) :
  R.v2283 (state s) (inputs i) = Zmod.unsigned (N.v2283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2283 s i)) at 1.
  unfold R.v2283, N.v2283.
  rewrite ?node_2282.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r915_nr_5F915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r915_nr_5F915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2284 (s : N.State) (i : N.Inputs) :
  R.v2284 (state s) (inputs i) = Zmod.unsigned (N.v2284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2284 s i)) at 1.
  unfold R.v2284, N.v2284.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2285 (s : N.State) (i : N.Inputs) :
  R.v2285 (state s) (inputs i) = Zmod.unsigned (N.v2285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2285 s i)) at 1.
  unfold R.v2285, N.v2285.
  rewrite ?node_2284.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r916_nr_5F916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r916_nr_5F916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2286 (s : N.State) (i : N.Inputs) :
  R.v2286 (state s) (inputs i) = Zmod.unsigned (N.v2286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2286 s i)) at 1.
  unfold R.v2286, N.v2286.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2287 (s : N.State) (i : N.Inputs) :
  R.v2287 (state s) (inputs i) = Zmod.unsigned (N.v2287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2287 s i)) at 1.
  unfold R.v2287, N.v2287.
  rewrite ?node_2286.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r917_nr_5F917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r917_nr_5F917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2288 (s : N.State) (i : N.Inputs) :
  R.v2288 (state s) (inputs i) = Zmod.unsigned (N.v2288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2288 s i)) at 1.
  unfold R.v2288, N.v2288.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2289 (s : N.State) (i : N.Inputs) :
  R.v2289 (state s) (inputs i) = Zmod.unsigned (N.v2289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2289 s i)) at 1.
  unfold R.v2289, N.v2289.
  rewrite ?node_2288.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r918_nr_5F918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r918_nr_5F918 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2290 (s : N.State) (i : N.Inputs) :
  R.v2290 (state s) (inputs i) = Zmod.unsigned (N.v2290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2290 s i)) at 1.
  unfold R.v2290, N.v2290.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2291 (s : N.State) (i : N.Inputs) :
  R.v2291 (state s) (inputs i) = Zmod.unsigned (N.v2291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2291 s i)) at 1.
  unfold R.v2291, N.v2291.
  rewrite ?node_2290.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r919_nr_5F919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r919_nr_5F919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2292 (s : N.State) (i : N.Inputs) :
  R.v2292 (state s) (inputs i) = Zmod.unsigned (N.v2292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2292 s i)) at 1.
  unfold R.v2292, N.v2292.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2293 (s : N.State) (i : N.Inputs) :
  R.v2293 (state s) (inputs i) = Zmod.unsigned (N.v2293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2293 s i)) at 1.
  unfold R.v2293, N.v2293.
  rewrite ?node_2292.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r920_nr_5F920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r920_nr_5F920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2294 (s : N.State) (i : N.Inputs) :
  R.v2294 (state s) (inputs i) = Zmod.unsigned (N.v2294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2294 s i)) at 1.
  unfold R.v2294, N.v2294.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2295 (s : N.State) (i : N.Inputs) :
  R.v2295 (state s) (inputs i) = Zmod.unsigned (N.v2295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2295 s i)) at 1.
  unfold R.v2295, N.v2295.
  rewrite ?node_2294.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r921_nr_5F921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r921_nr_5F921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2296 (s : N.State) (i : N.Inputs) :
  R.v2296 (state s) (inputs i) = Zmod.unsigned (N.v2296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2296 s i)) at 1.
  unfold R.v2296, N.v2296.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2297 (s : N.State) (i : N.Inputs) :
  R.v2297 (state s) (inputs i) = Zmod.unsigned (N.v2297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2297 s i)) at 1.
  unfold R.v2297, N.v2297.
  rewrite ?node_2296.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r922_nr_5F922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r922_nr_5F922 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2298 (s : N.State) (i : N.Inputs) :
  R.v2298 (state s) (inputs i) = Zmod.unsigned (N.v2298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2298 s i)) at 1.
  unfold R.v2298, N.v2298.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2299 (s : N.State) (i : N.Inputs) :
  R.v2299 (state s) (inputs i) = Zmod.unsigned (N.v2299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2299 s i)) at 1.
  unfold R.v2299, N.v2299.
  rewrite ?node_2298.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r923_nr_5F923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r923_nr_5F923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2300 (s : N.State) (i : N.Inputs) :
  R.v2300 (state s) (inputs i) = Zmod.unsigned (N.v2300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2300 s i)) at 1.
  unfold R.v2300, N.v2300.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2301 (s : N.State) (i : N.Inputs) :
  R.v2301 (state s) (inputs i) = Zmod.unsigned (N.v2301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2301 s i)) at 1.
  unfold R.v2301, N.v2301.
  rewrite ?node_2300.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r924_nr_5F924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r924_nr_5F924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2302 (s : N.State) (i : N.Inputs) :
  R.v2302 (state s) (inputs i) = Zmod.unsigned (N.v2302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2302 s i)) at 1.
  unfold R.v2302, N.v2302.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2303 (s : N.State) (i : N.Inputs) :
  R.v2303 (state s) (inputs i) = Zmod.unsigned (N.v2303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2303 s i)) at 1.
  unfold R.v2303, N.v2303.
  rewrite ?node_2302.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r925_nr_5F925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r925_nr_5F925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2304 (s : N.State) (i : N.Inputs) :
  R.v2304 (state s) (inputs i) = Zmod.unsigned (N.v2304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2304 s i)) at 1.
  unfold R.v2304, N.v2304.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2305 (s : N.State) (i : N.Inputs) :
  R.v2305 (state s) (inputs i) = Zmod.unsigned (N.v2305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2305 s i)) at 1.
  unfold R.v2305, N.v2305.
  rewrite ?node_2304.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r926_nr_5F926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r926_nr_5F926 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2306 (s : N.State) (i : N.Inputs) :
  R.v2306 (state s) (inputs i) = Zmod.unsigned (N.v2306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2306 s i)) at 1.
  unfold R.v2306, N.v2306.
  rewrite ?node_2245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2307 (s : N.State) (i : N.Inputs) :
  R.v2307 (state s) (inputs i) = Zmod.unsigned (N.v2307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2307 s i)) at 1.
  unfold R.v2307, N.v2307.
  rewrite ?node_2306.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r927_nr_5F927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r927_nr_5F927 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2308 (s : N.State) (i : N.Inputs) :
  R.v2308 (state s) (inputs i) = Zmod.unsigned (N.v2308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2308 s i)) at 1.
  unfold R.v2308, N.v2308.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2309 (s : N.State) (i : N.Inputs) :
  R.v2309 (state s) (inputs i) = Zmod.unsigned (N.v2309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2309 s i)) at 1.
  unfold R.v2309, N.v2309.
  rewrite ?node_2308.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r928_nr_5F928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r928_nr_5F928 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2310 (s : N.State) (i : N.Inputs) :
  R.v2310 (state s) (inputs i) = Zmod.unsigned (N.v2310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2310 s i)) at 1.
  unfold R.v2310, N.v2310.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2311 (s : N.State) (i : N.Inputs) :
  R.v2311 (state s) (inputs i) = Zmod.unsigned (N.v2311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2311 s i)) at 1.
  unfold R.v2311, N.v2311.
  rewrite ?node_2310.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r929_nr_5F929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r929_nr_5F929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2312 (s : N.State) (i : N.Inputs) :
  R.v2312 (state s) (inputs i) = Zmod.unsigned (N.v2312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2312 s i)) at 1.
  unfold R.v2312, N.v2312.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2313 (s : N.State) (i : N.Inputs) :
  R.v2313 (state s) (inputs i) = Zmod.unsigned (N.v2313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2313 s i)) at 1.
  unfold R.v2313, N.v2313.
  rewrite ?node_2312.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r930_nr_5F930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r930_nr_5F930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2314 (s : N.State) (i : N.Inputs) :
  R.v2314 (state s) (inputs i) = Zmod.unsigned (N.v2314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2314 s i)) at 1.
  unfold R.v2314, N.v2314.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2315 (s : N.State) (i : N.Inputs) :
  R.v2315 (state s) (inputs i) = Zmod.unsigned (N.v2315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2315 s i)) at 1.
  unfold R.v2315, N.v2315.
  rewrite ?node_2314.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r931_nr_5F931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r931_nr_5F931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2316 (s : N.State) (i : N.Inputs) :
  R.v2316 (state s) (inputs i) = Zmod.unsigned (N.v2316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2316 s i)) at 1.
  unfold R.v2316, N.v2316.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2317 (s : N.State) (i : N.Inputs) :
  R.v2317 (state s) (inputs i) = Zmod.unsigned (N.v2317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2317 s i)) at 1.
  unfold R.v2317, N.v2317.
  rewrite ?node_2316.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r932_nr_5F932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r932_nr_5F932 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2318 (s : N.State) (i : N.Inputs) :
  R.v2318 (state s) (inputs i) = Zmod.unsigned (N.v2318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2318 s i)) at 1.
  unfold R.v2318, N.v2318.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2319 (s : N.State) (i : N.Inputs) :
  R.v2319 (state s) (inputs i) = Zmod.unsigned (N.v2319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2319 s i)) at 1.
  unfold R.v2319, N.v2319.
  rewrite ?node_2318.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r933_nr_5F933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r933_nr_5F933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2320 (s : N.State) (i : N.Inputs) :
  R.v2320 (state s) (inputs i) = Zmod.unsigned (N.v2320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2320 s i)) at 1.
  unfold R.v2320, N.v2320.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2321 (s : N.State) (i : N.Inputs) :
  R.v2321 (state s) (inputs i) = Zmod.unsigned (N.v2321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2321 s i)) at 1.
  unfold R.v2321, N.v2321.
  rewrite ?node_2320.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r934_nr_5F934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r934_nr_5F934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2322 (s : N.State) (i : N.Inputs) :
  R.v2322 (state s) (inputs i) = Zmod.unsigned (N.v2322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2322 s i)) at 1.
  unfold R.v2322, N.v2322.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2323 (s : N.State) (i : N.Inputs) :
  R.v2323 (state s) (inputs i) = Zmod.unsigned (N.v2323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2323 s i)) at 1.
  unfold R.v2323, N.v2323.
  rewrite ?node_2322.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r935_nr_5F935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r935_nr_5F935 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2324 (s : N.State) (i : N.Inputs) :
  R.v2324 (state s) (inputs i) = Zmod.unsigned (N.v2324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2324 s i)) at 1.
  unfold R.v2324, N.v2324.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2325 (s : N.State) (i : N.Inputs) :
  R.v2325 (state s) (inputs i) = Zmod.unsigned (N.v2325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2325 s i)) at 1.
  unfold R.v2325, N.v2325.
  rewrite ?node_2324.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r936_nr_5F936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r936_nr_5F936 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2326 (s : N.State) (i : N.Inputs) :
  R.v2326 (state s) (inputs i) = Zmod.unsigned (N.v2326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2326 s i)) at 1.
  unfold R.v2326, N.v2326.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2327 (s : N.State) (i : N.Inputs) :
  R.v2327 (state s) (inputs i) = Zmod.unsigned (N.v2327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2327 s i)) at 1.
  unfold R.v2327, N.v2327.
  rewrite ?node_2326.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r937_nr_5F937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r937_nr_5F937 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2328 (s : N.State) (i : N.Inputs) :
  R.v2328 (state s) (inputs i) = Zmod.unsigned (N.v2328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2328 s i)) at 1.
  unfold R.v2328, N.v2328.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2329 (s : N.State) (i : N.Inputs) :
  R.v2329 (state s) (inputs i) = Zmod.unsigned (N.v2329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2329 s i)) at 1.
  unfold R.v2329, N.v2329.
  rewrite ?node_2328.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r938_nr_5F938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r938_nr_5F938 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2330 (s : N.State) (i : N.Inputs) :
  R.v2330 (state s) (inputs i) = Zmod.unsigned (N.v2330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2330 s i)) at 1.
  unfold R.v2330, N.v2330.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2331 (s : N.State) (i : N.Inputs) :
  R.v2331 (state s) (inputs i) = Zmod.unsigned (N.v2331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2331 s i)) at 1.
  unfold R.v2331, N.v2331.
  rewrite ?node_2330.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r939_nr_5F939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r939_nr_5F939 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2332 (s : N.State) (i : N.Inputs) :
  R.v2332 (state s) (inputs i) = Zmod.unsigned (N.v2332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2332 s i)) at 1.
  unfold R.v2332, N.v2332.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2333 (s : N.State) (i : N.Inputs) :
  R.v2333 (state s) (inputs i) = Zmod.unsigned (N.v2333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2333 s i)) at 1.
  unfold R.v2333, N.v2333.
  rewrite ?node_2332.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r940_nr_5F940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r940_nr_5F940 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2334 (s : N.State) (i : N.Inputs) :
  R.v2334 (state s) (inputs i) = Zmod.unsigned (N.v2334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2334 s i)) at 1.
  unfold R.v2334, N.v2334.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2335 (s : N.State) (i : N.Inputs) :
  R.v2335 (state s) (inputs i) = Zmod.unsigned (N.v2335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2335 s i)) at 1.
  unfold R.v2335, N.v2335.
  rewrite ?node_2334.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r941_nr_5F941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r941_nr_5F941 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2336 (s : N.State) (i : N.Inputs) :
  R.v2336 (state s) (inputs i) = Zmod.unsigned (N.v2336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2336 s i)) at 1.
  unfold R.v2336, N.v2336.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2337 (s : N.State) (i : N.Inputs) :
  R.v2337 (state s) (inputs i) = Zmod.unsigned (N.v2337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2337 s i)) at 1.
  unfold R.v2337, N.v2337.
  rewrite ?node_2336.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r942_nr_5F942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r942_nr_5F942 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2338 (s : N.State) (i : N.Inputs) :
  R.v2338 (state s) (inputs i) = Zmod.unsigned (N.v2338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2338 s i)) at 1.
  unfold R.v2338, N.v2338.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2339 (s : N.State) (i : N.Inputs) :
  R.v2339 (state s) (inputs i) = Zmod.unsigned (N.v2339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2339 s i)) at 1.
  unfold R.v2339, N.v2339.
  rewrite ?node_2338.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r943_nr_5F943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r943_nr_5F943 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2340 (s : N.State) (i : N.Inputs) :
  R.v2340 (state s) (inputs i) = Zmod.unsigned (N.v2340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2340 s i)) at 1.
  unfold R.v2340, N.v2340.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2341 (s : N.State) (i : N.Inputs) :
  R.v2341 (state s) (inputs i) = Zmod.unsigned (N.v2341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2341 s i)) at 1.
  unfold R.v2341, N.v2341.
  rewrite ?node_2340.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r944_nr_5F944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r944_nr_5F944 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2342 (s : N.State) (i : N.Inputs) :
  R.v2342 (state s) (inputs i) = Zmod.unsigned (N.v2342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2342 s i)) at 1.
  unfold R.v2342, N.v2342.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2343 (s : N.State) (i : N.Inputs) :
  R.v2343 (state s) (inputs i) = Zmod.unsigned (N.v2343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2343 s i)) at 1.
  unfold R.v2343, N.v2343.
  rewrite ?node_2342.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r945_nr_5F945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r945_nr_5F945 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2344 (s : N.State) (i : N.Inputs) :
  R.v2344 (state s) (inputs i) = Zmod.unsigned (N.v2344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2344 s i)) at 1.
  unfold R.v2344, N.v2344.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2345 (s : N.State) (i : N.Inputs) :
  R.v2345 (state s) (inputs i) = Zmod.unsigned (N.v2345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2345 s i)) at 1.
  unfold R.v2345, N.v2345.
  rewrite ?node_2344.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r946_nr_5F946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r946_nr_5F946 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2346 (s : N.State) (i : N.Inputs) :
  R.v2346 (state s) (inputs i) = Zmod.unsigned (N.v2346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2346 s i)) at 1.
  unfold R.v2346, N.v2346.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2347 (s : N.State) (i : N.Inputs) :
  R.v2347 (state s) (inputs i) = Zmod.unsigned (N.v2347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2347 s i)) at 1.
  unfold R.v2347, N.v2347.
  rewrite ?node_2346.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r947_nr_5F947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r947_nr_5F947 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2348 (s : N.State) (i : N.Inputs) :
  R.v2348 (state s) (inputs i) = Zmod.unsigned (N.v2348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2348 s i)) at 1.
  unfold R.v2348, N.v2348.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2349 (s : N.State) (i : N.Inputs) :
  R.v2349 (state s) (inputs i) = Zmod.unsigned (N.v2349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2349 s i)) at 1.
  unfold R.v2349, N.v2349.
  rewrite ?node_2348.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r948_nr_5F948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r948_nr_5F948 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2350 (s : N.State) (i : N.Inputs) :
  R.v2350 (state s) (inputs i) = Zmod.unsigned (N.v2350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2350 s i)) at 1.
  unfold R.v2350, N.v2350.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2351 (s : N.State) (i : N.Inputs) :
  R.v2351 (state s) (inputs i) = Zmod.unsigned (N.v2351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2351 s i)) at 1.
  unfold R.v2351, N.v2351.
  rewrite ?node_2350.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r949_nr_5F949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r949_nr_5F949 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2352 (s : N.State) (i : N.Inputs) :
  R.v2352 (state s) (inputs i) = Zmod.unsigned (N.v2352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2352 s i)) at 1.
  unfold R.v2352, N.v2352.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2353 (s : N.State) (i : N.Inputs) :
  R.v2353 (state s) (inputs i) = Zmod.unsigned (N.v2353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2353 s i)) at 1.
  unfold R.v2353, N.v2353.
  rewrite ?node_2352.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r950_nr_5F950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r950_nr_5F950 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2354 (s : N.State) (i : N.Inputs) :
  R.v2354 (state s) (inputs i) = Zmod.unsigned (N.v2354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2354 s i)) at 1.
  unfold R.v2354, N.v2354.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2355 (s : N.State) (i : N.Inputs) :
  R.v2355 (state s) (inputs i) = Zmod.unsigned (N.v2355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2355 s i)) at 1.
  unfold R.v2355, N.v2355.
  rewrite ?node_2354.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r951_nr_5F951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r951_nr_5F951 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2356 (s : N.State) (i : N.Inputs) :
  R.v2356 (state s) (inputs i) = Zmod.unsigned (N.v2356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2356 s i)) at 1.
  unfold R.v2356, N.v2356.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2357 (s : N.State) (i : N.Inputs) :
  R.v2357 (state s) (inputs i) = Zmod.unsigned (N.v2357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2357 s i)) at 1.
  unfold R.v2357, N.v2357.
  rewrite ?node_2356.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r952_nr_5F952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r952_nr_5F952 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2358 (s : N.State) (i : N.Inputs) :
  R.v2358 (state s) (inputs i) = Zmod.unsigned (N.v2358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2358 s i)) at 1.
  unfold R.v2358, N.v2358.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2359 (s : N.State) (i : N.Inputs) :
  R.v2359 (state s) (inputs i) = Zmod.unsigned (N.v2359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2359 s i)) at 1.
  unfold R.v2359, N.v2359.
  rewrite ?node_2358.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r953_nr_5F953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r953_nr_5F953 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2360 (s : N.State) (i : N.Inputs) :
  R.v2360 (state s) (inputs i) = Zmod.unsigned (N.v2360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2360 s i)) at 1.
  unfold R.v2360, N.v2360.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2361 (s : N.State) (i : N.Inputs) :
  R.v2361 (state s) (inputs i) = Zmod.unsigned (N.v2361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2361 s i)) at 1.
  unfold R.v2361, N.v2361.
  rewrite ?node_2360.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r954_nr_5F954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r954_nr_5F954 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2362 (s : N.State) (i : N.Inputs) :
  R.v2362 (state s) (inputs i) = Zmod.unsigned (N.v2362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2362 s i)) at 1.
  unfold R.v2362, N.v2362.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2363 (s : N.State) (i : N.Inputs) :
  R.v2363 (state s) (inputs i) = Zmod.unsigned (N.v2363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2363 s i)) at 1.
  unfold R.v2363, N.v2363.
  rewrite ?node_2362.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r955_nr_5F955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r955_nr_5F955 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2364 (s : N.State) (i : N.Inputs) :
  R.v2364 (state s) (inputs i) = Zmod.unsigned (N.v2364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2364 s i)) at 1.
  unfold R.v2364, N.v2364.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2365 (s : N.State) (i : N.Inputs) :
  R.v2365 (state s) (inputs i) = Zmod.unsigned (N.v2365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2365 s i)) at 1.
  unfold R.v2365, N.v2365.
  rewrite ?node_2364.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r956_nr_5F956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r956_nr_5F956 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2366 (s : N.State) (i : N.Inputs) :
  R.v2366 (state s) (inputs i) = Zmod.unsigned (N.v2366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2366 s i)) at 1.
  unfold R.v2366, N.v2366.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2367 (s : N.State) (i : N.Inputs) :
  R.v2367 (state s) (inputs i) = Zmod.unsigned (N.v2367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2367 s i)) at 1.
  unfold R.v2367, N.v2367.
  unfold R.v33, N.v33.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2368 (s : N.State) (i : N.Inputs) :
  R.v2368 (state s) (inputs i) = Zmod.unsigned (N.v2368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2368 s i)) at 1.
  unfold R.v2368, N.v2368.
  unfold R.v35, N.v35.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2369 (s : N.State) (i : N.Inputs) :
  R.v2369 (state s) (inputs i) = Zmod.unsigned (N.v2369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2369 s i)) at 1.
  unfold R.v2369, N.v2369.
  rewrite ?node_2367.
  rewrite ?node_2368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2370 (s : N.State) (i : N.Inputs) :
  R.v2370 (state s) (inputs i) = Zmod.unsigned (N.v2370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2370 s i)) at 1.
  unfold R.v2370, N.v2370.
  unfold R.v39, N.v39.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2371 (s : N.State) (i : N.Inputs) :
  R.v2371 (state s) (inputs i) = Zmod.unsigned (N.v2371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2371 s i)) at 1.
  unfold R.v2371, N.v2371.
  unfold R.v42, N.v42.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2372 (s : N.State) (i : N.Inputs) :
  R.v2372 (state s) (inputs i) = Zmod.unsigned (N.v2372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2372 s i)) at 1.
  unfold R.v2372, N.v2372.
  unfold R.v45, N.v45.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2373 (s : N.State) (i : N.Inputs) :
  R.v2373 (state s) (inputs i) = Zmod.unsigned (N.v2373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2373 s i)) at 1.
  unfold R.v2373, N.v2373.
  unfold R.v47, N.v47.
  rewrite ?node_2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2374 (s : N.State) (i : N.Inputs) :
  R.v2374 (state s) (inputs i) = Zmod.unsigned (N.v2374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2374 s i)) at 1.
  unfold R.v2374, N.v2374.
  rewrite ?node_2372.
  rewrite ?node_2373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2375 (s : N.State) (i : N.Inputs) :
  R.v2375 (state s) (inputs i) = Zmod.unsigned (N.v2375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2375 s i)) at 1.
  unfold R.v2375, N.v2375.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2376 (s : N.State) (i : N.Inputs) :
  R.v2376 (state s) (inputs i) = Zmod.unsigned (N.v2376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2376 s i)) at 1.
  unfold R.v2376, N.v2376.
  rewrite ?node_44.
  rewrite ?node_2371.
  rewrite ?node_2375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2377 (s : N.State) (i : N.Inputs) :
  R.v2377 (state s) (inputs i) = Zmod.unsigned (N.v2377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2377 s i)) at 1.
  unfold R.v2377, N.v2377.
  rewrite ?node_41.
  rewrite ?node_2370.
  rewrite ?node_2376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2378 (s : N.State) (i : N.Inputs) :
  R.v2378 (state s) (inputs i) = Zmod.unsigned (N.v2378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2378 s i)) at 1.
  unfold R.v2378, N.v2378.
  rewrite ?node_38.
  rewrite ?node_2369.
  rewrite ?node_2377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2379 (s : N.State) (i : N.Inputs) :
  R.v2379 (state s) (inputs i) = Zmod.unsigned (N.v2379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2379 s i)) at 1.
  unfold R.v2379, N.v2379.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2380 (s : N.State) (i : N.Inputs) :
  R.v2380 (state s) (inputs i) = Zmod.unsigned (N.v2380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2380 s i)) at 1.
  unfold R.v2380, N.v2380.
  rewrite ?node_2379.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r957_nr_5F957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r957_nr_5F957 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2381 (s : N.State) (i : N.Inputs) :
  R.v2381 (state s) (inputs i) = Zmod.unsigned (N.v2381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2381 s i)) at 1.
  unfold R.v2381, N.v2381.
  unfold R.v6, N.v6.
  rewrite ?node_2370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2382 (s : N.State) (i : N.Inputs) :
  R.v2382 (state s) (inputs i) = Zmod.unsigned (N.v2382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2382 s i)) at 1.
  unfold R.v2382, N.v2382.
  unfold R.v19, N.v19.
  rewrite ?node_2369.
  rewrite ?node_2381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2383 (s : N.State) (i : N.Inputs) :
  R.v2383 (state s) (inputs i) = Zmod.unsigned (N.v2383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2383 s i)) at 1.
  unfold R.v2383, N.v2383.
  rewrite ?node_2382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2384 (s : N.State) (i : N.Inputs) :
  R.v2384 (state s) (inputs i) = Zmod.unsigned (N.v2384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2384 s i)) at 1.
  unfold R.v2384, N.v2384.
  rewrite ?node_2383.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r958_nr_5F958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r958_nr_5F958 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2385 (s : N.State) (i : N.Inputs) :
  R.v2385 (state s) (inputs i) = Zmod.unsigned (N.v2385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2385 s i)) at 1.
  unfold R.v2385, N.v2385.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2386 (s : N.State) (i : N.Inputs) :
  R.v2386 (state s) (inputs i) = Zmod.unsigned (N.v2386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2386 s i)) at 1.
  unfold R.v2386, N.v2386.
  rewrite ?node_2385.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r959_nr_5F959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r959_nr_5F959 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2387 (s : N.State) (i : N.Inputs) :
  R.v2387 (state s) (inputs i) = Zmod.unsigned (N.v2387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2387 s i)) at 1.
  unfold R.v2387, N.v2387.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2388 (s : N.State) (i : N.Inputs) :
  R.v2388 (state s) (inputs i) = Zmod.unsigned (N.v2388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2388 s i)) at 1.
  unfold R.v2388, N.v2388.
  rewrite ?node_2387.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r960_nr_5F960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r960_nr_5F960 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2389 (s : N.State) (i : N.Inputs) :
  R.v2389 (state s) (inputs i) = Zmod.unsigned (N.v2389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2389 s i)) at 1.
  unfold R.v2389, N.v2389.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2390 (s : N.State) (i : N.Inputs) :
  R.v2390 (state s) (inputs i) = Zmod.unsigned (N.v2390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2390 s i)) at 1.
  unfold R.v2390, N.v2390.
  rewrite ?node_2389.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r961_nr_5F961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r961_nr_5F961 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2391 (s : N.State) (i : N.Inputs) :
  R.v2391 (state s) (inputs i) = Zmod.unsigned (N.v2391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2391 s i)) at 1.
  unfold R.v2391, N.v2391.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2392 (s : N.State) (i : N.Inputs) :
  R.v2392 (state s) (inputs i) = Zmod.unsigned (N.v2392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2392 s i)) at 1.
  unfold R.v2392, N.v2392.
  rewrite ?node_2391.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r962_nr_5F962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r962_nr_5F962 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2393 (s : N.State) (i : N.Inputs) :
  R.v2393 (state s) (inputs i) = Zmod.unsigned (N.v2393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2393 s i)) at 1.
  unfold R.v2393, N.v2393.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2394 (s : N.State) (i : N.Inputs) :
  R.v2394 (state s) (inputs i) = Zmod.unsigned (N.v2394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2394 s i)) at 1.
  unfold R.v2394, N.v2394.
  rewrite ?node_2393.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r963_nr_5F963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r963_nr_5F963 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2395 (s : N.State) (i : N.Inputs) :
  R.v2395 (state s) (inputs i) = Zmod.unsigned (N.v2395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2395 s i)) at 1.
  unfold R.v2395, N.v2395.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2396 (s : N.State) (i : N.Inputs) :
  R.v2396 (state s) (inputs i) = Zmod.unsigned (N.v2396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2396 s i)) at 1.
  unfold R.v2396, N.v2396.
  rewrite ?node_2395.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r964_nr_5F964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r964_nr_5F964 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2397 (s : N.State) (i : N.Inputs) :
  R.v2397 (state s) (inputs i) = Zmod.unsigned (N.v2397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2397 s i)) at 1.
  unfold R.v2397, N.v2397.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2398 (s : N.State) (i : N.Inputs) :
  R.v2398 (state s) (inputs i) = Zmod.unsigned (N.v2398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2398 s i)) at 1.
  unfold R.v2398, N.v2398.
  rewrite ?node_2397.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r965_nr_5F965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r965_nr_5F965 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2399 (s : N.State) (i : N.Inputs) :
  R.v2399 (state s) (inputs i) = Zmod.unsigned (N.v2399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2399 s i)) at 1.
  unfold R.v2399, N.v2399.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2400 (s : N.State) (i : N.Inputs) :
  R.v2400 (state s) (inputs i) = Zmod.unsigned (N.v2400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2400 s i)) at 1.
  unfold R.v2400, N.v2400.
  rewrite ?node_2399.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r966_nr_5F966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r966_nr_5F966 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2401 (s : N.State) (i : N.Inputs) :
  R.v2401 (state s) (inputs i) = Zmod.unsigned (N.v2401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2401 s i)) at 1.
  unfold R.v2401, N.v2401.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2402 (s : N.State) (i : N.Inputs) :
  R.v2402 (state s) (inputs i) = Zmod.unsigned (N.v2402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2402 s i)) at 1.
  unfold R.v2402, N.v2402.
  rewrite ?node_2401.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r967_nr_5F967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r967_nr_5F967 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2403 (s : N.State) (i : N.Inputs) :
  R.v2403 (state s) (inputs i) = Zmod.unsigned (N.v2403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2403 s i)) at 1.
  unfold R.v2403, N.v2403.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2404 (s : N.State) (i : N.Inputs) :
  R.v2404 (state s) (inputs i) = Zmod.unsigned (N.v2404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2404 s i)) at 1.
  unfold R.v2404, N.v2404.
  rewrite ?node_2403.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r968_nr_5F968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r968_nr_5F968 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2405 (s : N.State) (i : N.Inputs) :
  R.v2405 (state s) (inputs i) = Zmod.unsigned (N.v2405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2405 s i)) at 1.
  unfold R.v2405, N.v2405.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2406 (s : N.State) (i : N.Inputs) :
  R.v2406 (state s) (inputs i) = Zmod.unsigned (N.v2406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2406 s i)) at 1.
  unfold R.v2406, N.v2406.
  rewrite ?node_2405.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r969_nr_5F969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r969_nr_5F969 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2407 (s : N.State) (i : N.Inputs) :
  R.v2407 (state s) (inputs i) = Zmod.unsigned (N.v2407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2407 s i)) at 1.
  unfold R.v2407, N.v2407.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2408 (s : N.State) (i : N.Inputs) :
  R.v2408 (state s) (inputs i) = Zmod.unsigned (N.v2408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2408 s i)) at 1.
  unfold R.v2408, N.v2408.
  rewrite ?node_2407.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r970_nr_5F970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r970_nr_5F970 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2409 (s : N.State) (i : N.Inputs) :
  R.v2409 (state s) (inputs i) = Zmod.unsigned (N.v2409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2409 s i)) at 1.
  unfold R.v2409, N.v2409.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2410 (s : N.State) (i : N.Inputs) :
  R.v2410 (state s) (inputs i) = Zmod.unsigned (N.v2410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2410 s i)) at 1.
  unfold R.v2410, N.v2410.
  rewrite ?node_2409.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r971_nr_5F971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r971_nr_5F971 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2411 (s : N.State) (i : N.Inputs) :
  R.v2411 (state s) (inputs i) = Zmod.unsigned (N.v2411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2411 s i)) at 1.
  unfold R.v2411, N.v2411.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2412 (s : N.State) (i : N.Inputs) :
  R.v2412 (state s) (inputs i) = Zmod.unsigned (N.v2412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2412 s i)) at 1.
  unfold R.v2412, N.v2412.
  rewrite ?node_2411.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r972_nr_5F972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r972_nr_5F972 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2413 (s : N.State) (i : N.Inputs) :
  R.v2413 (state s) (inputs i) = Zmod.unsigned (N.v2413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2413 s i)) at 1.
  unfold R.v2413, N.v2413.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2414 (s : N.State) (i : N.Inputs) :
  R.v2414 (state s) (inputs i) = Zmod.unsigned (N.v2414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2414 s i)) at 1.
  unfold R.v2414, N.v2414.
  rewrite ?node_2413.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r973_nr_5F973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r973_nr_5F973 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2415 (s : N.State) (i : N.Inputs) :
  R.v2415 (state s) (inputs i) = Zmod.unsigned (N.v2415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2415 s i)) at 1.
  unfold R.v2415, N.v2415.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2416 (s : N.State) (i : N.Inputs) :
  R.v2416 (state s) (inputs i) = Zmod.unsigned (N.v2416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2416 s i)) at 1.
  unfold R.v2416, N.v2416.
  rewrite ?node_2415.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r974_nr_5F974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r974_nr_5F974 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2417 (s : N.State) (i : N.Inputs) :
  R.v2417 (state s) (inputs i) = Zmod.unsigned (N.v2417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2417 s i)) at 1.
  unfold R.v2417, N.v2417.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2418 (s : N.State) (i : N.Inputs) :
  R.v2418 (state s) (inputs i) = Zmod.unsigned (N.v2418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2418 s i)) at 1.
  unfold R.v2418, N.v2418.
  rewrite ?node_2417.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r975_nr_5F975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r975_nr_5F975 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2419 (s : N.State) (i : N.Inputs) :
  R.v2419 (state s) (inputs i) = Zmod.unsigned (N.v2419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2419 s i)) at 1.
  unfold R.v2419, N.v2419.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2420 (s : N.State) (i : N.Inputs) :
  R.v2420 (state s) (inputs i) = Zmod.unsigned (N.v2420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2420 s i)) at 1.
  unfold R.v2420, N.v2420.
  rewrite ?node_2419.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r976_nr_5F976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r976_nr_5F976 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2421 (s : N.State) (i : N.Inputs) :
  R.v2421 (state s) (inputs i) = Zmod.unsigned (N.v2421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2421 s i)) at 1.
  unfold R.v2421, N.v2421.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2422 (s : N.State) (i : N.Inputs) :
  R.v2422 (state s) (inputs i) = Zmod.unsigned (N.v2422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2422 s i)) at 1.
  unfold R.v2422, N.v2422.
  rewrite ?node_2421.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r977_nr_5F977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r977_nr_5F977 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2423 (s : N.State) (i : N.Inputs) :
  R.v2423 (state s) (inputs i) = Zmod.unsigned (N.v2423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2423 s i)) at 1.
  unfold R.v2423, N.v2423.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2424 (s : N.State) (i : N.Inputs) :
  R.v2424 (state s) (inputs i) = Zmod.unsigned (N.v2424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2424 s i)) at 1.
  unfold R.v2424, N.v2424.
  rewrite ?node_2423.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r978_nr_5F978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r978_nr_5F978 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2425 (s : N.State) (i : N.Inputs) :
  R.v2425 (state s) (inputs i) = Zmod.unsigned (N.v2425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2425 s i)) at 1.
  unfold R.v2425, N.v2425.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2426 (s : N.State) (i : N.Inputs) :
  R.v2426 (state s) (inputs i) = Zmod.unsigned (N.v2426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2426 s i)) at 1.
  unfold R.v2426, N.v2426.
  rewrite ?node_2425.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r979_nr_5F979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r979_nr_5F979 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2427 (s : N.State) (i : N.Inputs) :
  R.v2427 (state s) (inputs i) = Zmod.unsigned (N.v2427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2427 s i)) at 1.
  unfold R.v2427, N.v2427.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2428 (s : N.State) (i : N.Inputs) :
  R.v2428 (state s) (inputs i) = Zmod.unsigned (N.v2428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2428 s i)) at 1.
  unfold R.v2428, N.v2428.
  rewrite ?node_2427.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r980_nr_5F980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r980_nr_5F980 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2429 (s : N.State) (i : N.Inputs) :
  R.v2429 (state s) (inputs i) = Zmod.unsigned (N.v2429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2429 s i)) at 1.
  unfold R.v2429, N.v2429.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2430 (s : N.State) (i : N.Inputs) :
  R.v2430 (state s) (inputs i) = Zmod.unsigned (N.v2430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2430 s i)) at 1.
  unfold R.v2430, N.v2430.
  rewrite ?node_2429.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r981_nr_5F981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r981_nr_5F981 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2431 (s : N.State) (i : N.Inputs) :
  R.v2431 (state s) (inputs i) = Zmod.unsigned (N.v2431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2431 s i)) at 1.
  unfold R.v2431, N.v2431.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2432 (s : N.State) (i : N.Inputs) :
  R.v2432 (state s) (inputs i) = Zmod.unsigned (N.v2432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2432 s i)) at 1.
  unfold R.v2432, N.v2432.
  rewrite ?node_2431.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r982_nr_5F982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r982_nr_5F982 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2433 (s : N.State) (i : N.Inputs) :
  R.v2433 (state s) (inputs i) = Zmod.unsigned (N.v2433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2433 s i)) at 1.
  unfold R.v2433, N.v2433.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2434 (s : N.State) (i : N.Inputs) :
  R.v2434 (state s) (inputs i) = Zmod.unsigned (N.v2434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2434 s i)) at 1.
  unfold R.v2434, N.v2434.
  rewrite ?node_2433.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r983_nr_5F983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r983_nr_5F983 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2435 (s : N.State) (i : N.Inputs) :
  R.v2435 (state s) (inputs i) = Zmod.unsigned (N.v2435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2435 s i)) at 1.
  unfold R.v2435, N.v2435.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2436 (s : N.State) (i : N.Inputs) :
  R.v2436 (state s) (inputs i) = Zmod.unsigned (N.v2436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2436 s i)) at 1.
  unfold R.v2436, N.v2436.
  rewrite ?node_2435.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r984_nr_5F984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r984_nr_5F984 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2437 (s : N.State) (i : N.Inputs) :
  R.v2437 (state s) (inputs i) = Zmod.unsigned (N.v2437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2437 s i)) at 1.
  unfold R.v2437, N.v2437.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2438 (s : N.State) (i : N.Inputs) :
  R.v2438 (state s) (inputs i) = Zmod.unsigned (N.v2438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2438 s i)) at 1.
  unfold R.v2438, N.v2438.
  rewrite ?node_2437.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r985_nr_5F985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r985_nr_5F985 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2439 (s : N.State) (i : N.Inputs) :
  R.v2439 (state s) (inputs i) = Zmod.unsigned (N.v2439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2439 s i)) at 1.
  unfold R.v2439, N.v2439.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2440 (s : N.State) (i : N.Inputs) :
  R.v2440 (state s) (inputs i) = Zmod.unsigned (N.v2440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2440 s i)) at 1.
  unfold R.v2440, N.v2440.
  rewrite ?node_2439.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r986_nr_5F986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r986_nr_5F986 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2441 (s : N.State) (i : N.Inputs) :
  R.v2441 (state s) (inputs i) = Zmod.unsigned (N.v2441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2441 s i)) at 1.
  unfold R.v2441, N.v2441.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2442 (s : N.State) (i : N.Inputs) :
  R.v2442 (state s) (inputs i) = Zmod.unsigned (N.v2442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2442 s i)) at 1.
  unfold R.v2442, N.v2442.
  rewrite ?node_2441.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r987_nr_5F987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r987_nr_5F987 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2443 (s : N.State) (i : N.Inputs) :
  R.v2443 (state s) (inputs i) = Zmod.unsigned (N.v2443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2443 s i)) at 1.
  unfold R.v2443, N.v2443.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2444 (s : N.State) (i : N.Inputs) :
  R.v2444 (state s) (inputs i) = Zmod.unsigned (N.v2444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2444 s i)) at 1.
  unfold R.v2444, N.v2444.
  rewrite ?node_2443.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r988_nr_5F988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r988_nr_5F988 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2445 (s : N.State) (i : N.Inputs) :
  R.v2445 (state s) (inputs i) = Zmod.unsigned (N.v2445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2445 s i)) at 1.
  unfold R.v2445, N.v2445.
  rewrite ?node_2382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2446 (s : N.State) (i : N.Inputs) :
  R.v2446 (state s) (inputs i) = Zmod.unsigned (N.v2446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2446 s i)) at 1.
  unfold R.v2446, N.v2446.
  rewrite ?node_2445.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r989_nr_5F989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r989_nr_5F989 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2447 (s : N.State) (i : N.Inputs) :
  R.v2447 (state s) (inputs i) = Zmod.unsigned (N.v2447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2447 s i)) at 1.
  unfold R.v2447, N.v2447.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2448 (s : N.State) (i : N.Inputs) :
  R.v2448 (state s) (inputs i) = Zmod.unsigned (N.v2448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2448 s i)) at 1.
  unfold R.v2448, N.v2448.
  rewrite ?node_2447.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r990_nr_5F990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r990_nr_5F990 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2449 (s : N.State) (i : N.Inputs) :
  R.v2449 (state s) (inputs i) = Zmod.unsigned (N.v2449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2449 s i)) at 1.
  unfold R.v2449, N.v2449.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2450 (s : N.State) (i : N.Inputs) :
  R.v2450 (state s) (inputs i) = Zmod.unsigned (N.v2450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2450 s i)) at 1.
  unfold R.v2450, N.v2450.
  rewrite ?node_2449.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r991_nr_5F991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r991_nr_5F991 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2451 (s : N.State) (i : N.Inputs) :
  R.v2451 (state s) (inputs i) = Zmod.unsigned (N.v2451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2451 s i)) at 1.
  unfold R.v2451, N.v2451.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2452 (s : N.State) (i : N.Inputs) :
  R.v2452 (state s) (inputs i) = Zmod.unsigned (N.v2452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2452 s i)) at 1.
  unfold R.v2452, N.v2452.
  rewrite ?node_2451.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r992_nr_5F992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r992_nr_5F992 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2453 (s : N.State) (i : N.Inputs) :
  R.v2453 (state s) (inputs i) = Zmod.unsigned (N.v2453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2453 s i)) at 1.
  unfold R.v2453, N.v2453.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2454 (s : N.State) (i : N.Inputs) :
  R.v2454 (state s) (inputs i) = Zmod.unsigned (N.v2454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2454 s i)) at 1.
  unfold R.v2454, N.v2454.
  rewrite ?node_2453.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r993_nr_5F993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r993_nr_5F993 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2455 (s : N.State) (i : N.Inputs) :
  R.v2455 (state s) (inputs i) = Zmod.unsigned (N.v2455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2455 s i)) at 1.
  unfold R.v2455, N.v2455.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2456 (s : N.State) (i : N.Inputs) :
  R.v2456 (state s) (inputs i) = Zmod.unsigned (N.v2456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2456 s i)) at 1.
  unfold R.v2456, N.v2456.
  rewrite ?node_2455.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r994_nr_5F994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r994_nr_5F994 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2457 (s : N.State) (i : N.Inputs) :
  R.v2457 (state s) (inputs i) = Zmod.unsigned (N.v2457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2457 s i)) at 1.
  unfold R.v2457, N.v2457.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2458 (s : N.State) (i : N.Inputs) :
  R.v2458 (state s) (inputs i) = Zmod.unsigned (N.v2458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2458 s i)) at 1.
  unfold R.v2458, N.v2458.
  rewrite ?node_2457.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r995_nr_5F995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r995_nr_5F995 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2459 (s : N.State) (i : N.Inputs) :
  R.v2459 (state s) (inputs i) = Zmod.unsigned (N.v2459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2459 s i)) at 1.
  unfold R.v2459, N.v2459.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2460 (s : N.State) (i : N.Inputs) :
  R.v2460 (state s) (inputs i) = Zmod.unsigned (N.v2460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2460 s i)) at 1.
  unfold R.v2460, N.v2460.
  rewrite ?node_2459.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r996_nr_5F996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r996_nr_5F996 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2461 (s : N.State) (i : N.Inputs) :
  R.v2461 (state s) (inputs i) = Zmod.unsigned (N.v2461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2461 s i)) at 1.
  unfold R.v2461, N.v2461.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2462 (s : N.State) (i : N.Inputs) :
  R.v2462 (state s) (inputs i) = Zmod.unsigned (N.v2462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2462 s i)) at 1.
  unfold R.v2462, N.v2462.
  rewrite ?node_2461.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r997_nr_5F997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r997_nr_5F997 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2463 (s : N.State) (i : N.Inputs) :
  R.v2463 (state s) (inputs i) = Zmod.unsigned (N.v2463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2463 s i)) at 1.
  unfold R.v2463, N.v2463.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2464 (s : N.State) (i : N.Inputs) :
  R.v2464 (state s) (inputs i) = Zmod.unsigned (N.v2464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2464 s i)) at 1.
  unfold R.v2464, N.v2464.
  rewrite ?node_2463.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r998_nr_5F998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r998_nr_5F998 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2465 (s : N.State) (i : N.Inputs) :
  R.v2465 (state s) (inputs i) = Zmod.unsigned (N.v2465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2465 s i)) at 1.
  unfold R.v2465, N.v2465.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2466 (s : N.State) (i : N.Inputs) :
  R.v2466 (state s) (inputs i) = Zmod.unsigned (N.v2466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2466 s i)) at 1.
  unfold R.v2466, N.v2466.
  rewrite ?node_2465.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r999_nr_5F999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r999_nr_5F999 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2467 (s : N.State) (i : N.Inputs) :
  R.v2467 (state s) (inputs i) = Zmod.unsigned (N.v2467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2467 s i)) at 1.
  unfold R.v2467, N.v2467.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2468 (s : N.State) (i : N.Inputs) :
  R.v2468 (state s) (inputs i) = Zmod.unsigned (N.v2468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2468 s i)) at 1.
  unfold R.v2468, N.v2468.
  rewrite ?node_2467.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1000_nr_5F1000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1000_nr_5F1000 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2469 (s : N.State) (i : N.Inputs) :
  R.v2469 (state s) (inputs i) = Zmod.unsigned (N.v2469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2469 s i)) at 1.
  unfold R.v2469, N.v2469.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2470 (s : N.State) (i : N.Inputs) :
  R.v2470 (state s) (inputs i) = Zmod.unsigned (N.v2470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2470 s i)) at 1.
  unfold R.v2470, N.v2470.
  rewrite ?node_2469.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1001_nr_5F1001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1001_nr_5F1001 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2471 (s : N.State) (i : N.Inputs) :
  R.v2471 (state s) (inputs i) = Zmod.unsigned (N.v2471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2471 s i)) at 1.
  unfold R.v2471, N.v2471.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2472 (s : N.State) (i : N.Inputs) :
  R.v2472 (state s) (inputs i) = Zmod.unsigned (N.v2472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2472 s i)) at 1.
  unfold R.v2472, N.v2472.
  rewrite ?node_2471.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1002_nr_5F1002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1002_nr_5F1002 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2473 (s : N.State) (i : N.Inputs) :
  R.v2473 (state s) (inputs i) = Zmod.unsigned (N.v2473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2473 s i)) at 1.
  unfold R.v2473, N.v2473.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2474 (s : N.State) (i : N.Inputs) :
  R.v2474 (state s) (inputs i) = Zmod.unsigned (N.v2474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2474 s i)) at 1.
  unfold R.v2474, N.v2474.
  rewrite ?node_2473.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1003_nr_5F1003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1003_nr_5F1003 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2475 (s : N.State) (i : N.Inputs) :
  R.v2475 (state s) (inputs i) = Zmod.unsigned (N.v2475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2475 s i)) at 1.
  unfold R.v2475, N.v2475.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2476 (s : N.State) (i : N.Inputs) :
  R.v2476 (state s) (inputs i) = Zmod.unsigned (N.v2476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2476 s i)) at 1.
  unfold R.v2476, N.v2476.
  rewrite ?node_2475.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1004_nr_5F1004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1004_nr_5F1004 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2477 (s : N.State) (i : N.Inputs) :
  R.v2477 (state s) (inputs i) = Zmod.unsigned (N.v2477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2477 s i)) at 1.
  unfold R.v2477, N.v2477.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2478 (s : N.State) (i : N.Inputs) :
  R.v2478 (state s) (inputs i) = Zmod.unsigned (N.v2478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2478 s i)) at 1.
  unfold R.v2478, N.v2478.
  rewrite ?node_2477.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1005_nr_5F1005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1005_nr_5F1005 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2479 (s : N.State) (i : N.Inputs) :
  R.v2479 (state s) (inputs i) = Zmod.unsigned (N.v2479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2479 s i)) at 1.
  unfold R.v2479, N.v2479.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2480 (s : N.State) (i : N.Inputs) :
  R.v2480 (state s) (inputs i) = Zmod.unsigned (N.v2480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2480 s i)) at 1.
  unfold R.v2480, N.v2480.
  rewrite ?node_2479.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1006_nr_5F1006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1006_nr_5F1006 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2481 (s : N.State) (i : N.Inputs) :
  R.v2481 (state s) (inputs i) = Zmod.unsigned (N.v2481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2481 s i)) at 1.
  unfold R.v2481, N.v2481.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2482 (s : N.State) (i : N.Inputs) :
  R.v2482 (state s) (inputs i) = Zmod.unsigned (N.v2482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2482 s i)) at 1.
  unfold R.v2482, N.v2482.
  rewrite ?node_2481.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1007_nr_5F1007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1007_nr_5F1007 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2483 (s : N.State) (i : N.Inputs) :
  R.v2483 (state s) (inputs i) = Zmod.unsigned (N.v2483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2483 s i)) at 1.
  unfold R.v2483, N.v2483.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2484 (s : N.State) (i : N.Inputs) :
  R.v2484 (state s) (inputs i) = Zmod.unsigned (N.v2484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2484 s i)) at 1.
  unfold R.v2484, N.v2484.
  rewrite ?node_2483.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1008_nr_5F1008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1008_nr_5F1008 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2485 (s : N.State) (i : N.Inputs) :
  R.v2485 (state s) (inputs i) = Zmod.unsigned (N.v2485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2485 s i)) at 1.
  unfold R.v2485, N.v2485.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2486 (s : N.State) (i : N.Inputs) :
  R.v2486 (state s) (inputs i) = Zmod.unsigned (N.v2486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2486 s i)) at 1.
  unfold R.v2486, N.v2486.
  rewrite ?node_2485.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1009_nr_5F1009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1009_nr_5F1009 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2487 (s : N.State) (i : N.Inputs) :
  R.v2487 (state s) (inputs i) = Zmod.unsigned (N.v2487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2487 s i)) at 1.
  unfold R.v2487, N.v2487.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2488 (s : N.State) (i : N.Inputs) :
  R.v2488 (state s) (inputs i) = Zmod.unsigned (N.v2488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2488 s i)) at 1.
  unfold R.v2488, N.v2488.
  rewrite ?node_2487.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1010_nr_5F1010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1010_nr_5F1010 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2489 (s : N.State) (i : N.Inputs) :
  R.v2489 (state s) (inputs i) = Zmod.unsigned (N.v2489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2489 s i)) at 1.
  unfold R.v2489, N.v2489.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2490 (s : N.State) (i : N.Inputs) :
  R.v2490 (state s) (inputs i) = Zmod.unsigned (N.v2490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2490 s i)) at 1.
  unfold R.v2490, N.v2490.
  rewrite ?node_2489.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1011_nr_5F1011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1011_nr_5F1011 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2491 (s : N.State) (i : N.Inputs) :
  R.v2491 (state s) (inputs i) = Zmod.unsigned (N.v2491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2491 s i)) at 1.
  unfold R.v2491, N.v2491.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2492 (s : N.State) (i : N.Inputs) :
  R.v2492 (state s) (inputs i) = Zmod.unsigned (N.v2492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2492 s i)) at 1.
  unfold R.v2492, N.v2492.
  rewrite ?node_2491.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1012_nr_5F1012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1012_nr_5F1012 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2493 (s : N.State) (i : N.Inputs) :
  R.v2493 (state s) (inputs i) = Zmod.unsigned (N.v2493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2493 s i)) at 1.
  unfold R.v2493, N.v2493.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2494 (s : N.State) (i : N.Inputs) :
  R.v2494 (state s) (inputs i) = Zmod.unsigned (N.v2494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2494 s i)) at 1.
  unfold R.v2494, N.v2494.
  rewrite ?node_2493.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1013_nr_5F1013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1013_nr_5F1013 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2495 (s : N.State) (i : N.Inputs) :
  R.v2495 (state s) (inputs i) = Zmod.unsigned (N.v2495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2495 s i)) at 1.
  unfold R.v2495, N.v2495.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2496 (s : N.State) (i : N.Inputs) :
  R.v2496 (state s) (inputs i) = Zmod.unsigned (N.v2496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2496 s i)) at 1.
  unfold R.v2496, N.v2496.
  rewrite ?node_2495.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1014_nr_5F1014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1014_nr_5F1014 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2497 (s : N.State) (i : N.Inputs) :
  R.v2497 (state s) (inputs i) = Zmod.unsigned (N.v2497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2497 s i)) at 1.
  unfold R.v2497, N.v2497.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2498 (s : N.State) (i : N.Inputs) :
  R.v2498 (state s) (inputs i) = Zmod.unsigned (N.v2498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2498 s i)) at 1.
  unfold R.v2498, N.v2498.
  rewrite ?node_2497.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1015_nr_5F1015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1015_nr_5F1015 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2499 (s : N.State) (i : N.Inputs) :
  R.v2499 (state s) (inputs i) = Zmod.unsigned (N.v2499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2499 s i)) at 1.
  unfold R.v2499, N.v2499.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2500 (s : N.State) (i : N.Inputs) :
  R.v2500 (state s) (inputs i) = Zmod.unsigned (N.v2500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2500 s i)) at 1.
  unfold R.v2500, N.v2500.
  rewrite ?node_2499.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1016_nr_5F1016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1016_nr_5F1016 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2501 (s : N.State) (i : N.Inputs) :
  R.v2501 (state s) (inputs i) = Zmod.unsigned (N.v2501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2501 s i)) at 1.
  unfold R.v2501, N.v2501.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2502 (s : N.State) (i : N.Inputs) :
  R.v2502 (state s) (inputs i) = Zmod.unsigned (N.v2502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2502 s i)) at 1.
  unfold R.v2502, N.v2502.
  rewrite ?node_2501.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1017_nr_5F1017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1017_nr_5F1017 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2503 (s : N.State) (i : N.Inputs) :
  R.v2503 (state s) (inputs i) = Zmod.unsigned (N.v2503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2503 s i)) at 1.
  unfold R.v2503, N.v2503.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2504 (s : N.State) (i : N.Inputs) :
  R.v2504 (state s) (inputs i) = Zmod.unsigned (N.v2504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2504 s i)) at 1.
  unfold R.v2504, N.v2504.
  rewrite ?node_2503.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1018_nr_5F1018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1018_nr_5F1018 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2505 (s : N.State) (i : N.Inputs) :
  R.v2505 (state s) (inputs i) = Zmod.unsigned (N.v2505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2505 s i)) at 1.
  unfold R.v2505, N.v2505.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2506 (s : N.State) (i : N.Inputs) :
  R.v2506 (state s) (inputs i) = Zmod.unsigned (N.v2506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2506 s i)) at 1.
  unfold R.v2506, N.v2506.
  rewrite ?node_2505.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1019_nr_5F1019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1019_nr_5F1019 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2507 (s : N.State) (i : N.Inputs) :
  R.v2507 (state s) (inputs i) = Zmod.unsigned (N.v2507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2507 s i)) at 1.
  unfold R.v2507, N.v2507.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2508 (s : N.State) (i : N.Inputs) :
  R.v2508 (state s) (inputs i) = Zmod.unsigned (N.v2508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2508 s i)) at 1.
  unfold R.v2508, N.v2508.
  unfold R.v33, N.v33.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2509 (s : N.State) (i : N.Inputs) :
  R.v2509 (state s) (inputs i) = Zmod.unsigned (N.v2509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2509 s i)) at 1.
  unfold R.v2509, N.v2509.
  unfold R.v35, N.v35.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2510 (s : N.State) (i : N.Inputs) :
  R.v2510 (state s) (inputs i) = Zmod.unsigned (N.v2510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2510 s i)) at 1.
  unfold R.v2510, N.v2510.
  rewrite ?node_2508.
  rewrite ?node_2509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2511 (s : N.State) (i : N.Inputs) :
  R.v2511 (state s) (inputs i) = Zmod.unsigned (N.v2511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2511 s i)) at 1.
  unfold R.v2511, N.v2511.
  unfold R.v39, N.v39.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2512 (s : N.State) (i : N.Inputs) :
  R.v2512 (state s) (inputs i) = Zmod.unsigned (N.v2512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2512 s i)) at 1.
  unfold R.v2512, N.v2512.
  unfold R.v42, N.v42.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2513 (s : N.State) (i : N.Inputs) :
  R.v2513 (state s) (inputs i) = Zmod.unsigned (N.v2513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2513 s i)) at 1.
  unfold R.v2513, N.v2513.
  unfold R.v45, N.v45.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2514 (s : N.State) (i : N.Inputs) :
  R.v2514 (state s) (inputs i) = Zmod.unsigned (N.v2514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2514 s i)) at 1.
  unfold R.v2514, N.v2514.
  unfold R.v47, N.v47.
  rewrite ?node_2507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2515 (s : N.State) (i : N.Inputs) :
  R.v2515 (state s) (inputs i) = Zmod.unsigned (N.v2515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2515 s i)) at 1.
  unfold R.v2515, N.v2515.
  rewrite ?node_2513.
  rewrite ?node_2514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2516 (s : N.State) (i : N.Inputs) :
  R.v2516 (state s) (inputs i) = Zmod.unsigned (N.v2516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2516 s i)) at 1.
  unfold R.v2516, N.v2516.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2517 (s : N.State) (i : N.Inputs) :
  R.v2517 (state s) (inputs i) = Zmod.unsigned (N.v2517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2517 s i)) at 1.
  unfold R.v2517, N.v2517.
  rewrite ?node_44.
  rewrite ?node_2512.
  rewrite ?node_2516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2518 (s : N.State) (i : N.Inputs) :
  R.v2518 (state s) (inputs i) = Zmod.unsigned (N.v2518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2518 s i)) at 1.
  unfold R.v2518, N.v2518.
  rewrite ?node_41.
  rewrite ?node_2511.
  rewrite ?node_2517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2519 (s : N.State) (i : N.Inputs) :
  R.v2519 (state s) (inputs i) = Zmod.unsigned (N.v2519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2519 s i)) at 1.
  unfold R.v2519, N.v2519.
  rewrite ?node_38.
  rewrite ?node_2510.
  rewrite ?node_2518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2520 (s : N.State) (i : N.Inputs) :
  R.v2520 (state s) (inputs i) = Zmod.unsigned (N.v2520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2520 s i)) at 1.
  unfold R.v2520, N.v2520.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2521 (s : N.State) (i : N.Inputs) :
  R.v2521 (state s) (inputs i) = Zmod.unsigned (N.v2521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2521 s i)) at 1.
  unfold R.v2521, N.v2521.
  rewrite ?node_2520.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1020_nr_5F1020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1020_nr_5F1020 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2522 (s : N.State) (i : N.Inputs) :
  R.v2522 (state s) (inputs i) = Zmod.unsigned (N.v2522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2522 s i)) at 1.
  unfold R.v2522, N.v2522.
  unfold R.v6, N.v6.
  rewrite ?node_2511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2523 (s : N.State) (i : N.Inputs) :
  R.v2523 (state s) (inputs i) = Zmod.unsigned (N.v2523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2523 s i)) at 1.
  unfold R.v2523, N.v2523.
  unfold R.v19, N.v19.
  rewrite ?node_2510.
  rewrite ?node_2522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2524 (s : N.State) (i : N.Inputs) :
  R.v2524 (state s) (inputs i) = Zmod.unsigned (N.v2524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2524 s i)) at 1.
  unfold R.v2524, N.v2524.
  rewrite ?node_2523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2525 (s : N.State) (i : N.Inputs) :
  R.v2525 (state s) (inputs i) = Zmod.unsigned (N.v2525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2525 s i)) at 1.
  unfold R.v2525, N.v2525.
  rewrite ?node_2524.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1021_nr_5F1021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1021_nr_5F1021 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2526 (s : N.State) (i : N.Inputs) :
  R.v2526 (state s) (inputs i) = Zmod.unsigned (N.v2526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2526 s i)) at 1.
  unfold R.v2526, N.v2526.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2527 (s : N.State) (i : N.Inputs) :
  R.v2527 (state s) (inputs i) = Zmod.unsigned (N.v2527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2527 s i)) at 1.
  unfold R.v2527, N.v2527.
  rewrite ?node_2526.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1022_nr_5F1022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1022_nr_5F1022 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2528 (s : N.State) (i : N.Inputs) :
  R.v2528 (state s) (inputs i) = Zmod.unsigned (N.v2528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2528 s i)) at 1.
  unfold R.v2528, N.v2528.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2529 (s : N.State) (i : N.Inputs) :
  R.v2529 (state s) (inputs i) = Zmod.unsigned (N.v2529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2529 s i)) at 1.
  unfold R.v2529, N.v2529.
  rewrite ?node_2528.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1023_nr_5F1023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1023_nr_5F1023 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2530 (s : N.State) (i : N.Inputs) :
  R.v2530 (state s) (inputs i) = Zmod.unsigned (N.v2530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2530 s i)) at 1.
  unfold R.v2530, N.v2530.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2531 (s : N.State) (i : N.Inputs) :
  R.v2531 (state s) (inputs i) = Zmod.unsigned (N.v2531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2531 s i)) at 1.
  unfold R.v2531, N.v2531.
  rewrite ?node_2530.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1024_nr_5F1024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1024_nr_5F1024 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2532 (s : N.State) (i : N.Inputs) :
  R.v2532 (state s) (inputs i) = Zmod.unsigned (N.v2532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2532 s i)) at 1.
  unfold R.v2532, N.v2532.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2533 (s : N.State) (i : N.Inputs) :
  R.v2533 (state s) (inputs i) = Zmod.unsigned (N.v2533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2533 s i)) at 1.
  unfold R.v2533, N.v2533.
  rewrite ?node_2532.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1025_nr_5F1025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1025_nr_5F1025 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2534 (s : N.State) (i : N.Inputs) :
  R.v2534 (state s) (inputs i) = Zmod.unsigned (N.v2534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2534 s i)) at 1.
  unfold R.v2534, N.v2534.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2535 (s : N.State) (i : N.Inputs) :
  R.v2535 (state s) (inputs i) = Zmod.unsigned (N.v2535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2535 s i)) at 1.
  unfold R.v2535, N.v2535.
  rewrite ?node_2534.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1026_nr_5F1026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1026_nr_5F1026 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2536 (s : N.State) (i : N.Inputs) :
  R.v2536 (state s) (inputs i) = Zmod.unsigned (N.v2536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2536 s i)) at 1.
  unfold R.v2536, N.v2536.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2537 (s : N.State) (i : N.Inputs) :
  R.v2537 (state s) (inputs i) = Zmod.unsigned (N.v2537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2537 s i)) at 1.
  unfold R.v2537, N.v2537.
  rewrite ?node_2536.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1027_nr_5F1027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1027_nr_5F1027 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2538 (s : N.State) (i : N.Inputs) :
  R.v2538 (state s) (inputs i) = Zmod.unsigned (N.v2538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2538 s i)) at 1.
  unfold R.v2538, N.v2538.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2539 (s : N.State) (i : N.Inputs) :
  R.v2539 (state s) (inputs i) = Zmod.unsigned (N.v2539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2539 s i)) at 1.
  unfold R.v2539, N.v2539.
  rewrite ?node_2538.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1028_nr_5F1028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1028_nr_5F1028 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2540 (s : N.State) (i : N.Inputs) :
  R.v2540 (state s) (inputs i) = Zmod.unsigned (N.v2540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2540 s i)) at 1.
  unfold R.v2540, N.v2540.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2541 (s : N.State) (i : N.Inputs) :
  R.v2541 (state s) (inputs i) = Zmod.unsigned (N.v2541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2541 s i)) at 1.
  unfold R.v2541, N.v2541.
  rewrite ?node_2540.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1029_nr_5F1029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1029_nr_5F1029 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2542 (s : N.State) (i : N.Inputs) :
  R.v2542 (state s) (inputs i) = Zmod.unsigned (N.v2542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2542 s i)) at 1.
  unfold R.v2542, N.v2542.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2543 (s : N.State) (i : N.Inputs) :
  R.v2543 (state s) (inputs i) = Zmod.unsigned (N.v2543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2543 s i)) at 1.
  unfold R.v2543, N.v2543.
  rewrite ?node_2542.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1030_nr_5F1030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1030_nr_5F1030 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2544 (s : N.State) (i : N.Inputs) :
  R.v2544 (state s) (inputs i) = Zmod.unsigned (N.v2544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2544 s i)) at 1.
  unfold R.v2544, N.v2544.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2545 (s : N.State) (i : N.Inputs) :
  R.v2545 (state s) (inputs i) = Zmod.unsigned (N.v2545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2545 s i)) at 1.
  unfold R.v2545, N.v2545.
  rewrite ?node_2544.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1031_nr_5F1031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1031_nr_5F1031 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2546 (s : N.State) (i : N.Inputs) :
  R.v2546 (state s) (inputs i) = Zmod.unsigned (N.v2546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2546 s i)) at 1.
  unfold R.v2546, N.v2546.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2547 (s : N.State) (i : N.Inputs) :
  R.v2547 (state s) (inputs i) = Zmod.unsigned (N.v2547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2547 s i)) at 1.
  unfold R.v2547, N.v2547.
  rewrite ?node_2546.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1032_nr_5F1032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1032_nr_5F1032 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2548 (s : N.State) (i : N.Inputs) :
  R.v2548 (state s) (inputs i) = Zmod.unsigned (N.v2548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2548 s i)) at 1.
  unfold R.v2548, N.v2548.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2549 (s : N.State) (i : N.Inputs) :
  R.v2549 (state s) (inputs i) = Zmod.unsigned (N.v2549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2549 s i)) at 1.
  unfold R.v2549, N.v2549.
  rewrite ?node_2548.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1033_nr_5F1033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1033_nr_5F1033 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2550 (s : N.State) (i : N.Inputs) :
  R.v2550 (state s) (inputs i) = Zmod.unsigned (N.v2550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2550 s i)) at 1.
  unfold R.v2550, N.v2550.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2551 (s : N.State) (i : N.Inputs) :
  R.v2551 (state s) (inputs i) = Zmod.unsigned (N.v2551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2551 s i)) at 1.
  unfold R.v2551, N.v2551.
  rewrite ?node_2550.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1034_nr_5F1034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1034_nr_5F1034 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2552 (s : N.State) (i : N.Inputs) :
  R.v2552 (state s) (inputs i) = Zmod.unsigned (N.v2552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2552 s i)) at 1.
  unfold R.v2552, N.v2552.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2553 (s : N.State) (i : N.Inputs) :
  R.v2553 (state s) (inputs i) = Zmod.unsigned (N.v2553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2553 s i)) at 1.
  unfold R.v2553, N.v2553.
  rewrite ?node_2552.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1035_nr_5F1035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1035_nr_5F1035 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2554 (s : N.State) (i : N.Inputs) :
  R.v2554 (state s) (inputs i) = Zmod.unsigned (N.v2554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2554 s i)) at 1.
  unfold R.v2554, N.v2554.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2555 (s : N.State) (i : N.Inputs) :
  R.v2555 (state s) (inputs i) = Zmod.unsigned (N.v2555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2555 s i)) at 1.
  unfold R.v2555, N.v2555.
  rewrite ?node_2554.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1036_nr_5F1036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1036_nr_5F1036 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2556 (s : N.State) (i : N.Inputs) :
  R.v2556 (state s) (inputs i) = Zmod.unsigned (N.v2556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2556 s i)) at 1.
  unfold R.v2556, N.v2556.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2557 (s : N.State) (i : N.Inputs) :
  R.v2557 (state s) (inputs i) = Zmod.unsigned (N.v2557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2557 s i)) at 1.
  unfold R.v2557, N.v2557.
  rewrite ?node_2556.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1037_nr_5F1037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1037_nr_5F1037 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2558 (s : N.State) (i : N.Inputs) :
  R.v2558 (state s) (inputs i) = Zmod.unsigned (N.v2558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2558 s i)) at 1.
  unfold R.v2558, N.v2558.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2559 (s : N.State) (i : N.Inputs) :
  R.v2559 (state s) (inputs i) = Zmod.unsigned (N.v2559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2559 s i)) at 1.
  unfold R.v2559, N.v2559.
  rewrite ?node_2558.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1038_nr_5F1038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1038_nr_5F1038 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2560 (s : N.State) (i : N.Inputs) :
  R.v2560 (state s) (inputs i) = Zmod.unsigned (N.v2560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2560 s i)) at 1.
  unfold R.v2560, N.v2560.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2561 (s : N.State) (i : N.Inputs) :
  R.v2561 (state s) (inputs i) = Zmod.unsigned (N.v2561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2561 s i)) at 1.
  unfold R.v2561, N.v2561.
  rewrite ?node_2560.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1039_nr_5F1039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1039_nr_5F1039 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2562 (s : N.State) (i : N.Inputs) :
  R.v2562 (state s) (inputs i) = Zmod.unsigned (N.v2562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2562 s i)) at 1.
  unfold R.v2562, N.v2562.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2563 (s : N.State) (i : N.Inputs) :
  R.v2563 (state s) (inputs i) = Zmod.unsigned (N.v2563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2563 s i)) at 1.
  unfold R.v2563, N.v2563.
  rewrite ?node_2562.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1040_nr_5F1040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1040_nr_5F1040 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2564 (s : N.State) (i : N.Inputs) :
  R.v2564 (state s) (inputs i) = Zmod.unsigned (N.v2564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2564 s i)) at 1.
  unfold R.v2564, N.v2564.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2565 (s : N.State) (i : N.Inputs) :
  R.v2565 (state s) (inputs i) = Zmod.unsigned (N.v2565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2565 s i)) at 1.
  unfold R.v2565, N.v2565.
  rewrite ?node_2564.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1041_nr_5F1041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1041_nr_5F1041 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2566 (s : N.State) (i : N.Inputs) :
  R.v2566 (state s) (inputs i) = Zmod.unsigned (N.v2566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2566 s i)) at 1.
  unfold R.v2566, N.v2566.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2567 (s : N.State) (i : N.Inputs) :
  R.v2567 (state s) (inputs i) = Zmod.unsigned (N.v2567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2567 s i)) at 1.
  unfold R.v2567, N.v2567.
  rewrite ?node_2566.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1042_nr_5F1042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1042_nr_5F1042 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2568 (s : N.State) (i : N.Inputs) :
  R.v2568 (state s) (inputs i) = Zmod.unsigned (N.v2568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2568 s i)) at 1.
  unfold R.v2568, N.v2568.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2569 (s : N.State) (i : N.Inputs) :
  R.v2569 (state s) (inputs i) = Zmod.unsigned (N.v2569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2569 s i)) at 1.
  unfold R.v2569, N.v2569.
  rewrite ?node_2568.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1043_nr_5F1043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1043_nr_5F1043 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2570 (s : N.State) (i : N.Inputs) :
  R.v2570 (state s) (inputs i) = Zmod.unsigned (N.v2570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2570 s i)) at 1.
  unfold R.v2570, N.v2570.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2571 (s : N.State) (i : N.Inputs) :
  R.v2571 (state s) (inputs i) = Zmod.unsigned (N.v2571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2571 s i)) at 1.
  unfold R.v2571, N.v2571.
  rewrite ?node_2570.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1044_nr_5F1044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1044_nr_5F1044 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2572 (s : N.State) (i : N.Inputs) :
  R.v2572 (state s) (inputs i) = Zmod.unsigned (N.v2572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2572 s i)) at 1.
  unfold R.v2572, N.v2572.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2573 (s : N.State) (i : N.Inputs) :
  R.v2573 (state s) (inputs i) = Zmod.unsigned (N.v2573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2573 s i)) at 1.
  unfold R.v2573, N.v2573.
  rewrite ?node_2572.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1045_nr_5F1045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1045_nr_5F1045 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2574 (s : N.State) (i : N.Inputs) :
  R.v2574 (state s) (inputs i) = Zmod.unsigned (N.v2574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2574 s i)) at 1.
  unfold R.v2574, N.v2574.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2575 (s : N.State) (i : N.Inputs) :
  R.v2575 (state s) (inputs i) = Zmod.unsigned (N.v2575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2575 s i)) at 1.
  unfold R.v2575, N.v2575.
  rewrite ?node_2574.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1046_nr_5F1046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1046_nr_5F1046 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2576 (s : N.State) (i : N.Inputs) :
  R.v2576 (state s) (inputs i) = Zmod.unsigned (N.v2576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2576 s i)) at 1.
  unfold R.v2576, N.v2576.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2577 (s : N.State) (i : N.Inputs) :
  R.v2577 (state s) (inputs i) = Zmod.unsigned (N.v2577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2577 s i)) at 1.
  unfold R.v2577, N.v2577.
  rewrite ?node_2576.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1047_nr_5F1047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1047_nr_5F1047 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2578 (s : N.State) (i : N.Inputs) :
  R.v2578 (state s) (inputs i) = Zmod.unsigned (N.v2578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2578 s i)) at 1.
  unfold R.v2578, N.v2578.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2579 (s : N.State) (i : N.Inputs) :
  R.v2579 (state s) (inputs i) = Zmod.unsigned (N.v2579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2579 s i)) at 1.
  unfold R.v2579, N.v2579.
  rewrite ?node_2578.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1048_nr_5F1048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1048_nr_5F1048 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2580 (s : N.State) (i : N.Inputs) :
  R.v2580 (state s) (inputs i) = Zmod.unsigned (N.v2580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2580 s i)) at 1.
  unfold R.v2580, N.v2580.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2581 (s : N.State) (i : N.Inputs) :
  R.v2581 (state s) (inputs i) = Zmod.unsigned (N.v2581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2581 s i)) at 1.
  unfold R.v2581, N.v2581.
  rewrite ?node_2580.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1049_nr_5F1049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1049_nr_5F1049 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2582 (s : N.State) (i : N.Inputs) :
  R.v2582 (state s) (inputs i) = Zmod.unsigned (N.v2582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2582 s i)) at 1.
  unfold R.v2582, N.v2582.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2583 (s : N.State) (i : N.Inputs) :
  R.v2583 (state s) (inputs i) = Zmod.unsigned (N.v2583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2583 s i)) at 1.
  unfold R.v2583, N.v2583.
  rewrite ?node_2582.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1050_nr_5F1050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1050_nr_5F1050 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2584 (s : N.State) (i : N.Inputs) :
  R.v2584 (state s) (inputs i) = Zmod.unsigned (N.v2584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2584 s i)) at 1.
  unfold R.v2584, N.v2584.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2585 (s : N.State) (i : N.Inputs) :
  R.v2585 (state s) (inputs i) = Zmod.unsigned (N.v2585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2585 s i)) at 1.
  unfold R.v2585, N.v2585.
  rewrite ?node_2584.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1051_nr_5F1051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1051_nr_5F1051 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2586 (s : N.State) (i : N.Inputs) :
  R.v2586 (state s) (inputs i) = Zmod.unsigned (N.v2586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2586 s i)) at 1.
  unfold R.v2586, N.v2586.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2587 (s : N.State) (i : N.Inputs) :
  R.v2587 (state s) (inputs i) = Zmod.unsigned (N.v2587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2587 s i)) at 1.
  unfold R.v2587, N.v2587.
  rewrite ?node_2586.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1052_nr_5F1052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1052_nr_5F1052 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2588 (s : N.State) (i : N.Inputs) :
  R.v2588 (state s) (inputs i) = Zmod.unsigned (N.v2588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2588 s i)) at 1.
  unfold R.v2588, N.v2588.
  rewrite ?node_2523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2589 (s : N.State) (i : N.Inputs) :
  R.v2589 (state s) (inputs i) = Zmod.unsigned (N.v2589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2589 s i)) at 1.
  unfold R.v2589, N.v2589.
  rewrite ?node_2588.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1053_nr_5F1053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1053_nr_5F1053 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2590 (s : N.State) (i : N.Inputs) :
  R.v2590 (state s) (inputs i) = Zmod.unsigned (N.v2590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2590 s i)) at 1.
  unfold R.v2590, N.v2590.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2591 (s : N.State) (i : N.Inputs) :
  R.v2591 (state s) (inputs i) = Zmod.unsigned (N.v2591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2591 s i)) at 1.
  unfold R.v2591, N.v2591.
  rewrite ?node_2590.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1054_nr_5F1054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1054_nr_5F1054 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2592 (s : N.State) (i : N.Inputs) :
  R.v2592 (state s) (inputs i) = Zmod.unsigned (N.v2592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2592 s i)) at 1.
  unfold R.v2592, N.v2592.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2593 (s : N.State) (i : N.Inputs) :
  R.v2593 (state s) (inputs i) = Zmod.unsigned (N.v2593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2593 s i)) at 1.
  unfold R.v2593, N.v2593.
  rewrite ?node_2592.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1055_nr_5F1055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1055_nr_5F1055 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2594 (s : N.State) (i : N.Inputs) :
  R.v2594 (state s) (inputs i) = Zmod.unsigned (N.v2594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2594 s i)) at 1.
  unfold R.v2594, N.v2594.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2595 (s : N.State) (i : N.Inputs) :
  R.v2595 (state s) (inputs i) = Zmod.unsigned (N.v2595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2595 s i)) at 1.
  unfold R.v2595, N.v2595.
  rewrite ?node_2594.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1056_nr_5F1056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1056_nr_5F1056 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2596 (s : N.State) (i : N.Inputs) :
  R.v2596 (state s) (inputs i) = Zmod.unsigned (N.v2596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2596 s i)) at 1.
  unfold R.v2596, N.v2596.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2597 (s : N.State) (i : N.Inputs) :
  R.v2597 (state s) (inputs i) = Zmod.unsigned (N.v2597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2597 s i)) at 1.
  unfold R.v2597, N.v2597.
  rewrite ?node_2596.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1057_nr_5F1057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1057_nr_5F1057 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2598 (s : N.State) (i : N.Inputs) :
  R.v2598 (state s) (inputs i) = Zmod.unsigned (N.v2598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2598 s i)) at 1.
  unfold R.v2598, N.v2598.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2599 (s : N.State) (i : N.Inputs) :
  R.v2599 (state s) (inputs i) = Zmod.unsigned (N.v2599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2599 s i)) at 1.
  unfold R.v2599, N.v2599.
  rewrite ?node_2598.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1058_nr_5F1058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1058_nr_5F1058 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2600 (s : N.State) (i : N.Inputs) :
  R.v2600 (state s) (inputs i) = Zmod.unsigned (N.v2600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2600 s i)) at 1.
  unfold R.v2600, N.v2600.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2601 (s : N.State) (i : N.Inputs) :
  R.v2601 (state s) (inputs i) = Zmod.unsigned (N.v2601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2601 s i)) at 1.
  unfold R.v2601, N.v2601.
  rewrite ?node_2600.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1059_nr_5F1059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1059_nr_5F1059 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2602 (s : N.State) (i : N.Inputs) :
  R.v2602 (state s) (inputs i) = Zmod.unsigned (N.v2602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2602 s i)) at 1.
  unfold R.v2602, N.v2602.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2603 (s : N.State) (i : N.Inputs) :
  R.v2603 (state s) (inputs i) = Zmod.unsigned (N.v2603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2603 s i)) at 1.
  unfold R.v2603, N.v2603.
  rewrite ?node_2602.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1060_nr_5F1060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1060_nr_5F1060 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2604 (s : N.State) (i : N.Inputs) :
  R.v2604 (state s) (inputs i) = Zmod.unsigned (N.v2604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2604 s i)) at 1.
  unfold R.v2604, N.v2604.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2605 (s : N.State) (i : N.Inputs) :
  R.v2605 (state s) (inputs i) = Zmod.unsigned (N.v2605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2605 s i)) at 1.
  unfold R.v2605, N.v2605.
  rewrite ?node_2604.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1061_nr_5F1061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1061_nr_5F1061 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2606 (s : N.State) (i : N.Inputs) :
  R.v2606 (state s) (inputs i) = Zmod.unsigned (N.v2606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2606 s i)) at 1.
  unfold R.v2606, N.v2606.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2607 (s : N.State) (i : N.Inputs) :
  R.v2607 (state s) (inputs i) = Zmod.unsigned (N.v2607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2607 s i)) at 1.
  unfold R.v2607, N.v2607.
  rewrite ?node_2606.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1062_nr_5F1062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1062_nr_5F1062 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2608 (s : N.State) (i : N.Inputs) :
  R.v2608 (state s) (inputs i) = Zmod.unsigned (N.v2608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2608 s i)) at 1.
  unfold R.v2608, N.v2608.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2609 (s : N.State) (i : N.Inputs) :
  R.v2609 (state s) (inputs i) = Zmod.unsigned (N.v2609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2609 s i)) at 1.
  unfold R.v2609, N.v2609.
  rewrite ?node_2608.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1063_nr_5F1063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1063_nr_5F1063 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2610 (s : N.State) (i : N.Inputs) :
  R.v2610 (state s) (inputs i) = Zmod.unsigned (N.v2610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2610 s i)) at 1.
  unfold R.v2610, N.v2610.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2611 (s : N.State) (i : N.Inputs) :
  R.v2611 (state s) (inputs i) = Zmod.unsigned (N.v2611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2611 s i)) at 1.
  unfold R.v2611, N.v2611.
  rewrite ?node_2610.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1064_nr_5F1064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1064_nr_5F1064 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2612 (s : N.State) (i : N.Inputs) :
  R.v2612 (state s) (inputs i) = Zmod.unsigned (N.v2612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2612 s i)) at 1.
  unfold R.v2612, N.v2612.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2613 (s : N.State) (i : N.Inputs) :
  R.v2613 (state s) (inputs i) = Zmod.unsigned (N.v2613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2613 s i)) at 1.
  unfold R.v2613, N.v2613.
  rewrite ?node_2612.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1065_nr_5F1065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1065_nr_5F1065 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2614 (s : N.State) (i : N.Inputs) :
  R.v2614 (state s) (inputs i) = Zmod.unsigned (N.v2614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2614 s i)) at 1.
  unfold R.v2614, N.v2614.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2615 (s : N.State) (i : N.Inputs) :
  R.v2615 (state s) (inputs i) = Zmod.unsigned (N.v2615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2615 s i)) at 1.
  unfold R.v2615, N.v2615.
  rewrite ?node_2614.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1066_nr_5F1066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1066_nr_5F1066 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2616 (s : N.State) (i : N.Inputs) :
  R.v2616 (state s) (inputs i) = Zmod.unsigned (N.v2616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2616 s i)) at 1.
  unfold R.v2616, N.v2616.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2617 (s : N.State) (i : N.Inputs) :
  R.v2617 (state s) (inputs i) = Zmod.unsigned (N.v2617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2617 s i)) at 1.
  unfold R.v2617, N.v2617.
  rewrite ?node_2616.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1067_nr_5F1067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1067_nr_5F1067 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2618 (s : N.State) (i : N.Inputs) :
  R.v2618 (state s) (inputs i) = Zmod.unsigned (N.v2618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2618 s i)) at 1.
  unfold R.v2618, N.v2618.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2619 (s : N.State) (i : N.Inputs) :
  R.v2619 (state s) (inputs i) = Zmod.unsigned (N.v2619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2619 s i)) at 1.
  unfold R.v2619, N.v2619.
  rewrite ?node_2618.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1068_nr_5F1068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1068_nr_5F1068 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2620 (s : N.State) (i : N.Inputs) :
  R.v2620 (state s) (inputs i) = Zmod.unsigned (N.v2620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2620 s i)) at 1.
  unfold R.v2620, N.v2620.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2621 (s : N.State) (i : N.Inputs) :
  R.v2621 (state s) (inputs i) = Zmod.unsigned (N.v2621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2621 s i)) at 1.
  unfold R.v2621, N.v2621.
  rewrite ?node_2620.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1069_nr_5F1069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1069_nr_5F1069 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2622 (s : N.State) (i : N.Inputs) :
  R.v2622 (state s) (inputs i) = Zmod.unsigned (N.v2622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2622 s i)) at 1.
  unfold R.v2622, N.v2622.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2623 (s : N.State) (i : N.Inputs) :
  R.v2623 (state s) (inputs i) = Zmod.unsigned (N.v2623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2623 s i)) at 1.
  unfold R.v2623, N.v2623.
  rewrite ?node_2622.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1070_nr_5F1070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1070_nr_5F1070 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2624 (s : N.State) (i : N.Inputs) :
  R.v2624 (state s) (inputs i) = Zmod.unsigned (N.v2624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2624 s i)) at 1.
  unfold R.v2624, N.v2624.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2625 (s : N.State) (i : N.Inputs) :
  R.v2625 (state s) (inputs i) = Zmod.unsigned (N.v2625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2625 s i)) at 1.
  unfold R.v2625, N.v2625.
  rewrite ?node_2624.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1071_nr_5F1071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1071_nr_5F1071 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2626 (s : N.State) (i : N.Inputs) :
  R.v2626 (state s) (inputs i) = Zmod.unsigned (N.v2626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2626 s i)) at 1.
  unfold R.v2626, N.v2626.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2627 (s : N.State) (i : N.Inputs) :
  R.v2627 (state s) (inputs i) = Zmod.unsigned (N.v2627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2627 s i)) at 1.
  unfold R.v2627, N.v2627.
  rewrite ?node_2626.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1072_nr_5F1072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1072_nr_5F1072 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2628 (s : N.State) (i : N.Inputs) :
  R.v2628 (state s) (inputs i) = Zmod.unsigned (N.v2628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2628 s i)) at 1.
  unfold R.v2628, N.v2628.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2629 (s : N.State) (i : N.Inputs) :
  R.v2629 (state s) (inputs i) = Zmod.unsigned (N.v2629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2629 s i)) at 1.
  unfold R.v2629, N.v2629.
  rewrite ?node_2628.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1073_nr_5F1073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1073_nr_5F1073 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2630 (s : N.State) (i : N.Inputs) :
  R.v2630 (state s) (inputs i) = Zmod.unsigned (N.v2630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2630 s i)) at 1.
  unfold R.v2630, N.v2630.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2631 (s : N.State) (i : N.Inputs) :
  R.v2631 (state s) (inputs i) = Zmod.unsigned (N.v2631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2631 s i)) at 1.
  unfold R.v2631, N.v2631.
  rewrite ?node_2630.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1074_nr_5F1074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1074_nr_5F1074 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2632 (s : N.State) (i : N.Inputs) :
  R.v2632 (state s) (inputs i) = Zmod.unsigned (N.v2632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2632 s i)) at 1.
  unfold R.v2632, N.v2632.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2633 (s : N.State) (i : N.Inputs) :
  R.v2633 (state s) (inputs i) = Zmod.unsigned (N.v2633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2633 s i)) at 1.
  unfold R.v2633, N.v2633.
  rewrite ?node_2632.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1075_nr_5F1075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1075_nr_5F1075 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2634 (s : N.State) (i : N.Inputs) :
  R.v2634 (state s) (inputs i) = Zmod.unsigned (N.v2634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2634 s i)) at 1.
  unfold R.v2634, N.v2634.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2635 (s : N.State) (i : N.Inputs) :
  R.v2635 (state s) (inputs i) = Zmod.unsigned (N.v2635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2635 s i)) at 1.
  unfold R.v2635, N.v2635.
  rewrite ?node_2634.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1076_nr_5F1076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1076_nr_5F1076 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2636 (s : N.State) (i : N.Inputs) :
  R.v2636 (state s) (inputs i) = Zmod.unsigned (N.v2636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2636 s i)) at 1.
  unfold R.v2636, N.v2636.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2637 (s : N.State) (i : N.Inputs) :
  R.v2637 (state s) (inputs i) = Zmod.unsigned (N.v2637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2637 s i)) at 1.
  unfold R.v2637, N.v2637.
  rewrite ?node_2636.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1077_nr_5F1077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1077_nr_5F1077 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2638 (s : N.State) (i : N.Inputs) :
  R.v2638 (state s) (inputs i) = Zmod.unsigned (N.v2638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2638 s i)) at 1.
  unfold R.v2638, N.v2638.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2639 (s : N.State) (i : N.Inputs) :
  R.v2639 (state s) (inputs i) = Zmod.unsigned (N.v2639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2639 s i)) at 1.
  unfold R.v2639, N.v2639.
  rewrite ?node_2638.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1078_nr_5F1078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1078_nr_5F1078 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2640 (s : N.State) (i : N.Inputs) :
  R.v2640 (state s) (inputs i) = Zmod.unsigned (N.v2640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2640 s i)) at 1.
  unfold R.v2640, N.v2640.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2641 (s : N.State) (i : N.Inputs) :
  R.v2641 (state s) (inputs i) = Zmod.unsigned (N.v2641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2641 s i)) at 1.
  unfold R.v2641, N.v2641.
  rewrite ?node_2640.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1079_nr_5F1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1079_nr_5F1079 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2642 (s : N.State) (i : N.Inputs) :
  R.v2642 (state s) (inputs i) = Zmod.unsigned (N.v2642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2642 s i)) at 1.
  unfold R.v2642, N.v2642.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2643 (s : N.State) (i : N.Inputs) :
  R.v2643 (state s) (inputs i) = Zmod.unsigned (N.v2643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2643 s i)) at 1.
  unfold R.v2643, N.v2643.
  rewrite ?node_2642.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1080_nr_5F1080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1080_nr_5F1080 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2644 (s : N.State) (i : N.Inputs) :
  R.v2644 (state s) (inputs i) = Zmod.unsigned (N.v2644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2644 s i)) at 1.
  unfold R.v2644, N.v2644.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2645 (s : N.State) (i : N.Inputs) :
  R.v2645 (state s) (inputs i) = Zmod.unsigned (N.v2645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2645 s i)) at 1.
  unfold R.v2645, N.v2645.
  rewrite ?node_2644.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1081_nr_5F1081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1081_nr_5F1081 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2646 (s : N.State) (i : N.Inputs) :
  R.v2646 (state s) (inputs i) = Zmod.unsigned (N.v2646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2646 s i)) at 1.
  unfold R.v2646, N.v2646.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2647 (s : N.State) (i : N.Inputs) :
  R.v2647 (state s) (inputs i) = Zmod.unsigned (N.v2647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2647 s i)) at 1.
  unfold R.v2647, N.v2647.
  rewrite ?node_2646.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1082_nr_5F1082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1082_nr_5F1082 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2648 (s : N.State) (i : N.Inputs) :
  R.v2648 (state s) (inputs i) = Zmod.unsigned (N.v2648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2648 s i)) at 1.
  unfold R.v2648, N.v2648.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2649 (s : N.State) (i : N.Inputs) :
  R.v2649 (state s) (inputs i) = Zmod.unsigned (N.v2649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2649 s i)) at 1.
  unfold R.v2649, N.v2649.
  rewrite ?node_2648.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1083_nr_5F1083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1083_nr_5F1083 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2650 (s : N.State) (i : N.Inputs) :
  R.v2650 (state s) (inputs i) = Zmod.unsigned (N.v2650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2650 s i)) at 1.
  unfold R.v2650, N.v2650.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2651 (s : N.State) (i : N.Inputs) :
  R.v2651 (state s) (inputs i) = Zmod.unsigned (N.v2651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2651 s i)) at 1.
  unfold R.v2651, N.v2651.
  rewrite ?node_2650.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1084_nr_5F1084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1084_nr_5F1084 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2652 (s : N.State) (i : N.Inputs) :
  R.v2652 (state s) (inputs i) = Zmod.unsigned (N.v2652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2652 s i)) at 1.
  unfold R.v2652, N.v2652.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2653 (s : N.State) (i : N.Inputs) :
  R.v2653 (state s) (inputs i) = Zmod.unsigned (N.v2653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2653 s i)) at 1.
  unfold R.v2653, N.v2653.
  unfold R.v33, N.v33.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2654 (s : N.State) (i : N.Inputs) :
  R.v2654 (state s) (inputs i) = Zmod.unsigned (N.v2654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2654 s i)) at 1.
  unfold R.v2654, N.v2654.
  unfold R.v35, N.v35.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2655 (s : N.State) (i : N.Inputs) :
  R.v2655 (state s) (inputs i) = Zmod.unsigned (N.v2655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2655 s i)) at 1.
  unfold R.v2655, N.v2655.
  rewrite ?node_2653.
  rewrite ?node_2654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2656 (s : N.State) (i : N.Inputs) :
  R.v2656 (state s) (inputs i) = Zmod.unsigned (N.v2656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2656 s i)) at 1.
  unfold R.v2656, N.v2656.
  unfold R.v39, N.v39.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2657 (s : N.State) (i : N.Inputs) :
  R.v2657 (state s) (inputs i) = Zmod.unsigned (N.v2657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2657 s i)) at 1.
  unfold R.v2657, N.v2657.
  unfold R.v42, N.v42.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2658 (s : N.State) (i : N.Inputs) :
  R.v2658 (state s) (inputs i) = Zmod.unsigned (N.v2658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2658 s i)) at 1.
  unfold R.v2658, N.v2658.
  unfold R.v45, N.v45.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2659 (s : N.State) (i : N.Inputs) :
  R.v2659 (state s) (inputs i) = Zmod.unsigned (N.v2659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2659 s i)) at 1.
  unfold R.v2659, N.v2659.
  unfold R.v47, N.v47.
  rewrite ?node_2652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2660 (s : N.State) (i : N.Inputs) :
  R.v2660 (state s) (inputs i) = Zmod.unsigned (N.v2660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2660 s i)) at 1.
  unfold R.v2660, N.v2660.
  rewrite ?node_2658.
  rewrite ?node_2659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2661 (s : N.State) (i : N.Inputs) :
  R.v2661 (state s) (inputs i) = Zmod.unsigned (N.v2661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2661 s i)) at 1.
  unfold R.v2661, N.v2661.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2662 (s : N.State) (i : N.Inputs) :
  R.v2662 (state s) (inputs i) = Zmod.unsigned (N.v2662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2662 s i)) at 1.
  unfold R.v2662, N.v2662.
  rewrite ?node_44.
  rewrite ?node_2657.
  rewrite ?node_2661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2663 (s : N.State) (i : N.Inputs) :
  R.v2663 (state s) (inputs i) = Zmod.unsigned (N.v2663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2663 s i)) at 1.
  unfold R.v2663, N.v2663.
  rewrite ?node_41.
  rewrite ?node_2656.
  rewrite ?node_2662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2664 (s : N.State) (i : N.Inputs) :
  R.v2664 (state s) (inputs i) = Zmod.unsigned (N.v2664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2664 s i)) at 1.
  unfold R.v2664, N.v2664.
  rewrite ?node_38.
  rewrite ?node_2655.
  rewrite ?node_2663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2665 (s : N.State) (i : N.Inputs) :
  R.v2665 (state s) (inputs i) = Zmod.unsigned (N.v2665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2665 s i)) at 1.
  unfold R.v2665, N.v2665.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2666 (s : N.State) (i : N.Inputs) :
  R.v2666 (state s) (inputs i) = Zmod.unsigned (N.v2666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2666 s i)) at 1.
  unfold R.v2666, N.v2666.
  rewrite ?node_2665.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1085_nr_5F1085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1085_nr_5F1085 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2667 (s : N.State) (i : N.Inputs) :
  R.v2667 (state s) (inputs i) = Zmod.unsigned (N.v2667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2667 s i)) at 1.
  unfold R.v2667, N.v2667.
  unfold R.v6, N.v6.
  rewrite ?node_2656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2668 (s : N.State) (i : N.Inputs) :
  R.v2668 (state s) (inputs i) = Zmod.unsigned (N.v2668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2668 s i)) at 1.
  unfold R.v2668, N.v2668.
  unfold R.v19, N.v19.
  rewrite ?node_2655.
  rewrite ?node_2667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2669 (s : N.State) (i : N.Inputs) :
  R.v2669 (state s) (inputs i) = Zmod.unsigned (N.v2669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2669 s i)) at 1.
  unfold R.v2669, N.v2669.
  rewrite ?node_2668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2670 (s : N.State) (i : N.Inputs) :
  R.v2670 (state s) (inputs i) = Zmod.unsigned (N.v2670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2670 s i)) at 1.
  unfold R.v2670, N.v2670.
  rewrite ?node_2669.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1086_nr_5F1086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1086_nr_5F1086 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2671 (s : N.State) (i : N.Inputs) :
  R.v2671 (state s) (inputs i) = Zmod.unsigned (N.v2671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2671 s i)) at 1.
  unfold R.v2671, N.v2671.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2672 (s : N.State) (i : N.Inputs) :
  R.v2672 (state s) (inputs i) = Zmod.unsigned (N.v2672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2672 s i)) at 1.
  unfold R.v2672, N.v2672.
  rewrite ?node_2671.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1087_nr_5F1087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1087_nr_5F1087 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2673 (s : N.State) (i : N.Inputs) :
  R.v2673 (state s) (inputs i) = Zmod.unsigned (N.v2673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2673 s i)) at 1.
  unfold R.v2673, N.v2673.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2674 (s : N.State) (i : N.Inputs) :
  R.v2674 (state s) (inputs i) = Zmod.unsigned (N.v2674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2674 s i)) at 1.
  unfold R.v2674, N.v2674.
  rewrite ?node_2673.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1088_nr_5F1088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1088_nr_5F1088 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2675 (s : N.State) (i : N.Inputs) :
  R.v2675 (state s) (inputs i) = Zmod.unsigned (N.v2675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2675 s i)) at 1.
  unfold R.v2675, N.v2675.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2676 (s : N.State) (i : N.Inputs) :
  R.v2676 (state s) (inputs i) = Zmod.unsigned (N.v2676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2676 s i)) at 1.
  unfold R.v2676, N.v2676.
  rewrite ?node_2675.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1089_nr_5F1089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1089_nr_5F1089 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2677 (s : N.State) (i : N.Inputs) :
  R.v2677 (state s) (inputs i) = Zmod.unsigned (N.v2677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2677 s i)) at 1.
  unfold R.v2677, N.v2677.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2678 (s : N.State) (i : N.Inputs) :
  R.v2678 (state s) (inputs i) = Zmod.unsigned (N.v2678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2678 s i)) at 1.
  unfold R.v2678, N.v2678.
  rewrite ?node_2677.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1090_nr_5F1090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1090_nr_5F1090 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2679 (s : N.State) (i : N.Inputs) :
  R.v2679 (state s) (inputs i) = Zmod.unsigned (N.v2679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2679 s i)) at 1.
  unfold R.v2679, N.v2679.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2680 (s : N.State) (i : N.Inputs) :
  R.v2680 (state s) (inputs i) = Zmod.unsigned (N.v2680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2680 s i)) at 1.
  unfold R.v2680, N.v2680.
  rewrite ?node_2679.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1091_nr_5F1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1091_nr_5F1091 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2681 (s : N.State) (i : N.Inputs) :
  R.v2681 (state s) (inputs i) = Zmod.unsigned (N.v2681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2681 s i)) at 1.
  unfold R.v2681, N.v2681.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2682 (s : N.State) (i : N.Inputs) :
  R.v2682 (state s) (inputs i) = Zmod.unsigned (N.v2682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2682 s i)) at 1.
  unfold R.v2682, N.v2682.
  rewrite ?node_2681.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1092_nr_5F1092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1092_nr_5F1092 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2683 (s : N.State) (i : N.Inputs) :
  R.v2683 (state s) (inputs i) = Zmod.unsigned (N.v2683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2683 s i)) at 1.
  unfold R.v2683, N.v2683.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2684 (s : N.State) (i : N.Inputs) :
  R.v2684 (state s) (inputs i) = Zmod.unsigned (N.v2684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2684 s i)) at 1.
  unfold R.v2684, N.v2684.
  rewrite ?node_2683.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1093_nr_5F1093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1093_nr_5F1093 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2685 (s : N.State) (i : N.Inputs) :
  R.v2685 (state s) (inputs i) = Zmod.unsigned (N.v2685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2685 s i)) at 1.
  unfold R.v2685, N.v2685.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2686 (s : N.State) (i : N.Inputs) :
  R.v2686 (state s) (inputs i) = Zmod.unsigned (N.v2686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2686 s i)) at 1.
  unfold R.v2686, N.v2686.
  rewrite ?node_2685.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1094_nr_5F1094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1094_nr_5F1094 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2687 (s : N.State) (i : N.Inputs) :
  R.v2687 (state s) (inputs i) = Zmod.unsigned (N.v2687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2687 s i)) at 1.
  unfold R.v2687, N.v2687.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2688 (s : N.State) (i : N.Inputs) :
  R.v2688 (state s) (inputs i) = Zmod.unsigned (N.v2688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2688 s i)) at 1.
  unfold R.v2688, N.v2688.
  rewrite ?node_2687.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1095_nr_5F1095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1095_nr_5F1095 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2689 (s : N.State) (i : N.Inputs) :
  R.v2689 (state s) (inputs i) = Zmod.unsigned (N.v2689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2689 s i)) at 1.
  unfold R.v2689, N.v2689.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2690 (s : N.State) (i : N.Inputs) :
  R.v2690 (state s) (inputs i) = Zmod.unsigned (N.v2690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2690 s i)) at 1.
  unfold R.v2690, N.v2690.
  rewrite ?node_2689.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1096_nr_5F1096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1096_nr_5F1096 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2691 (s : N.State) (i : N.Inputs) :
  R.v2691 (state s) (inputs i) = Zmod.unsigned (N.v2691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2691 s i)) at 1.
  unfold R.v2691, N.v2691.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2692 (s : N.State) (i : N.Inputs) :
  R.v2692 (state s) (inputs i) = Zmod.unsigned (N.v2692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2692 s i)) at 1.
  unfold R.v2692, N.v2692.
  rewrite ?node_2691.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1097_nr_5F1097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1097_nr_5F1097 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2693 (s : N.State) (i : N.Inputs) :
  R.v2693 (state s) (inputs i) = Zmod.unsigned (N.v2693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2693 s i)) at 1.
  unfold R.v2693, N.v2693.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2694 (s : N.State) (i : N.Inputs) :
  R.v2694 (state s) (inputs i) = Zmod.unsigned (N.v2694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2694 s i)) at 1.
  unfold R.v2694, N.v2694.
  rewrite ?node_2693.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1098_nr_5F1098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1098_nr_5F1098 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2695 (s : N.State) (i : N.Inputs) :
  R.v2695 (state s) (inputs i) = Zmod.unsigned (N.v2695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2695 s i)) at 1.
  unfold R.v2695, N.v2695.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2696 (s : N.State) (i : N.Inputs) :
  R.v2696 (state s) (inputs i) = Zmod.unsigned (N.v2696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2696 s i)) at 1.
  unfold R.v2696, N.v2696.
  rewrite ?node_2695.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1099_nr_5F1099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1099_nr_5F1099 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2697 (s : N.State) (i : N.Inputs) :
  R.v2697 (state s) (inputs i) = Zmod.unsigned (N.v2697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2697 s i)) at 1.
  unfold R.v2697, N.v2697.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2698 (s : N.State) (i : N.Inputs) :
  R.v2698 (state s) (inputs i) = Zmod.unsigned (N.v2698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2698 s i)) at 1.
  unfold R.v2698, N.v2698.
  rewrite ?node_2697.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1100_nr_5F1100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1100_nr_5F1100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2699 (s : N.State) (i : N.Inputs) :
  R.v2699 (state s) (inputs i) = Zmod.unsigned (N.v2699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2699 s i)) at 1.
  unfold R.v2699, N.v2699.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2700 (s : N.State) (i : N.Inputs) :
  R.v2700 (state s) (inputs i) = Zmod.unsigned (N.v2700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2700 s i)) at 1.
  unfold R.v2700, N.v2700.
  rewrite ?node_2699.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1101_nr_5F1101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1101_nr_5F1101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2701 (s : N.State) (i : N.Inputs) :
  R.v2701 (state s) (inputs i) = Zmod.unsigned (N.v2701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2701 s i)) at 1.
  unfold R.v2701, N.v2701.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2702 (s : N.State) (i : N.Inputs) :
  R.v2702 (state s) (inputs i) = Zmod.unsigned (N.v2702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2702 s i)) at 1.
  unfold R.v2702, N.v2702.
  rewrite ?node_2701.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1102_nr_5F1102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1102_nr_5F1102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2703 (s : N.State) (i : N.Inputs) :
  R.v2703 (state s) (inputs i) = Zmod.unsigned (N.v2703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2703 s i)) at 1.
  unfold R.v2703, N.v2703.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2704 (s : N.State) (i : N.Inputs) :
  R.v2704 (state s) (inputs i) = Zmod.unsigned (N.v2704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2704 s i)) at 1.
  unfold R.v2704, N.v2704.
  rewrite ?node_2703.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1103_nr_5F1103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1103_nr_5F1103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2705 (s : N.State) (i : N.Inputs) :
  R.v2705 (state s) (inputs i) = Zmod.unsigned (N.v2705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2705 s i)) at 1.
  unfold R.v2705, N.v2705.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2706 (s : N.State) (i : N.Inputs) :
  R.v2706 (state s) (inputs i) = Zmod.unsigned (N.v2706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2706 s i)) at 1.
  unfold R.v2706, N.v2706.
  rewrite ?node_2705.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1104_nr_5F1104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1104_nr_5F1104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2707 (s : N.State) (i : N.Inputs) :
  R.v2707 (state s) (inputs i) = Zmod.unsigned (N.v2707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2707 s i)) at 1.
  unfold R.v2707, N.v2707.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2708 (s : N.State) (i : N.Inputs) :
  R.v2708 (state s) (inputs i) = Zmod.unsigned (N.v2708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2708 s i)) at 1.
  unfold R.v2708, N.v2708.
  rewrite ?node_2707.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1105_nr_5F1105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1105_nr_5F1105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2709 (s : N.State) (i : N.Inputs) :
  R.v2709 (state s) (inputs i) = Zmod.unsigned (N.v2709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2709 s i)) at 1.
  unfold R.v2709, N.v2709.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2710 (s : N.State) (i : N.Inputs) :
  R.v2710 (state s) (inputs i) = Zmod.unsigned (N.v2710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2710 s i)) at 1.
  unfold R.v2710, N.v2710.
  rewrite ?node_2709.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1106_nr_5F1106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1106_nr_5F1106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2711 (s : N.State) (i : N.Inputs) :
  R.v2711 (state s) (inputs i) = Zmod.unsigned (N.v2711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2711 s i)) at 1.
  unfold R.v2711, N.v2711.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2712 (s : N.State) (i : N.Inputs) :
  R.v2712 (state s) (inputs i) = Zmod.unsigned (N.v2712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2712 s i)) at 1.
  unfold R.v2712, N.v2712.
  rewrite ?node_2711.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1107_nr_5F1107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1107_nr_5F1107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2713 (s : N.State) (i : N.Inputs) :
  R.v2713 (state s) (inputs i) = Zmod.unsigned (N.v2713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2713 s i)) at 1.
  unfold R.v2713, N.v2713.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2714 (s : N.State) (i : N.Inputs) :
  R.v2714 (state s) (inputs i) = Zmod.unsigned (N.v2714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2714 s i)) at 1.
  unfold R.v2714, N.v2714.
  rewrite ?node_2713.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1108_nr_5F1108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1108_nr_5F1108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2715 (s : N.State) (i : N.Inputs) :
  R.v2715 (state s) (inputs i) = Zmod.unsigned (N.v2715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2715 s i)) at 1.
  unfold R.v2715, N.v2715.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2716 (s : N.State) (i : N.Inputs) :
  R.v2716 (state s) (inputs i) = Zmod.unsigned (N.v2716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2716 s i)) at 1.
  unfold R.v2716, N.v2716.
  rewrite ?node_2715.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1109_nr_5F1109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1109_nr_5F1109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2717 (s : N.State) (i : N.Inputs) :
  R.v2717 (state s) (inputs i) = Zmod.unsigned (N.v2717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2717 s i)) at 1.
  unfold R.v2717, N.v2717.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2718 (s : N.State) (i : N.Inputs) :
  R.v2718 (state s) (inputs i) = Zmod.unsigned (N.v2718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2718 s i)) at 1.
  unfold R.v2718, N.v2718.
  rewrite ?node_2717.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1110_nr_5F1110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1110_nr_5F1110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2719 (s : N.State) (i : N.Inputs) :
  R.v2719 (state s) (inputs i) = Zmod.unsigned (N.v2719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2719 s i)) at 1.
  unfold R.v2719, N.v2719.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2720 (s : N.State) (i : N.Inputs) :
  R.v2720 (state s) (inputs i) = Zmod.unsigned (N.v2720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2720 s i)) at 1.
  unfold R.v2720, N.v2720.
  rewrite ?node_2719.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1111_nr_5F1111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1111_nr_5F1111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2721 (s : N.State) (i : N.Inputs) :
  R.v2721 (state s) (inputs i) = Zmod.unsigned (N.v2721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2721 s i)) at 1.
  unfold R.v2721, N.v2721.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2722 (s : N.State) (i : N.Inputs) :
  R.v2722 (state s) (inputs i) = Zmod.unsigned (N.v2722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2722 s i)) at 1.
  unfold R.v2722, N.v2722.
  rewrite ?node_2721.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1112_nr_5F1112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1112_nr_5F1112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2723 (s : N.State) (i : N.Inputs) :
  R.v2723 (state s) (inputs i) = Zmod.unsigned (N.v2723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2723 s i)) at 1.
  unfold R.v2723, N.v2723.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2724 (s : N.State) (i : N.Inputs) :
  R.v2724 (state s) (inputs i) = Zmod.unsigned (N.v2724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2724 s i)) at 1.
  unfold R.v2724, N.v2724.
  rewrite ?node_2723.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1113_nr_5F1113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1113_nr_5F1113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2725 (s : N.State) (i : N.Inputs) :
  R.v2725 (state s) (inputs i) = Zmod.unsigned (N.v2725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2725 s i)) at 1.
  unfold R.v2725, N.v2725.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2726 (s : N.State) (i : N.Inputs) :
  R.v2726 (state s) (inputs i) = Zmod.unsigned (N.v2726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2726 s i)) at 1.
  unfold R.v2726, N.v2726.
  rewrite ?node_2725.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1114_nr_5F1114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1114_nr_5F1114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2727 (s : N.State) (i : N.Inputs) :
  R.v2727 (state s) (inputs i) = Zmod.unsigned (N.v2727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2727 s i)) at 1.
  unfold R.v2727, N.v2727.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2728 (s : N.State) (i : N.Inputs) :
  R.v2728 (state s) (inputs i) = Zmod.unsigned (N.v2728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2728 s i)) at 1.
  unfold R.v2728, N.v2728.
  rewrite ?node_2727.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1115_nr_5F1115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1115_nr_5F1115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2729 (s : N.State) (i : N.Inputs) :
  R.v2729 (state s) (inputs i) = Zmod.unsigned (N.v2729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2729 s i)) at 1.
  unfold R.v2729, N.v2729.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2730 (s : N.State) (i : N.Inputs) :
  R.v2730 (state s) (inputs i) = Zmod.unsigned (N.v2730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2730 s i)) at 1.
  unfold R.v2730, N.v2730.
  rewrite ?node_2729.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1116_nr_5F1116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1116_nr_5F1116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2731 (s : N.State) (i : N.Inputs) :
  R.v2731 (state s) (inputs i) = Zmod.unsigned (N.v2731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2731 s i)) at 1.
  unfold R.v2731, N.v2731.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2732 (s : N.State) (i : N.Inputs) :
  R.v2732 (state s) (inputs i) = Zmod.unsigned (N.v2732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2732 s i)) at 1.
  unfold R.v2732, N.v2732.
  rewrite ?node_2731.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1117_nr_5F1117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1117_nr_5F1117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2733 (s : N.State) (i : N.Inputs) :
  R.v2733 (state s) (inputs i) = Zmod.unsigned (N.v2733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2733 s i)) at 1.
  unfold R.v2733, N.v2733.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2734 (s : N.State) (i : N.Inputs) :
  R.v2734 (state s) (inputs i) = Zmod.unsigned (N.v2734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2734 s i)) at 1.
  unfold R.v2734, N.v2734.
  rewrite ?node_2733.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1118_nr_5F1118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1118_nr_5F1118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2735 (s : N.State) (i : N.Inputs) :
  R.v2735 (state s) (inputs i) = Zmod.unsigned (N.v2735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2735 s i)) at 1.
  unfold R.v2735, N.v2735.
  rewrite ?node_2668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2736 (s : N.State) (i : N.Inputs) :
  R.v2736 (state s) (inputs i) = Zmod.unsigned (N.v2736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2736 s i)) at 1.
  unfold R.v2736, N.v2736.
  rewrite ?node_2735.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1119_nr_5F1119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1119_nr_5F1119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2737 (s : N.State) (i : N.Inputs) :
  R.v2737 (state s) (inputs i) = Zmod.unsigned (N.v2737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2737 s i)) at 1.
  unfold R.v2737, N.v2737.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2738 (s : N.State) (i : N.Inputs) :
  R.v2738 (state s) (inputs i) = Zmod.unsigned (N.v2738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2738 s i)) at 1.
  unfold R.v2738, N.v2738.
  rewrite ?node_2737.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1120_nr_5F1120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1120_nr_5F1120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2739 (s : N.State) (i : N.Inputs) :
  R.v2739 (state s) (inputs i) = Zmod.unsigned (N.v2739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2739 s i)) at 1.
  unfold R.v2739, N.v2739.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2740 (s : N.State) (i : N.Inputs) :
  R.v2740 (state s) (inputs i) = Zmod.unsigned (N.v2740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2740 s i)) at 1.
  unfold R.v2740, N.v2740.
  rewrite ?node_2739.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1121_nr_5F1121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1121_nr_5F1121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2741 (s : N.State) (i : N.Inputs) :
  R.v2741 (state s) (inputs i) = Zmod.unsigned (N.v2741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2741 s i)) at 1.
  unfold R.v2741, N.v2741.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2742 (s : N.State) (i : N.Inputs) :
  R.v2742 (state s) (inputs i) = Zmod.unsigned (N.v2742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2742 s i)) at 1.
  unfold R.v2742, N.v2742.
  rewrite ?node_2741.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1122_nr_5F1122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1122_nr_5F1122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2743 (s : N.State) (i : N.Inputs) :
  R.v2743 (state s) (inputs i) = Zmod.unsigned (N.v2743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2743 s i)) at 1.
  unfold R.v2743, N.v2743.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2744 (s : N.State) (i : N.Inputs) :
  R.v2744 (state s) (inputs i) = Zmod.unsigned (N.v2744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2744 s i)) at 1.
  unfold R.v2744, N.v2744.
  rewrite ?node_2743.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1123_nr_5F1123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1123_nr_5F1123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2745 (s : N.State) (i : N.Inputs) :
  R.v2745 (state s) (inputs i) = Zmod.unsigned (N.v2745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2745 s i)) at 1.
  unfold R.v2745, N.v2745.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2746 (s : N.State) (i : N.Inputs) :
  R.v2746 (state s) (inputs i) = Zmod.unsigned (N.v2746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2746 s i)) at 1.
  unfold R.v2746, N.v2746.
  rewrite ?node_2745.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1124_nr_5F1124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1124_nr_5F1124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2747 (s : N.State) (i : N.Inputs) :
  R.v2747 (state s) (inputs i) = Zmod.unsigned (N.v2747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2747 s i)) at 1.
  unfold R.v2747, N.v2747.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2748 (s : N.State) (i : N.Inputs) :
  R.v2748 (state s) (inputs i) = Zmod.unsigned (N.v2748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2748 s i)) at 1.
  unfold R.v2748, N.v2748.
  rewrite ?node_2747.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1125_nr_5F1125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1125_nr_5F1125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2749 (s : N.State) (i : N.Inputs) :
  R.v2749 (state s) (inputs i) = Zmod.unsigned (N.v2749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2749 s i)) at 1.
  unfold R.v2749, N.v2749.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2750 (s : N.State) (i : N.Inputs) :
  R.v2750 (state s) (inputs i) = Zmod.unsigned (N.v2750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2750 s i)) at 1.
  unfold R.v2750, N.v2750.
  rewrite ?node_2749.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1126_nr_5F1126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1126_nr_5F1126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2751 (s : N.State) (i : N.Inputs) :
  R.v2751 (state s) (inputs i) = Zmod.unsigned (N.v2751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2751 s i)) at 1.
  unfold R.v2751, N.v2751.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2752 (s : N.State) (i : N.Inputs) :
  R.v2752 (state s) (inputs i) = Zmod.unsigned (N.v2752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2752 s i)) at 1.
  unfold R.v2752, N.v2752.
  rewrite ?node_2751.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1127_nr_5F1127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1127_nr_5F1127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2753 (s : N.State) (i : N.Inputs) :
  R.v2753 (state s) (inputs i) = Zmod.unsigned (N.v2753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2753 s i)) at 1.
  unfold R.v2753, N.v2753.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2754 (s : N.State) (i : N.Inputs) :
  R.v2754 (state s) (inputs i) = Zmod.unsigned (N.v2754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2754 s i)) at 1.
  unfold R.v2754, N.v2754.
  rewrite ?node_2753.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1128_nr_5F1128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1128_nr_5F1128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2755 (s : N.State) (i : N.Inputs) :
  R.v2755 (state s) (inputs i) = Zmod.unsigned (N.v2755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2755 s i)) at 1.
  unfold R.v2755, N.v2755.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2756 (s : N.State) (i : N.Inputs) :
  R.v2756 (state s) (inputs i) = Zmod.unsigned (N.v2756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2756 s i)) at 1.
  unfold R.v2756, N.v2756.
  rewrite ?node_2755.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1129_nr_5F1129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1129_nr_5F1129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2757 (s : N.State) (i : N.Inputs) :
  R.v2757 (state s) (inputs i) = Zmod.unsigned (N.v2757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2757 s i)) at 1.
  unfold R.v2757, N.v2757.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2758 (s : N.State) (i : N.Inputs) :
  R.v2758 (state s) (inputs i) = Zmod.unsigned (N.v2758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2758 s i)) at 1.
  unfold R.v2758, N.v2758.
  rewrite ?node_2757.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1130_nr_5F1130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1130_nr_5F1130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2759 (s : N.State) (i : N.Inputs) :
  R.v2759 (state s) (inputs i) = Zmod.unsigned (N.v2759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2759 s i)) at 1.
  unfold R.v2759, N.v2759.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2760 (s : N.State) (i : N.Inputs) :
  R.v2760 (state s) (inputs i) = Zmod.unsigned (N.v2760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2760 s i)) at 1.
  unfold R.v2760, N.v2760.
  rewrite ?node_2759.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1131_nr_5F1131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1131_nr_5F1131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2761 (s : N.State) (i : N.Inputs) :
  R.v2761 (state s) (inputs i) = Zmod.unsigned (N.v2761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2761 s i)) at 1.
  unfold R.v2761, N.v2761.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2762 (s : N.State) (i : N.Inputs) :
  R.v2762 (state s) (inputs i) = Zmod.unsigned (N.v2762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2762 s i)) at 1.
  unfold R.v2762, N.v2762.
  rewrite ?node_2761.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1132_nr_5F1132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1132_nr_5F1132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2763 (s : N.State) (i : N.Inputs) :
  R.v2763 (state s) (inputs i) = Zmod.unsigned (N.v2763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2763 s i)) at 1.
  unfold R.v2763, N.v2763.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2764 (s : N.State) (i : N.Inputs) :
  R.v2764 (state s) (inputs i) = Zmod.unsigned (N.v2764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2764 s i)) at 1.
  unfold R.v2764, N.v2764.
  rewrite ?node_2763.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1133_nr_5F1133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1133_nr_5F1133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2765 (s : N.State) (i : N.Inputs) :
  R.v2765 (state s) (inputs i) = Zmod.unsigned (N.v2765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2765 s i)) at 1.
  unfold R.v2765, N.v2765.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2766 (s : N.State) (i : N.Inputs) :
  R.v2766 (state s) (inputs i) = Zmod.unsigned (N.v2766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2766 s i)) at 1.
  unfold R.v2766, N.v2766.
  rewrite ?node_2765.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1134_nr_5F1134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1134_nr_5F1134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2767 (s : N.State) (i : N.Inputs) :
  R.v2767 (state s) (inputs i) = Zmod.unsigned (N.v2767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2767 s i)) at 1.
  unfold R.v2767, N.v2767.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2768 (s : N.State) (i : N.Inputs) :
  R.v2768 (state s) (inputs i) = Zmod.unsigned (N.v2768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2768 s i)) at 1.
  unfold R.v2768, N.v2768.
  rewrite ?node_2767.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1135_nr_5F1135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1135_nr_5F1135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2769 (s : N.State) (i : N.Inputs) :
  R.v2769 (state s) (inputs i) = Zmod.unsigned (N.v2769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2769 s i)) at 1.
  unfold R.v2769, N.v2769.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2770 (s : N.State) (i : N.Inputs) :
  R.v2770 (state s) (inputs i) = Zmod.unsigned (N.v2770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2770 s i)) at 1.
  unfold R.v2770, N.v2770.
  rewrite ?node_2769.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1136_nr_5F1136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1136_nr_5F1136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2771 (s : N.State) (i : N.Inputs) :
  R.v2771 (state s) (inputs i) = Zmod.unsigned (N.v2771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2771 s i)) at 1.
  unfold R.v2771, N.v2771.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2772 (s : N.State) (i : N.Inputs) :
  R.v2772 (state s) (inputs i) = Zmod.unsigned (N.v2772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2772 s i)) at 1.
  unfold R.v2772, N.v2772.
  rewrite ?node_2771.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1137_nr_5F1137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1137_nr_5F1137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2773 (s : N.State) (i : N.Inputs) :
  R.v2773 (state s) (inputs i) = Zmod.unsigned (N.v2773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2773 s i)) at 1.
  unfold R.v2773, N.v2773.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2774 (s : N.State) (i : N.Inputs) :
  R.v2774 (state s) (inputs i) = Zmod.unsigned (N.v2774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2774 s i)) at 1.
  unfold R.v2774, N.v2774.
  rewrite ?node_2773.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1138_nr_5F1138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1138_nr_5F1138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2775 (s : N.State) (i : N.Inputs) :
  R.v2775 (state s) (inputs i) = Zmod.unsigned (N.v2775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2775 s i)) at 1.
  unfold R.v2775, N.v2775.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2776 (s : N.State) (i : N.Inputs) :
  R.v2776 (state s) (inputs i) = Zmod.unsigned (N.v2776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2776 s i)) at 1.
  unfold R.v2776, N.v2776.
  rewrite ?node_2775.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1139_nr_5F1139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1139_nr_5F1139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2777 (s : N.State) (i : N.Inputs) :
  R.v2777 (state s) (inputs i) = Zmod.unsigned (N.v2777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2777 s i)) at 1.
  unfold R.v2777, N.v2777.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2778 (s : N.State) (i : N.Inputs) :
  R.v2778 (state s) (inputs i) = Zmod.unsigned (N.v2778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2778 s i)) at 1.
  unfold R.v2778, N.v2778.
  rewrite ?node_2777.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1140_nr_5F1140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1140_nr_5F1140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2779 (s : N.State) (i : N.Inputs) :
  R.v2779 (state s) (inputs i) = Zmod.unsigned (N.v2779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2779 s i)) at 1.
  unfold R.v2779, N.v2779.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2780 (s : N.State) (i : N.Inputs) :
  R.v2780 (state s) (inputs i) = Zmod.unsigned (N.v2780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2780 s i)) at 1.
  unfold R.v2780, N.v2780.
  rewrite ?node_2779.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1141_nr_5F1141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1141_nr_5F1141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2781 (s : N.State) (i : N.Inputs) :
  R.v2781 (state s) (inputs i) = Zmod.unsigned (N.v2781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2781 s i)) at 1.
  unfold R.v2781, N.v2781.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2782 (s : N.State) (i : N.Inputs) :
  R.v2782 (state s) (inputs i) = Zmod.unsigned (N.v2782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2782 s i)) at 1.
  unfold R.v2782, N.v2782.
  rewrite ?node_2781.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1142_nr_5F1142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1142_nr_5F1142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2783 (s : N.State) (i : N.Inputs) :
  R.v2783 (state s) (inputs i) = Zmod.unsigned (N.v2783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2783 s i)) at 1.
  unfold R.v2783, N.v2783.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2784 (s : N.State) (i : N.Inputs) :
  R.v2784 (state s) (inputs i) = Zmod.unsigned (N.v2784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2784 s i)) at 1.
  unfold R.v2784, N.v2784.
  rewrite ?node_2783.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1143_nr_5F1143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1143_nr_5F1143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2785 (s : N.State) (i : N.Inputs) :
  R.v2785 (state s) (inputs i) = Zmod.unsigned (N.v2785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2785 s i)) at 1.
  unfold R.v2785, N.v2785.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2786 (s : N.State) (i : N.Inputs) :
  R.v2786 (state s) (inputs i) = Zmod.unsigned (N.v2786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2786 s i)) at 1.
  unfold R.v2786, N.v2786.
  rewrite ?node_2785.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1144_nr_5F1144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1144_nr_5F1144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2787 (s : N.State) (i : N.Inputs) :
  R.v2787 (state s) (inputs i) = Zmod.unsigned (N.v2787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2787 s i)) at 1.
  unfold R.v2787, N.v2787.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2788 (s : N.State) (i : N.Inputs) :
  R.v2788 (state s) (inputs i) = Zmod.unsigned (N.v2788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2788 s i)) at 1.
  unfold R.v2788, N.v2788.
  rewrite ?node_2787.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1145_nr_5F1145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1145_nr_5F1145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2789 (s : N.State) (i : N.Inputs) :
  R.v2789 (state s) (inputs i) = Zmod.unsigned (N.v2789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2789 s i)) at 1.
  unfold R.v2789, N.v2789.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2790 (s : N.State) (i : N.Inputs) :
  R.v2790 (state s) (inputs i) = Zmod.unsigned (N.v2790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2790 s i)) at 1.
  unfold R.v2790, N.v2790.
  rewrite ?node_2789.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1146_nr_5F1146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1146_nr_5F1146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2791 (s : N.State) (i : N.Inputs) :
  R.v2791 (state s) (inputs i) = Zmod.unsigned (N.v2791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2791 s i)) at 1.
  unfold R.v2791, N.v2791.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2792 (s : N.State) (i : N.Inputs) :
  R.v2792 (state s) (inputs i) = Zmod.unsigned (N.v2792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2792 s i)) at 1.
  unfold R.v2792, N.v2792.
  rewrite ?node_2791.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1147_nr_5F1147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1147_nr_5F1147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2793 (s : N.State) (i : N.Inputs) :
  R.v2793 (state s) (inputs i) = Zmod.unsigned (N.v2793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2793 s i)) at 1.
  unfold R.v2793, N.v2793.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2794 (s : N.State) (i : N.Inputs) :
  R.v2794 (state s) (inputs i) = Zmod.unsigned (N.v2794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2794 s i)) at 1.
  unfold R.v2794, N.v2794.
  rewrite ?node_2793.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1148_nr_5F1148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1148_nr_5F1148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2795 (s : N.State) (i : N.Inputs) :
  R.v2795 (state s) (inputs i) = Zmod.unsigned (N.v2795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2795 s i)) at 1.
  unfold R.v2795, N.v2795.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2796 (s : N.State) (i : N.Inputs) :
  R.v2796 (state s) (inputs i) = Zmod.unsigned (N.v2796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2796 s i)) at 1.
  unfold R.v2796, N.v2796.
  rewrite ?node_2795.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1149_nr_5F1149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1149_nr_5F1149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2797 (s : N.State) (i : N.Inputs) :
  R.v2797 (state s) (inputs i) = Zmod.unsigned (N.v2797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2797 s i)) at 1.
  unfold R.v2797, N.v2797.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2798 (s : N.State) (i : N.Inputs) :
  R.v2798 (state s) (inputs i) = Zmod.unsigned (N.v2798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2798 s i)) at 1.
  unfold R.v2798, N.v2798.
  rewrite ?node_2797.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1150_nr_5F1150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1150_nr_5F1150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2799 (s : N.State) (i : N.Inputs) :
  R.v2799 (state s) (inputs i) = Zmod.unsigned (N.v2799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2799 s i)) at 1.
  unfold R.v2799, N.v2799.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2800 (s : N.State) (i : N.Inputs) :
  R.v2800 (state s) (inputs i) = Zmod.unsigned (N.v2800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2800 s i)) at 1.
  unfold R.v2800, N.v2800.
  rewrite ?node_2799.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1151_nr_5F1151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1151_nr_5F1151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2801 (s : N.State) (i : N.Inputs) :
  R.v2801 (state s) (inputs i) = Zmod.unsigned (N.v2801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2801 s i)) at 1.
  unfold R.v2801, N.v2801.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2802 (s : N.State) (i : N.Inputs) :
  R.v2802 (state s) (inputs i) = Zmod.unsigned (N.v2802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2802 s i)) at 1.
  unfold R.v2802, N.v2802.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2803 (s : N.State) (i : N.Inputs) :
  R.v2803 (state s) (inputs i) = Zmod.unsigned (N.v2803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2803 s i)) at 1.
  unfold R.v2803, N.v2803.
  rewrite ?node_2801.
  rewrite ?node_2802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2804 (s : N.State) (i : N.Inputs) :
  R.v2804 (state s) (inputs i) = Zmod.unsigned (N.v2804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2804 s i)) at 1.
  unfold R.v2804, N.v2804.
  unfold R.v33, N.v33.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2805 (s : N.State) (i : N.Inputs) :
  R.v2805 (state s) (inputs i) = Zmod.unsigned (N.v2805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2805 s i)) at 1.
  unfold R.v2805, N.v2805.
  unfold R.v35, N.v35.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2806 (s : N.State) (i : N.Inputs) :
  R.v2806 (state s) (inputs i) = Zmod.unsigned (N.v2806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2806 s i)) at 1.
  unfold R.v2806, N.v2806.
  rewrite ?node_2804.
  rewrite ?node_2805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2807 (s : N.State) (i : N.Inputs) :
  R.v2807 (state s) (inputs i) = Zmod.unsigned (N.v2807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2807 s i)) at 1.
  unfold R.v2807, N.v2807.
  unfold R.v39, N.v39.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2808 (s : N.State) (i : N.Inputs) :
  R.v2808 (state s) (inputs i) = Zmod.unsigned (N.v2808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2808 s i)) at 1.
  unfold R.v2808, N.v2808.
  unfold R.v42, N.v42.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2809 (s : N.State) (i : N.Inputs) :
  R.v2809 (state s) (inputs i) = Zmod.unsigned (N.v2809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2809 s i)) at 1.
  unfold R.v2809, N.v2809.
  unfold R.v45, N.v45.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2810 (s : N.State) (i : N.Inputs) :
  R.v2810 (state s) (inputs i) = Zmod.unsigned (N.v2810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2810 s i)) at 1.
  unfold R.v2810, N.v2810.
  unfold R.v47, N.v47.
  rewrite ?node_2803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2811 (s : N.State) (i : N.Inputs) :
  R.v2811 (state s) (inputs i) = Zmod.unsigned (N.v2811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2811 s i)) at 1.
  unfold R.v2811, N.v2811.
  rewrite ?node_2809.
  rewrite ?node_2810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2812 (s : N.State) (i : N.Inputs) :
  R.v2812 (state s) (inputs i) = Zmod.unsigned (N.v2812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2812 s i)) at 1.
  unfold R.v2812, N.v2812.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_2811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2813 (s : N.State) (i : N.Inputs) :
  R.v2813 (state s) (inputs i) = Zmod.unsigned (N.v2813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2813 s i)) at 1.
  unfold R.v2813, N.v2813.
  rewrite ?node_44.
  rewrite ?node_2808.
  rewrite ?node_2812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2814 (s : N.State) (i : N.Inputs) :
  R.v2814 (state s) (inputs i) = Zmod.unsigned (N.v2814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2814 s i)) at 1.
  unfold R.v2814, N.v2814.
  rewrite ?node_41.
  rewrite ?node_2807.
  rewrite ?node_2813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2815 (s : N.State) (i : N.Inputs) :
  R.v2815 (state s) (inputs i) = Zmod.unsigned (N.v2815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2815 s i)) at 1.
  unfold R.v2815, N.v2815.
  rewrite ?node_38.
  rewrite ?node_2806.
  rewrite ?node_2814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2816 (s : N.State) (i : N.Inputs) :
  R.v2816 (state s) (inputs i) = Zmod.unsigned (N.v2816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2816 s i)) at 1.
  unfold R.v2816, N.v2816.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2817 (s : N.State) (i : N.Inputs) :
  R.v2817 (state s) (inputs i) = Zmod.unsigned (N.v2817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2817 s i)) at 1.
  unfold R.v2817, N.v2817.
  rewrite ?node_2816.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1152_nr_5F1152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1152_nr_5F1152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2818 (s : N.State) (i : N.Inputs) :
  R.v2818 (state s) (inputs i) = Zmod.unsigned (N.v2818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2818 s i)) at 1.
  unfold R.v2818, N.v2818.
  unfold R.v6, N.v6.
  rewrite ?node_2807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2819 (s : N.State) (i : N.Inputs) :
  R.v2819 (state s) (inputs i) = Zmod.unsigned (N.v2819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2819 s i)) at 1.
  unfold R.v2819, N.v2819.
  unfold R.v19, N.v19.
  rewrite ?node_2806.
  rewrite ?node_2818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2820 (s : N.State) (i : N.Inputs) :
  R.v2820 (state s) (inputs i) = Zmod.unsigned (N.v2820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2820 s i)) at 1.
  unfold R.v2820, N.v2820.
  rewrite ?node_2819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2821 (s : N.State) (i : N.Inputs) :
  R.v2821 (state s) (inputs i) = Zmod.unsigned (N.v2821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2821 s i)) at 1.
  unfold R.v2821, N.v2821.
  rewrite ?node_2820.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1153_nr_5F1153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1153_nr_5F1153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2822 (s : N.State) (i : N.Inputs) :
  R.v2822 (state s) (inputs i) = Zmod.unsigned (N.v2822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2822 s i)) at 1.
  unfold R.v2822, N.v2822.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2823 (s : N.State) (i : N.Inputs) :
  R.v2823 (state s) (inputs i) = Zmod.unsigned (N.v2823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2823 s i)) at 1.
  unfold R.v2823, N.v2823.
  rewrite ?node_2822.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1154_nr_5F1154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1154_nr_5F1154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2824 (s : N.State) (i : N.Inputs) :
  R.v2824 (state s) (inputs i) = Zmod.unsigned (N.v2824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2824 s i)) at 1.
  unfold R.v2824, N.v2824.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2825 (s : N.State) (i : N.Inputs) :
  R.v2825 (state s) (inputs i) = Zmod.unsigned (N.v2825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2825 s i)) at 1.
  unfold R.v2825, N.v2825.
  rewrite ?node_2824.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1155_nr_5F1155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1155_nr_5F1155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2826 (s : N.State) (i : N.Inputs) :
  R.v2826 (state s) (inputs i) = Zmod.unsigned (N.v2826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2826 s i)) at 1.
  unfold R.v2826, N.v2826.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2827 (s : N.State) (i : N.Inputs) :
  R.v2827 (state s) (inputs i) = Zmod.unsigned (N.v2827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2827 s i)) at 1.
  unfold R.v2827, N.v2827.
  rewrite ?node_2826.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1156_nr_5F1156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1156_nr_5F1156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2828 (s : N.State) (i : N.Inputs) :
  R.v2828 (state s) (inputs i) = Zmod.unsigned (N.v2828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2828 s i)) at 1.
  unfold R.v2828, N.v2828.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2829 (s : N.State) (i : N.Inputs) :
  R.v2829 (state s) (inputs i) = Zmod.unsigned (N.v2829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2829 s i)) at 1.
  unfold R.v2829, N.v2829.
  rewrite ?node_2828.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1157_nr_5F1157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1157_nr_5F1157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2830 (s : N.State) (i : N.Inputs) :
  R.v2830 (state s) (inputs i) = Zmod.unsigned (N.v2830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2830 s i)) at 1.
  unfold R.v2830, N.v2830.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2831 (s : N.State) (i : N.Inputs) :
  R.v2831 (state s) (inputs i) = Zmod.unsigned (N.v2831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2831 s i)) at 1.
  unfold R.v2831, N.v2831.
  rewrite ?node_2830.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1158_nr_5F1158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1158_nr_5F1158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2832 (s : N.State) (i : N.Inputs) :
  R.v2832 (state s) (inputs i) = Zmod.unsigned (N.v2832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2832 s i)) at 1.
  unfold R.v2832, N.v2832.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2833 (s : N.State) (i : N.Inputs) :
  R.v2833 (state s) (inputs i) = Zmod.unsigned (N.v2833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2833 s i)) at 1.
  unfold R.v2833, N.v2833.
  rewrite ?node_2832.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1159_nr_5F1159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1159_nr_5F1159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2834 (s : N.State) (i : N.Inputs) :
  R.v2834 (state s) (inputs i) = Zmod.unsigned (N.v2834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2834 s i)) at 1.
  unfold R.v2834, N.v2834.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2835 (s : N.State) (i : N.Inputs) :
  R.v2835 (state s) (inputs i) = Zmod.unsigned (N.v2835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2835 s i)) at 1.
  unfold R.v2835, N.v2835.
  rewrite ?node_2834.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1160_nr_5F1160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1160_nr_5F1160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2836 (s : N.State) (i : N.Inputs) :
  R.v2836 (state s) (inputs i) = Zmod.unsigned (N.v2836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2836 s i)) at 1.
  unfold R.v2836, N.v2836.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2837 (s : N.State) (i : N.Inputs) :
  R.v2837 (state s) (inputs i) = Zmod.unsigned (N.v2837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2837 s i)) at 1.
  unfold R.v2837, N.v2837.
  rewrite ?node_2836.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1161_nr_5F1161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1161_nr_5F1161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2838 (s : N.State) (i : N.Inputs) :
  R.v2838 (state s) (inputs i) = Zmod.unsigned (N.v2838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2838 s i)) at 1.
  unfold R.v2838, N.v2838.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2839 (s : N.State) (i : N.Inputs) :
  R.v2839 (state s) (inputs i) = Zmod.unsigned (N.v2839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2839 s i)) at 1.
  unfold R.v2839, N.v2839.
  rewrite ?node_2838.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1162_nr_5F1162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1162_nr_5F1162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2840 (s : N.State) (i : N.Inputs) :
  R.v2840 (state s) (inputs i) = Zmod.unsigned (N.v2840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2840 s i)) at 1.
  unfold R.v2840, N.v2840.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2841 (s : N.State) (i : N.Inputs) :
  R.v2841 (state s) (inputs i) = Zmod.unsigned (N.v2841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2841 s i)) at 1.
  unfold R.v2841, N.v2841.
  rewrite ?node_2840.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1163_nr_5F1163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1163_nr_5F1163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2842 (s : N.State) (i : N.Inputs) :
  R.v2842 (state s) (inputs i) = Zmod.unsigned (N.v2842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2842 s i)) at 1.
  unfold R.v2842, N.v2842.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2843 (s : N.State) (i : N.Inputs) :
  R.v2843 (state s) (inputs i) = Zmod.unsigned (N.v2843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2843 s i)) at 1.
  unfold R.v2843, N.v2843.
  rewrite ?node_2842.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1164_nr_5F1164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1164_nr_5F1164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2844 (s : N.State) (i : N.Inputs) :
  R.v2844 (state s) (inputs i) = Zmod.unsigned (N.v2844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2844 s i)) at 1.
  unfold R.v2844, N.v2844.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2845 (s : N.State) (i : N.Inputs) :
  R.v2845 (state s) (inputs i) = Zmod.unsigned (N.v2845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2845 s i)) at 1.
  unfold R.v2845, N.v2845.
  rewrite ?node_2844.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1165_nr_5F1165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1165_nr_5F1165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2846 (s : N.State) (i : N.Inputs) :
  R.v2846 (state s) (inputs i) = Zmod.unsigned (N.v2846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2846 s i)) at 1.
  unfold R.v2846, N.v2846.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2847 (s : N.State) (i : N.Inputs) :
  R.v2847 (state s) (inputs i) = Zmod.unsigned (N.v2847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2847 s i)) at 1.
  unfold R.v2847, N.v2847.
  rewrite ?node_2846.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1166_nr_5F1166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1166_nr_5F1166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2848 (s : N.State) (i : N.Inputs) :
  R.v2848 (state s) (inputs i) = Zmod.unsigned (N.v2848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2848 s i)) at 1.
  unfold R.v2848, N.v2848.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2849 (s : N.State) (i : N.Inputs) :
  R.v2849 (state s) (inputs i) = Zmod.unsigned (N.v2849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2849 s i)) at 1.
  unfold R.v2849, N.v2849.
  rewrite ?node_2848.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1167_nr_5F1167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1167_nr_5F1167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2850 (s : N.State) (i : N.Inputs) :
  R.v2850 (state s) (inputs i) = Zmod.unsigned (N.v2850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2850 s i)) at 1.
  unfold R.v2850, N.v2850.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2851 (s : N.State) (i : N.Inputs) :
  R.v2851 (state s) (inputs i) = Zmod.unsigned (N.v2851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2851 s i)) at 1.
  unfold R.v2851, N.v2851.
  rewrite ?node_2850.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1168_nr_5F1168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1168_nr_5F1168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2852 (s : N.State) (i : N.Inputs) :
  R.v2852 (state s) (inputs i) = Zmod.unsigned (N.v2852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2852 s i)) at 1.
  unfold R.v2852, N.v2852.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2853 (s : N.State) (i : N.Inputs) :
  R.v2853 (state s) (inputs i) = Zmod.unsigned (N.v2853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2853 s i)) at 1.
  unfold R.v2853, N.v2853.
  rewrite ?node_2852.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1169_nr_5F1169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1169_nr_5F1169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2854 (s : N.State) (i : N.Inputs) :
  R.v2854 (state s) (inputs i) = Zmod.unsigned (N.v2854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2854 s i)) at 1.
  unfold R.v2854, N.v2854.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2855 (s : N.State) (i : N.Inputs) :
  R.v2855 (state s) (inputs i) = Zmod.unsigned (N.v2855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2855 s i)) at 1.
  unfold R.v2855, N.v2855.
  rewrite ?node_2854.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1170_nr_5F1170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1170_nr_5F1170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2856 (s : N.State) (i : N.Inputs) :
  R.v2856 (state s) (inputs i) = Zmod.unsigned (N.v2856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2856 s i)) at 1.
  unfold R.v2856, N.v2856.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2857 (s : N.State) (i : N.Inputs) :
  R.v2857 (state s) (inputs i) = Zmod.unsigned (N.v2857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2857 s i)) at 1.
  unfold R.v2857, N.v2857.
  rewrite ?node_2856.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1171_nr_5F1171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1171_nr_5F1171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2858 (s : N.State) (i : N.Inputs) :
  R.v2858 (state s) (inputs i) = Zmod.unsigned (N.v2858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2858 s i)) at 1.
  unfold R.v2858, N.v2858.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2859 (s : N.State) (i : N.Inputs) :
  R.v2859 (state s) (inputs i) = Zmod.unsigned (N.v2859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2859 s i)) at 1.
  unfold R.v2859, N.v2859.
  rewrite ?node_2858.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1172_nr_5F1172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1172_nr_5F1172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2860 (s : N.State) (i : N.Inputs) :
  R.v2860 (state s) (inputs i) = Zmod.unsigned (N.v2860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2860 s i)) at 1.
  unfold R.v2860, N.v2860.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2861 (s : N.State) (i : N.Inputs) :
  R.v2861 (state s) (inputs i) = Zmod.unsigned (N.v2861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2861 s i)) at 1.
  unfold R.v2861, N.v2861.
  rewrite ?node_2860.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1173_nr_5F1173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1173_nr_5F1173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2862 (s : N.State) (i : N.Inputs) :
  R.v2862 (state s) (inputs i) = Zmod.unsigned (N.v2862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2862 s i)) at 1.
  unfold R.v2862, N.v2862.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2863 (s : N.State) (i : N.Inputs) :
  R.v2863 (state s) (inputs i) = Zmod.unsigned (N.v2863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2863 s i)) at 1.
  unfold R.v2863, N.v2863.
  rewrite ?node_2862.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1174_nr_5F1174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1174_nr_5F1174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2864 (s : N.State) (i : N.Inputs) :
  R.v2864 (state s) (inputs i) = Zmod.unsigned (N.v2864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2864 s i)) at 1.
  unfold R.v2864, N.v2864.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2865 (s : N.State) (i : N.Inputs) :
  R.v2865 (state s) (inputs i) = Zmod.unsigned (N.v2865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2865 s i)) at 1.
  unfold R.v2865, N.v2865.
  rewrite ?node_2864.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1175_nr_5F1175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1175_nr_5F1175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2866 (s : N.State) (i : N.Inputs) :
  R.v2866 (state s) (inputs i) = Zmod.unsigned (N.v2866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2866 s i)) at 1.
  unfold R.v2866, N.v2866.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2867 (s : N.State) (i : N.Inputs) :
  R.v2867 (state s) (inputs i) = Zmod.unsigned (N.v2867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2867 s i)) at 1.
  unfold R.v2867, N.v2867.
  rewrite ?node_2866.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1176_nr_5F1176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1176_nr_5F1176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2868 (s : N.State) (i : N.Inputs) :
  R.v2868 (state s) (inputs i) = Zmod.unsigned (N.v2868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2868 s i)) at 1.
  unfold R.v2868, N.v2868.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2869 (s : N.State) (i : N.Inputs) :
  R.v2869 (state s) (inputs i) = Zmod.unsigned (N.v2869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2869 s i)) at 1.
  unfold R.v2869, N.v2869.
  rewrite ?node_2868.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1177_nr_5F1177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1177_nr_5F1177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2870 (s : N.State) (i : N.Inputs) :
  R.v2870 (state s) (inputs i) = Zmod.unsigned (N.v2870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2870 s i)) at 1.
  unfold R.v2870, N.v2870.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2871 (s : N.State) (i : N.Inputs) :
  R.v2871 (state s) (inputs i) = Zmod.unsigned (N.v2871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2871 s i)) at 1.
  unfold R.v2871, N.v2871.
  rewrite ?node_2870.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1178_nr_5F1178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1178_nr_5F1178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2872 (s : N.State) (i : N.Inputs) :
  R.v2872 (state s) (inputs i) = Zmod.unsigned (N.v2872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2872 s i)) at 1.
  unfold R.v2872, N.v2872.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2873 (s : N.State) (i : N.Inputs) :
  R.v2873 (state s) (inputs i) = Zmod.unsigned (N.v2873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2873 s i)) at 1.
  unfold R.v2873, N.v2873.
  rewrite ?node_2872.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1179_nr_5F1179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1179_nr_5F1179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2874 (s : N.State) (i : N.Inputs) :
  R.v2874 (state s) (inputs i) = Zmod.unsigned (N.v2874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2874 s i)) at 1.
  unfold R.v2874, N.v2874.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2875 (s : N.State) (i : N.Inputs) :
  R.v2875 (state s) (inputs i) = Zmod.unsigned (N.v2875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2875 s i)) at 1.
  unfold R.v2875, N.v2875.
  rewrite ?node_2874.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1180_nr_5F1180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1180_nr_5F1180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2876 (s : N.State) (i : N.Inputs) :
  R.v2876 (state s) (inputs i) = Zmod.unsigned (N.v2876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2876 s i)) at 1.
  unfold R.v2876, N.v2876.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2877 (s : N.State) (i : N.Inputs) :
  R.v2877 (state s) (inputs i) = Zmod.unsigned (N.v2877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2877 s i)) at 1.
  unfold R.v2877, N.v2877.
  rewrite ?node_2876.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1181_nr_5F1181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1181_nr_5F1181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2878 (s : N.State) (i : N.Inputs) :
  R.v2878 (state s) (inputs i) = Zmod.unsigned (N.v2878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2878 s i)) at 1.
  unfold R.v2878, N.v2878.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2879 (s : N.State) (i : N.Inputs) :
  R.v2879 (state s) (inputs i) = Zmod.unsigned (N.v2879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2879 s i)) at 1.
  unfold R.v2879, N.v2879.
  rewrite ?node_2878.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1182_nr_5F1182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1182_nr_5F1182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2880 (s : N.State) (i : N.Inputs) :
  R.v2880 (state s) (inputs i) = Zmod.unsigned (N.v2880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2880 s i)) at 1.
  unfold R.v2880, N.v2880.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2881 (s : N.State) (i : N.Inputs) :
  R.v2881 (state s) (inputs i) = Zmod.unsigned (N.v2881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2881 s i)) at 1.
  unfold R.v2881, N.v2881.
  rewrite ?node_2880.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1183_nr_5F1183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1183_nr_5F1183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2882 (s : N.State) (i : N.Inputs) :
  R.v2882 (state s) (inputs i) = Zmod.unsigned (N.v2882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2882 s i)) at 1.
  unfold R.v2882, N.v2882.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2883 (s : N.State) (i : N.Inputs) :
  R.v2883 (state s) (inputs i) = Zmod.unsigned (N.v2883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2883 s i)) at 1.
  unfold R.v2883, N.v2883.
  rewrite ?node_2882.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1184_nr_5F1184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1184_nr_5F1184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2884 (s : N.State) (i : N.Inputs) :
  R.v2884 (state s) (inputs i) = Zmod.unsigned (N.v2884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2884 s i)) at 1.
  unfold R.v2884, N.v2884.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2885 (s : N.State) (i : N.Inputs) :
  R.v2885 (state s) (inputs i) = Zmod.unsigned (N.v2885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2885 s i)) at 1.
  unfold R.v2885, N.v2885.
  rewrite ?node_2884.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1185_nr_5F1185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1185_nr_5F1185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2886 (s : N.State) (i : N.Inputs) :
  R.v2886 (state s) (inputs i) = Zmod.unsigned (N.v2886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2886 s i)) at 1.
  unfold R.v2886, N.v2886.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2887 (s : N.State) (i : N.Inputs) :
  R.v2887 (state s) (inputs i) = Zmod.unsigned (N.v2887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2887 s i)) at 1.
  unfold R.v2887, N.v2887.
  rewrite ?node_2886.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1186_nr_5F1186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1186_nr_5F1186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2888 (s : N.State) (i : N.Inputs) :
  R.v2888 (state s) (inputs i) = Zmod.unsigned (N.v2888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2888 s i)) at 1.
  unfold R.v2888, N.v2888.
  rewrite ?node_2819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2889 (s : N.State) (i : N.Inputs) :
  R.v2889 (state s) (inputs i) = Zmod.unsigned (N.v2889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2889 s i)) at 1.
  unfold R.v2889, N.v2889.
  rewrite ?node_2888.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1187_nr_5F1187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1187_nr_5F1187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2890 (s : N.State) (i : N.Inputs) :
  R.v2890 (state s) (inputs i) = Zmod.unsigned (N.v2890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2890 s i)) at 1.
  unfold R.v2890, N.v2890.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2891 (s : N.State) (i : N.Inputs) :
  R.v2891 (state s) (inputs i) = Zmod.unsigned (N.v2891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2891 s i)) at 1.
  unfold R.v2891, N.v2891.
  rewrite ?node_2890.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1188_nr_5F1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1188_nr_5F1188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2892 (s : N.State) (i : N.Inputs) :
  R.v2892 (state s) (inputs i) = Zmod.unsigned (N.v2892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2892 s i)) at 1.
  unfold R.v2892, N.v2892.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2893 (s : N.State) (i : N.Inputs) :
  R.v2893 (state s) (inputs i) = Zmod.unsigned (N.v2893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2893 s i)) at 1.
  unfold R.v2893, N.v2893.
  rewrite ?node_2892.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1189_nr_5F1189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1189_nr_5F1189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2894 (s : N.State) (i : N.Inputs) :
  R.v2894 (state s) (inputs i) = Zmod.unsigned (N.v2894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2894 s i)) at 1.
  unfold R.v2894, N.v2894.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2895 (s : N.State) (i : N.Inputs) :
  R.v2895 (state s) (inputs i) = Zmod.unsigned (N.v2895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2895 s i)) at 1.
  unfold R.v2895, N.v2895.
  rewrite ?node_2894.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1190_nr_5F1190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1190_nr_5F1190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2896 (s : N.State) (i : N.Inputs) :
  R.v2896 (state s) (inputs i) = Zmod.unsigned (N.v2896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2896 s i)) at 1.
  unfold R.v2896, N.v2896.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2897 (s : N.State) (i : N.Inputs) :
  R.v2897 (state s) (inputs i) = Zmod.unsigned (N.v2897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2897 s i)) at 1.
  unfold R.v2897, N.v2897.
  rewrite ?node_2896.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1191_nr_5F1191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1191_nr_5F1191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2898 (s : N.State) (i : N.Inputs) :
  R.v2898 (state s) (inputs i) = Zmod.unsigned (N.v2898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2898 s i)) at 1.
  unfold R.v2898, N.v2898.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2899 (s : N.State) (i : N.Inputs) :
  R.v2899 (state s) (inputs i) = Zmod.unsigned (N.v2899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2899 s i)) at 1.
  unfold R.v2899, N.v2899.
  rewrite ?node_2898.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1192_nr_5F1192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1192_nr_5F1192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2900 (s : N.State) (i : N.Inputs) :
  R.v2900 (state s) (inputs i) = Zmod.unsigned (N.v2900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2900 s i)) at 1.
  unfold R.v2900, N.v2900.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2901 (s : N.State) (i : N.Inputs) :
  R.v2901 (state s) (inputs i) = Zmod.unsigned (N.v2901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2901 s i)) at 1.
  unfold R.v2901, N.v2901.
  rewrite ?node_2900.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1193_nr_5F1193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1193_nr_5F1193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2902 (s : N.State) (i : N.Inputs) :
  R.v2902 (state s) (inputs i) = Zmod.unsigned (N.v2902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2902 s i)) at 1.
  unfold R.v2902, N.v2902.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2903 (s : N.State) (i : N.Inputs) :
  R.v2903 (state s) (inputs i) = Zmod.unsigned (N.v2903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2903 s i)) at 1.
  unfold R.v2903, N.v2903.
  rewrite ?node_2902.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1194_nr_5F1194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1194_nr_5F1194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2904 (s : N.State) (i : N.Inputs) :
  R.v2904 (state s) (inputs i) = Zmod.unsigned (N.v2904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2904 s i)) at 1.
  unfold R.v2904, N.v2904.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2905 (s : N.State) (i : N.Inputs) :
  R.v2905 (state s) (inputs i) = Zmod.unsigned (N.v2905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2905 s i)) at 1.
  unfold R.v2905, N.v2905.
  rewrite ?node_2904.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1195_nr_5F1195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1195_nr_5F1195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2906 (s : N.State) (i : N.Inputs) :
  R.v2906 (state s) (inputs i) = Zmod.unsigned (N.v2906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2906 s i)) at 1.
  unfold R.v2906, N.v2906.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2907 (s : N.State) (i : N.Inputs) :
  R.v2907 (state s) (inputs i) = Zmod.unsigned (N.v2907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2907 s i)) at 1.
  unfold R.v2907, N.v2907.
  rewrite ?node_2906.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1196_nr_5F1196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1196_nr_5F1196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2908 (s : N.State) (i : N.Inputs) :
  R.v2908 (state s) (inputs i) = Zmod.unsigned (N.v2908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2908 s i)) at 1.
  unfold R.v2908, N.v2908.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2909 (s : N.State) (i : N.Inputs) :
  R.v2909 (state s) (inputs i) = Zmod.unsigned (N.v2909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2909 s i)) at 1.
  unfold R.v2909, N.v2909.
  rewrite ?node_2908.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1197_nr_5F1197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1197_nr_5F1197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2910 (s : N.State) (i : N.Inputs) :
  R.v2910 (state s) (inputs i) = Zmod.unsigned (N.v2910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2910 s i)) at 1.
  unfold R.v2910, N.v2910.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2911 (s : N.State) (i : N.Inputs) :
  R.v2911 (state s) (inputs i) = Zmod.unsigned (N.v2911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2911 s i)) at 1.
  unfold R.v2911, N.v2911.
  rewrite ?node_2910.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1198_nr_5F1198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1198_nr_5F1198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2912 (s : N.State) (i : N.Inputs) :
  R.v2912 (state s) (inputs i) = Zmod.unsigned (N.v2912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2912 s i)) at 1.
  unfold R.v2912, N.v2912.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2913 (s : N.State) (i : N.Inputs) :
  R.v2913 (state s) (inputs i) = Zmod.unsigned (N.v2913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2913 s i)) at 1.
  unfold R.v2913, N.v2913.
  rewrite ?node_2912.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1199_nr_5F1199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1199_nr_5F1199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2914 (s : N.State) (i : N.Inputs) :
  R.v2914 (state s) (inputs i) = Zmod.unsigned (N.v2914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2914 s i)) at 1.
  unfold R.v2914, N.v2914.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2915 (s : N.State) (i : N.Inputs) :
  R.v2915 (state s) (inputs i) = Zmod.unsigned (N.v2915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2915 s i)) at 1.
  unfold R.v2915, N.v2915.
  rewrite ?node_2914.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1200_nr_5F1200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1200_nr_5F1200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2916 (s : N.State) (i : N.Inputs) :
  R.v2916 (state s) (inputs i) = Zmod.unsigned (N.v2916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2916 s i)) at 1.
  unfold R.v2916, N.v2916.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2917 (s : N.State) (i : N.Inputs) :
  R.v2917 (state s) (inputs i) = Zmod.unsigned (N.v2917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2917 s i)) at 1.
  unfold R.v2917, N.v2917.
  rewrite ?node_2916.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1201_nr_5F1201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1201_nr_5F1201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2918 (s : N.State) (i : N.Inputs) :
  R.v2918 (state s) (inputs i) = Zmod.unsigned (N.v2918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2918 s i)) at 1.
  unfold R.v2918, N.v2918.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2919 (s : N.State) (i : N.Inputs) :
  R.v2919 (state s) (inputs i) = Zmod.unsigned (N.v2919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2919 s i)) at 1.
  unfold R.v2919, N.v2919.
  rewrite ?node_2918.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1202_nr_5F1202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1202_nr_5F1202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2920 (s : N.State) (i : N.Inputs) :
  R.v2920 (state s) (inputs i) = Zmod.unsigned (N.v2920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2920 s i)) at 1.
  unfold R.v2920, N.v2920.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2921 (s : N.State) (i : N.Inputs) :
  R.v2921 (state s) (inputs i) = Zmod.unsigned (N.v2921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2921 s i)) at 1.
  unfold R.v2921, N.v2921.
  rewrite ?node_2920.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1203_nr_5F1203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1203_nr_5F1203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2922 (s : N.State) (i : N.Inputs) :
  R.v2922 (state s) (inputs i) = Zmod.unsigned (N.v2922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2922 s i)) at 1.
  unfold R.v2922, N.v2922.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2923 (s : N.State) (i : N.Inputs) :
  R.v2923 (state s) (inputs i) = Zmod.unsigned (N.v2923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2923 s i)) at 1.
  unfold R.v2923, N.v2923.
  rewrite ?node_2922.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1204_nr_5F1204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1204_nr_5F1204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2924 (s : N.State) (i : N.Inputs) :
  R.v2924 (state s) (inputs i) = Zmod.unsigned (N.v2924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2924 s i)) at 1.
  unfold R.v2924, N.v2924.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2925 (s : N.State) (i : N.Inputs) :
  R.v2925 (state s) (inputs i) = Zmod.unsigned (N.v2925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2925 s i)) at 1.
  unfold R.v2925, N.v2925.
  rewrite ?node_2924.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1205_nr_5F1205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1205_nr_5F1205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2926 (s : N.State) (i : N.Inputs) :
  R.v2926 (state s) (inputs i) = Zmod.unsigned (N.v2926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2926 s i)) at 1.
  unfold R.v2926, N.v2926.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2927 (s : N.State) (i : N.Inputs) :
  R.v2927 (state s) (inputs i) = Zmod.unsigned (N.v2927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2927 s i)) at 1.
  unfold R.v2927, N.v2927.
  rewrite ?node_2926.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1206_nr_5F1206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1206_nr_5F1206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2928 (s : N.State) (i : N.Inputs) :
  R.v2928 (state s) (inputs i) = Zmod.unsigned (N.v2928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2928 s i)) at 1.
  unfold R.v2928, N.v2928.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2929 (s : N.State) (i : N.Inputs) :
  R.v2929 (state s) (inputs i) = Zmod.unsigned (N.v2929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2929 s i)) at 1.
  unfold R.v2929, N.v2929.
  rewrite ?node_2928.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1207_nr_5F1207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1207_nr_5F1207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2930 (s : N.State) (i : N.Inputs) :
  R.v2930 (state s) (inputs i) = Zmod.unsigned (N.v2930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2930 s i)) at 1.
  unfold R.v2930, N.v2930.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2931 (s : N.State) (i : N.Inputs) :
  R.v2931 (state s) (inputs i) = Zmod.unsigned (N.v2931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2931 s i)) at 1.
  unfold R.v2931, N.v2931.
  rewrite ?node_2930.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1208_nr_5F1208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1208_nr_5F1208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2932 (s : N.State) (i : N.Inputs) :
  R.v2932 (state s) (inputs i) = Zmod.unsigned (N.v2932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2932 s i)) at 1.
  unfold R.v2932, N.v2932.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2933 (s : N.State) (i : N.Inputs) :
  R.v2933 (state s) (inputs i) = Zmod.unsigned (N.v2933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2933 s i)) at 1.
  unfold R.v2933, N.v2933.
  rewrite ?node_2932.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1209_nr_5F1209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1209_nr_5F1209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2934 (s : N.State) (i : N.Inputs) :
  R.v2934 (state s) (inputs i) = Zmod.unsigned (N.v2934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2934 s i)) at 1.
  unfold R.v2934, N.v2934.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2935 (s : N.State) (i : N.Inputs) :
  R.v2935 (state s) (inputs i) = Zmod.unsigned (N.v2935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2935 s i)) at 1.
  unfold R.v2935, N.v2935.
  rewrite ?node_2934.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1210_nr_5F1210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1210_nr_5F1210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2936 (s : N.State) (i : N.Inputs) :
  R.v2936 (state s) (inputs i) = Zmod.unsigned (N.v2936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2936 s i)) at 1.
  unfold R.v2936, N.v2936.
  rewrite ?node_1616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2937 (s : N.State) (i : N.Inputs) :
  R.v2937 (state s) (inputs i) = Zmod.unsigned (N.v2937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2937 s i)) at 1.
  unfold R.v2937, N.v2937.
  rewrite ?node_2936.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1211_nr_5F1211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1211_nr_5F1211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2938 (s : N.State) (i : N.Inputs) :
  R.v2938 (state s) (inputs i) = Zmod.unsigned (N.v2938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2938 s i)) at 1.
  unfold R.v2938, N.v2938.
  rewrite ?node_1733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2939 (s : N.State) (i : N.Inputs) :
  R.v2939 (state s) (inputs i) = Zmod.unsigned (N.v2939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2939 s i)) at 1.
  unfold R.v2939, N.v2939.
  rewrite ?node_2938.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1212_nr_5F1212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1212_nr_5F1212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2940 (s : N.State) (i : N.Inputs) :
  R.v2940 (state s) (inputs i) = Zmod.unsigned (N.v2940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2940 s i)) at 1.
  unfold R.v2940, N.v2940.
  rewrite ?node_1854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2941 (s : N.State) (i : N.Inputs) :
  R.v2941 (state s) (inputs i) = Zmod.unsigned (N.v2941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2941 s i)) at 1.
  unfold R.v2941, N.v2941.
  rewrite ?node_2940.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1213_nr_5F1213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1213_nr_5F1213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2942 (s : N.State) (i : N.Inputs) :
  R.v2942 (state s) (inputs i) = Zmod.unsigned (N.v2942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2942 s i)) at 1.
  unfold R.v2942, N.v2942.
  rewrite ?node_1979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2943 (s : N.State) (i : N.Inputs) :
  R.v2943 (state s) (inputs i) = Zmod.unsigned (N.v2943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2943 s i)) at 1.
  unfold R.v2943, N.v2943.
  rewrite ?node_2942.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1214_nr_5F1214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1214_nr_5F1214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2944 (s : N.State) (i : N.Inputs) :
  R.v2944 (state s) (inputs i) = Zmod.unsigned (N.v2944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2944 s i)) at 1.
  unfold R.v2944, N.v2944.
  rewrite ?node_2108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2945 (s : N.State) (i : N.Inputs) :
  R.v2945 (state s) (inputs i) = Zmod.unsigned (N.v2945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2945 s i)) at 1.
  unfold R.v2945, N.v2945.
  rewrite ?node_2944.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1215_nr_5F1215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1215_nr_5F1215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2946 (s : N.State) (i : N.Inputs) :
  R.v2946 (state s) (inputs i) = Zmod.unsigned (N.v2946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2946 s i)) at 1.
  unfold R.v2946, N.v2946.
  rewrite ?node_2241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2947 (s : N.State) (i : N.Inputs) :
  R.v2947 (state s) (inputs i) = Zmod.unsigned (N.v2947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2947 s i)) at 1.
  unfold R.v2947, N.v2947.
  rewrite ?node_2946.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1216_nr_5F1216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1216_nr_5F1216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2948 (s : N.State) (i : N.Inputs) :
  R.v2948 (state s) (inputs i) = Zmod.unsigned (N.v2948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2948 s i)) at 1.
  unfold R.v2948, N.v2948.
  rewrite ?node_2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2949 (s : N.State) (i : N.Inputs) :
  R.v2949 (state s) (inputs i) = Zmod.unsigned (N.v2949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2949 s i)) at 1.
  unfold R.v2949, N.v2949.
  rewrite ?node_2948.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1217_nr_5F1217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1217_nr_5F1217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2950 (s : N.State) (i : N.Inputs) :
  R.v2950 (state s) (inputs i) = Zmod.unsigned (N.v2950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2950 s i)) at 1.
  unfold R.v2950, N.v2950.
  rewrite ?node_2519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2951 (s : N.State) (i : N.Inputs) :
  R.v2951 (state s) (inputs i) = Zmod.unsigned (N.v2951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2951 s i)) at 1.
  unfold R.v2951, N.v2951.
  rewrite ?node_2950.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1218_nr_5F1218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1218_nr_5F1218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2952 (s : N.State) (i : N.Inputs) :
  R.v2952 (state s) (inputs i) = Zmod.unsigned (N.v2952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2952 s i)) at 1.
  unfold R.v2952, N.v2952.
  rewrite ?node_2664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2953 (s : N.State) (i : N.Inputs) :
  R.v2953 (state s) (inputs i) = Zmod.unsigned (N.v2953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2953 s i)) at 1.
  unfold R.v2953, N.v2953.
  rewrite ?node_2952.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1219_nr_5F1219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1219_nr_5F1219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2954 (s : N.State) (i : N.Inputs) :
  R.v2954 (state s) (inputs i) = Zmod.unsigned (N.v2954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2954 s i)) at 1.
  unfold R.v2954, N.v2954.
  rewrite ?node_2815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2955 (s : N.State) (i : N.Inputs) :
  R.v2955 (state s) (inputs i) = Zmod.unsigned (N.v2955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2955 s i)) at 1.
  unfold R.v2955, N.v2955.
  rewrite ?node_2954.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1220_nr_5F1220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1220_nr_5F1220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2956 (s : N.State) (i : N.Inputs) :
  R.v2956 (state s) (inputs i) = Zmod.unsigned (N.v2956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2956 s i)) at 1.
  unfold R.v2956, N.v2956.
  rewrite ?node_2890.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1221_nr_5F1221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1221_nr_5F1221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2957 (s : N.State) (i : N.Inputs) :
  R.v2957 (state s) (inputs i) = Zmod.unsigned (N.v2957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2957 s i)) at 1.
  unfold R.v2957, N.v2957.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2958 (s : N.State) (i : N.Inputs) :
  R.v2958 (state s) (inputs i) = Zmod.unsigned (N.v2958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2958 s i)) at 1.
  unfold R.v2958, N.v2958.
  rewrite ?node_2957.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1222_nr_5F1222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1222_nr_5F1222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2959 (s : N.State) (i : N.Inputs) :
  R.v2959 (state s) (inputs i) = Zmod.unsigned (N.v2959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2959 s i)) at 1.
  unfold R.v2959, N.v2959.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2960 (s : N.State) (i : N.Inputs) :
  R.v2960 (state s) (inputs i) = Zmod.unsigned (N.v2960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2960 s i)) at 1.
  unfold R.v2960, N.v2960.
  rewrite ?node_2959.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1223_nr_5F1223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1223_nr_5F1223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2961 (s : N.State) (i : N.Inputs) :
  R.v2961 (state s) (inputs i) = Zmod.unsigned (N.v2961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2961 s i)) at 1.
  unfold R.v2961, N.v2961.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2962 (s : N.State) (i : N.Inputs) :
  R.v2962 (state s) (inputs i) = Zmod.unsigned (N.v2962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2962 s i)) at 1.
  unfold R.v2962, N.v2962.
  rewrite ?node_2961.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1224_nr_5F1224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1224_nr_5F1224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2963 (s : N.State) (i : N.Inputs) :
  R.v2963 (state s) (inputs i) = Zmod.unsigned (N.v2963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2963 s i)) at 1.
  unfold R.v2963, N.v2963.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2964 (s : N.State) (i : N.Inputs) :
  R.v2964 (state s) (inputs i) = Zmod.unsigned (N.v2964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2964 s i)) at 1.
  unfold R.v2964, N.v2964.
  rewrite ?node_2963.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1225_nr_5F1225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1225_nr_5F1225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2965 (s : N.State) (i : N.Inputs) :
  R.v2965 (state s) (inputs i) = Zmod.unsigned (N.v2965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2965 s i)) at 1.
  unfold R.v2965, N.v2965.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2966 (s : N.State) (i : N.Inputs) :
  R.v2966 (state s) (inputs i) = Zmod.unsigned (N.v2966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2966 s i)) at 1.
  unfold R.v2966, N.v2966.
  rewrite ?node_2965.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1226_nr_5F1226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1226_nr_5F1226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2967 (s : N.State) (i : N.Inputs) :
  R.v2967 (state s) (inputs i) = Zmod.unsigned (N.v2967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2967 s i)) at 1.
  unfold R.v2967, N.v2967.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2968 (s : N.State) (i : N.Inputs) :
  R.v2968 (state s) (inputs i) = Zmod.unsigned (N.v2968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2968 s i)) at 1.
  unfold R.v2968, N.v2968.
  rewrite ?node_2967.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1227_nr_5F1227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1227_nr_5F1227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2969 (s : N.State) (i : N.Inputs) :
  R.v2969 (state s) (inputs i) = Zmod.unsigned (N.v2969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2969 s i)) at 1.
  unfold R.v2969, N.v2969.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2970 (s : N.State) (i : N.Inputs) :
  R.v2970 (state s) (inputs i) = Zmod.unsigned (N.v2970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2970 s i)) at 1.
  unfold R.v2970, N.v2970.
  rewrite ?node_2969.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1228_nr_5F1228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1228_nr_5F1228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2971 (s : N.State) (i : N.Inputs) :
  R.v2971 (state s) (inputs i) = Zmod.unsigned (N.v2971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2971 s i)) at 1.
  unfold R.v2971, N.v2971.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2972 (s : N.State) (i : N.Inputs) :
  R.v2972 (state s) (inputs i) = Zmod.unsigned (N.v2972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2972 s i)) at 1.
  unfold R.v2972, N.v2972.
  rewrite ?node_2971.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1229_nr_5F1229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1229_nr_5F1229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2973 (s : N.State) (i : N.Inputs) :
  R.v2973 (state s) (inputs i) = Zmod.unsigned (N.v2973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2973 s i)) at 1.
  unfold R.v2973, N.v2973.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2974 (s : N.State) (i : N.Inputs) :
  R.v2974 (state s) (inputs i) = Zmod.unsigned (N.v2974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2974 s i)) at 1.
  unfold R.v2974, N.v2974.
  rewrite ?node_2973.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1230_nr_5F1230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1230_nr_5F1230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2975 (s : N.State) (i : N.Inputs) :
  R.v2975 (state s) (inputs i) = Zmod.unsigned (N.v2975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2975 s i)) at 1.
  unfold R.v2975, N.v2975.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2976 (s : N.State) (i : N.Inputs) :
  R.v2976 (state s) (inputs i) = Zmod.unsigned (N.v2976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2976 s i)) at 1.
  unfold R.v2976, N.v2976.
  rewrite ?node_2975.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1231_nr_5F1231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1231_nr_5F1231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2977 (s : N.State) (i : N.Inputs) :
  R.v2977 (state s) (inputs i) = Zmod.unsigned (N.v2977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2977 s i)) at 1.
  unfold R.v2977, N.v2977.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2978 (s : N.State) (i : N.Inputs) :
  R.v2978 (state s) (inputs i) = Zmod.unsigned (N.v2978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2978 s i)) at 1.
  unfold R.v2978, N.v2978.
  rewrite ?node_2977.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1232_nr_5F1232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1232_nr_5F1232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2979 (s : N.State) (i : N.Inputs) :
  R.v2979 (state s) (inputs i) = Zmod.unsigned (N.v2979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2979 s i)) at 1.
  unfold R.v2979, N.v2979.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2980 (s : N.State) (i : N.Inputs) :
  R.v2980 (state s) (inputs i) = Zmod.unsigned (N.v2980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2980 s i)) at 1.
  unfold R.v2980, N.v2980.
  rewrite ?node_2979.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1233_nr_5F1233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1233_nr_5F1233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2981 (s : N.State) (i : N.Inputs) :
  R.v2981 (state s) (inputs i) = Zmod.unsigned (N.v2981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2981 s i)) at 1.
  unfold R.v2981, N.v2981.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2982 (s : N.State) (i : N.Inputs) :
  R.v2982 (state s) (inputs i) = Zmod.unsigned (N.v2982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2982 s i)) at 1.
  unfold R.v2982, N.v2982.
  rewrite ?node_2981.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1234_nr_5F1234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1234_nr_5F1234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2983 (s : N.State) (i : N.Inputs) :
  R.v2983 (state s) (inputs i) = Zmod.unsigned (N.v2983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2983 s i)) at 1.
  unfold R.v2983, N.v2983.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2984 (s : N.State) (i : N.Inputs) :
  R.v2984 (state s) (inputs i) = Zmod.unsigned (N.v2984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2984 s i)) at 1.
  unfold R.v2984, N.v2984.
  rewrite ?node_2983.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1235_nr_5F1235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1235_nr_5F1235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2985 (s : N.State) (i : N.Inputs) :
  R.v2985 (state s) (inputs i) = Zmod.unsigned (N.v2985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2985 s i)) at 1.
  unfold R.v2985, N.v2985.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2986 (s : N.State) (i : N.Inputs) :
  R.v2986 (state s) (inputs i) = Zmod.unsigned (N.v2986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2986 s i)) at 1.
  unfold R.v2986, N.v2986.
  rewrite ?node_2985.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1236_nr_5F1236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1236_nr_5F1236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2987 (s : N.State) (i : N.Inputs) :
  R.v2987 (state s) (inputs i) = Zmod.unsigned (N.v2987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2987 s i)) at 1.
  unfold R.v2987, N.v2987.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2988 (s : N.State) (i : N.Inputs) :
  R.v2988 (state s) (inputs i) = Zmod.unsigned (N.v2988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2988 s i)) at 1.
  unfold R.v2988, N.v2988.
  rewrite ?node_2987.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1237_nr_5F1237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1237_nr_5F1237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2989 (s : N.State) (i : N.Inputs) :
  R.v2989 (state s) (inputs i) = Zmod.unsigned (N.v2989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2989 s i)) at 1.
  unfold R.v2989, N.v2989.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2990 (s : N.State) (i : N.Inputs) :
  R.v2990 (state s) (inputs i) = Zmod.unsigned (N.v2990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2990 s i)) at 1.
  unfold R.v2990, N.v2990.
  rewrite ?node_2989.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1238_nr_5F1238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1238_nr_5F1238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2991 (s : N.State) (i : N.Inputs) :
  R.v2991 (state s) (inputs i) = Zmod.unsigned (N.v2991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2991 s i)) at 1.
  unfold R.v2991, N.v2991.
  rewrite ?node_1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2992 (s : N.State) (i : N.Inputs) :
  R.v2992 (state s) (inputs i) = Zmod.unsigned (N.v2992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2992 s i)) at 1.
  unfold R.v2992, N.v2992.
  rewrite ?node_2991.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1239_nr_5F1239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1239_nr_5F1239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2993 (s : N.State) (i : N.Inputs) :
  R.v2993 (state s) (inputs i) = Zmod.unsigned (N.v2993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2993 s i)) at 1.
  unfold R.v2993, N.v2993.
  rewrite ?node_1188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2994 (s : N.State) (i : N.Inputs) :
  R.v2994 (state s) (inputs i) = Zmod.unsigned (N.v2994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2994 s i)) at 1.
  unfold R.v2994, N.v2994.
  rewrite ?node_2993.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1240_nr_5F1240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1240_nr_5F1240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2995 (s : N.State) (i : N.Inputs) :
  R.v2995 (state s) (inputs i) = Zmod.unsigned (N.v2995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2995 s i)) at 1.
  unfold R.v2995, N.v2995.
  rewrite ?node_1289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2996 (s : N.State) (i : N.Inputs) :
  R.v2996 (state s) (inputs i) = Zmod.unsigned (N.v2996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2996 s i)) at 1.
  unfold R.v2996, N.v2996.
  rewrite ?node_2995.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1241_nr_5F1241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1241_nr_5F1241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2997 (s : N.State) (i : N.Inputs) :
  R.v2997 (state s) (inputs i) = Zmod.unsigned (N.v2997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2997 s i)) at 1.
  unfold R.v2997, N.v2997.
  rewrite ?node_1394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2998 (s : N.State) (i : N.Inputs) :
  R.v2998 (state s) (inputs i) = Zmod.unsigned (N.v2998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2998 s i)) at 1.
  unfold R.v2998, N.v2998.
  rewrite ?node_2997.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1242_nr_5F1242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1242_nr_5F1242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2999 (s : N.State) (i : N.Inputs) :
  R.v2999 (state s) (inputs i) = Zmod.unsigned (N.v2999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2999 s i)) at 1.
  unfold R.v2999, N.v2999.
  rewrite ?node_1503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
