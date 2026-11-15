From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes Slices Reductions Muxes MuxShapes Concats.
Local Open Scope Z_scope.

Lemma log2_69_reference s i ghost : to_Zpos (word_69 (encoded_leaves s i ghost)) = Reference.v82 s i.
Proof.
 rewrite mux_integer_69 slice_65_reference mux_68_reference.
 unfold Reference.v82, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_73_reference s i ghost : to_Zpos (word_73 (encoded_leaves s i ghost)) = Reference.v87 s i.
Proof.
 rewrite mux_integer_73 slice_71_reference slice_72_reference.
 unfold Reference.v87, Reference.v78, Reference.v86, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_74_reference s i ghost : to_Zpos (word_74 (encoded_leaves s i ghost)) = Reference.v88 s i.
Proof.
 rewrite mux_integer_74 slice_70_reference log2_73_reference.
 unfold Reference.v88, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_75_reference s i ghost : to_Zpos (word_75 (encoded_leaves s i ghost)) = Reference.v89 s i.
Proof.
 rewrite mux_integer_75 reduction_64_reference log2_69_reference log2_74_reference.
 unfold Reference.v89, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_76_reference s i ghost : to_Zpos (word_76 (encoded_leaves s i ghost)) = Reference.v90 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_76 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_76_size.
 -
 rewrite concat_integer_76 reduction_64_reference log2_75_reference.
 unfold Reference.v90, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_83_reference s i ghost : to_Zpos (word_83 (encoded_leaves s i ghost)) = Reference.v97 s i.
Proof.
 rewrite mux_integer_83 slice_81_reference slice_82_reference.
 unfold Reference.v97, Reference.v78, Reference.v96, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_84_reference s i ghost : to_Zpos (word_84 (encoded_leaves s i ghost)) = Reference.v98 s i.
Proof.
 rewrite mux_integer_84 slice_80_reference log2_83_reference.
 unfold Reference.v98, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_88_reference s i ghost : to_Zpos (word_88 (encoded_leaves s i ghost)) = Reference.v103 s i.
Proof.
 rewrite mux_integer_88 slice_86_reference slice_87_reference.
 unfold Reference.v103, Reference.v78, Reference.v102, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_89_reference s i ghost : to_Zpos (word_89 (encoded_leaves s i ghost)) = Reference.v104 s i.
Proof.
 rewrite mux_integer_89 slice_85_reference log2_88_reference.
 unfold Reference.v104, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_90_reference s i ghost : to_Zpos (word_90 (encoded_leaves s i ghost)) = Reference.v105 s i.
Proof.
 rewrite mux_integer_90 reduction_79_reference log2_84_reference log2_89_reference.
 unfold Reference.v105, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_91_reference s i ghost : to_Zpos (word_91 (encoded_leaves s i ghost)) = Reference.v106 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_91 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_91_size.
 -
 rewrite concat_integer_91 reduction_79_reference log2_90_reference.
 unfold Reference.v106, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_92_reference s i ghost : to_Zpos (word_92 (encoded_leaves s i ghost)) = Reference.v107 s i.
Proof.
 rewrite mux_integer_92 reduction_61_reference log2_76_reference log2_91_reference.
 unfold Reference.v107, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_93_reference s i ghost : to_Zpos (word_93 (encoded_leaves s i ghost)) = Reference.v108 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_93 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_93_size.
 -
 rewrite concat_integer_93 reduction_61_reference log2_92_reference.
 unfold Reference.v108, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_103_reference s i ghost : to_Zpos (word_103 (encoded_leaves s i ghost)) = Reference.v117 s i.
Proof.
 rewrite mux_integer_103 slice_101_reference slice_102_reference.
 unfold Reference.v117, Reference.v78, Reference.v116, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_104_reference s i ghost : to_Zpos (word_104 (encoded_leaves s i ghost)) = Reference.v118 s i.
Proof.
 rewrite mux_integer_104 slice_100_reference log2_103_reference.
 unfold Reference.v118, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_108_reference s i ghost : to_Zpos (word_108 (encoded_leaves s i ghost)) = Reference.v123 s i.
Proof.
 rewrite mux_integer_108 slice_106_reference slice_107_reference.
 unfold Reference.v123, Reference.v78, Reference.v122, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_109_reference s i ghost : to_Zpos (word_109 (encoded_leaves s i ghost)) = Reference.v124 s i.
Proof.
 rewrite mux_integer_109 slice_105_reference log2_108_reference.
 unfold Reference.v124, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_110_reference s i ghost : to_Zpos (word_110 (encoded_leaves s i ghost)) = Reference.v125 s i.
Proof.
 rewrite mux_integer_110 reduction_99_reference log2_104_reference log2_109_reference.
 unfold Reference.v125, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_111_reference s i ghost : to_Zpos (word_111 (encoded_leaves s i ghost)) = Reference.v126 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_111 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_111_size.
 -
 rewrite concat_integer_111 reduction_99_reference log2_110_reference.
 unfold Reference.v126, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_118_reference s i ghost : to_Zpos (word_118 (encoded_leaves s i ghost)) = Reference.v133 s i.
Proof.
 rewrite mux_integer_118 slice_116_reference slice_117_reference.
 unfold Reference.v133, Reference.v78, Reference.v132, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_119_reference s i ghost : to_Zpos (word_119 (encoded_leaves s i ghost)) = Reference.v134 s i.
Proof.
 rewrite mux_integer_119 slice_115_reference log2_118_reference.
 unfold Reference.v134, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_123_reference s i ghost : to_Zpos (word_123 (encoded_leaves s i ghost)) = Reference.v139 s i.
Proof.
 rewrite mux_integer_123 slice_121_reference slice_122_reference.
 unfold Reference.v139, Reference.v78, Reference.v138, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_124_reference s i ghost : to_Zpos (word_124 (encoded_leaves s i ghost)) = Reference.v140 s i.
Proof.
 rewrite mux_integer_124 slice_120_reference log2_123_reference.
 unfold Reference.v140, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_125_reference s i ghost : to_Zpos (word_125 (encoded_leaves s i ghost)) = Reference.v141 s i.
Proof.
 rewrite mux_integer_125 reduction_114_reference log2_119_reference log2_124_reference.
 unfold Reference.v141, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_126_reference s i ghost : to_Zpos (word_126 (encoded_leaves s i ghost)) = Reference.v142 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_126 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_126_size.
 -
 rewrite concat_integer_126 reduction_114_reference log2_125_reference.
 unfold Reference.v142, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_127_reference s i ghost : to_Zpos (word_127 (encoded_leaves s i ghost)) = Reference.v143 s i.
Proof.
 rewrite mux_integer_127 reduction_96_reference log2_111_reference log2_126_reference.
 unfold Reference.v143, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_128_reference s i ghost : to_Zpos (word_128 (encoded_leaves s i ghost)) = Reference.v144 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_128 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_128_size.
 -
 rewrite concat_integer_128 reduction_96_reference log2_127_reference.
 unfold Reference.v144, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_129_reference s i ghost : to_Zpos (word_129 (encoded_leaves s i ghost)) = Reference.v145 s i.
Proof.
 rewrite mux_integer_129 reduction_58_reference log2_93_reference log2_128_reference.
 unfold Reference.v145, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_130_reference s i ghost : to_Zpos (word_130 (encoded_leaves s i ghost)) = Reference.v146 s i.
Proof.
 transitivity (normalize 5 (to_Zpos (word_130 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_130_size.
 -
 rewrite concat_integer_130 reduction_58_reference log2_129_reference.
 unfold Reference.v146, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 5))). apply Z.add_comm.
Qed.
Lemma log2_143_reference s i ghost : to_Zpos (word_143 (encoded_leaves s i ghost)) = Reference.v157 s i.
Proof.
 rewrite mux_integer_143 slice_141_reference slice_142_reference.
 unfold Reference.v157, Reference.v78, Reference.v156, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_144_reference s i ghost : to_Zpos (word_144 (encoded_leaves s i ghost)) = Reference.v158 s i.
Proof.
 rewrite mux_integer_144 slice_140_reference log2_143_reference.
 unfold Reference.v158, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_148_reference s i ghost : to_Zpos (word_148 (encoded_leaves s i ghost)) = Reference.v163 s i.
Proof.
 rewrite mux_integer_148 slice_146_reference slice_147_reference.
 unfold Reference.v163, Reference.v78, Reference.v162, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_149_reference s i ghost : to_Zpos (word_149 (encoded_leaves s i ghost)) = Reference.v164 s i.
Proof.
 rewrite mux_integer_149 slice_145_reference log2_148_reference.
 unfold Reference.v164, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_150_reference s i ghost : to_Zpos (word_150 (encoded_leaves s i ghost)) = Reference.v165 s i.
Proof.
 rewrite mux_integer_150 reduction_139_reference log2_144_reference log2_149_reference.
 unfold Reference.v165, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_151_reference s i ghost : to_Zpos (word_151 (encoded_leaves s i ghost)) = Reference.v166 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_151 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_151_size.
 -
 rewrite concat_integer_151 reduction_139_reference log2_150_reference.
 unfold Reference.v166, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_158_reference s i ghost : to_Zpos (word_158 (encoded_leaves s i ghost)) = Reference.v173 s i.
Proof.
 rewrite mux_integer_158 slice_156_reference slice_157_reference.
 unfold Reference.v173, Reference.v78, Reference.v172, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_159_reference s i ghost : to_Zpos (word_159 (encoded_leaves s i ghost)) = Reference.v174 s i.
Proof.
 rewrite mux_integer_159 slice_155_reference log2_158_reference.
 unfold Reference.v174, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_163_reference s i ghost : to_Zpos (word_163 (encoded_leaves s i ghost)) = Reference.v179 s i.
Proof.
 rewrite mux_integer_163 slice_161_reference slice_162_reference.
 unfold Reference.v179, Reference.v78, Reference.v178, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_164_reference s i ghost : to_Zpos (word_164 (encoded_leaves s i ghost)) = Reference.v180 s i.
Proof.
 rewrite mux_integer_164 slice_160_reference log2_163_reference.
 unfold Reference.v180, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_165_reference s i ghost : to_Zpos (word_165 (encoded_leaves s i ghost)) = Reference.v181 s i.
Proof.
 rewrite mux_integer_165 reduction_154_reference log2_159_reference log2_164_reference.
 unfold Reference.v181, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_166_reference s i ghost : to_Zpos (word_166 (encoded_leaves s i ghost)) = Reference.v182 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_166 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_166_size.
 -
 rewrite concat_integer_166 reduction_154_reference log2_165_reference.
 unfold Reference.v182, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_167_reference s i ghost : to_Zpos (word_167 (encoded_leaves s i ghost)) = Reference.v183 s i.
Proof.
 rewrite mux_integer_167 reduction_136_reference log2_151_reference log2_166_reference.
 unfold Reference.v183, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_168_reference s i ghost : to_Zpos (word_168 (encoded_leaves s i ghost)) = Reference.v184 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_168 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_168_size.
 -
 rewrite concat_integer_168 reduction_136_reference log2_167_reference.
 unfold Reference.v184, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_178_reference s i ghost : to_Zpos (word_178 (encoded_leaves s i ghost)) = Reference.v193 s i.
Proof.
 rewrite mux_integer_178 slice_176_reference slice_177_reference.
 unfold Reference.v193, Reference.v78, Reference.v192, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_179_reference s i ghost : to_Zpos (word_179 (encoded_leaves s i ghost)) = Reference.v194 s i.
Proof.
 rewrite mux_integer_179 slice_175_reference log2_178_reference.
 unfold Reference.v194, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_183_reference s i ghost : to_Zpos (word_183 (encoded_leaves s i ghost)) = Reference.v199 s i.
Proof.
 rewrite mux_integer_183 slice_181_reference slice_182_reference.
 unfold Reference.v199, Reference.v78, Reference.v198, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_184_reference s i ghost : to_Zpos (word_184 (encoded_leaves s i ghost)) = Reference.v200 s i.
Proof.
 rewrite mux_integer_184 slice_180_reference log2_183_reference.
 unfold Reference.v200, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_185_reference s i ghost : to_Zpos (word_185 (encoded_leaves s i ghost)) = Reference.v201 s i.
Proof.
 rewrite mux_integer_185 reduction_174_reference log2_179_reference log2_184_reference.
 unfold Reference.v201, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_186_reference s i ghost : to_Zpos (word_186 (encoded_leaves s i ghost)) = Reference.v202 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_186 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_186_size.
 -
 rewrite concat_integer_186 reduction_174_reference log2_185_reference.
 unfold Reference.v202, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_193_reference s i ghost : to_Zpos (word_193 (encoded_leaves s i ghost)) = Reference.v209 s i.
Proof.
 rewrite mux_integer_193 slice_191_reference slice_192_reference.
 unfold Reference.v209, Reference.v78, Reference.v208, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_194_reference s i ghost : to_Zpos (word_194 (encoded_leaves s i ghost)) = Reference.v210 s i.
Proof.
 rewrite mux_integer_194 slice_190_reference log2_193_reference.
 unfold Reference.v210, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_198_reference s i ghost : to_Zpos (word_198 (encoded_leaves s i ghost)) = Reference.v215 s i.
Proof.
 rewrite mux_integer_198 slice_196_reference slice_197_reference.
 unfold Reference.v215, Reference.v78, Reference.v214, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_199_reference s i ghost : to_Zpos (word_199 (encoded_leaves s i ghost)) = Reference.v216 s i.
Proof.
 rewrite mux_integer_199 slice_195_reference log2_198_reference.
 unfold Reference.v216, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_200_reference s i ghost : to_Zpos (word_200 (encoded_leaves s i ghost)) = Reference.v217 s i.
Proof.
 rewrite mux_integer_200 reduction_189_reference log2_194_reference log2_199_reference.
 unfold Reference.v217, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_201_reference s i ghost : to_Zpos (word_201 (encoded_leaves s i ghost)) = Reference.v218 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_201 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_201_size.
 -
 rewrite concat_integer_201 reduction_189_reference log2_200_reference.
 unfold Reference.v218, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_202_reference s i ghost : to_Zpos (word_202 (encoded_leaves s i ghost)) = Reference.v219 s i.
Proof.
 rewrite mux_integer_202 reduction_171_reference log2_186_reference log2_201_reference.
 unfold Reference.v219, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_203_reference s i ghost : to_Zpos (word_203 (encoded_leaves s i ghost)) = Reference.v220 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_203 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_203_size.
 -
 rewrite concat_integer_203 reduction_171_reference log2_202_reference.
 unfold Reference.v220, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_204_reference s i ghost : to_Zpos (word_204 (encoded_leaves s i ghost)) = Reference.v221 s i.
Proof.
 rewrite mux_integer_204 reduction_133_reference log2_168_reference log2_203_reference.
 unfold Reference.v221, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_205_reference s i ghost : to_Zpos (word_205 (encoded_leaves s i ghost)) = Reference.v222 s i.
Proof.
 transitivity (normalize 5 (to_Zpos (word_205 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_205_size.
 -
 rewrite concat_integer_205 reduction_133_reference log2_204_reference.
 unfold Reference.v222, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 5))). apply Z.add_comm.
Qed.
Lemma log2_206_reference s i ghost : to_Zpos (word_206 (encoded_leaves s i ghost)) = Reference.v223 s i.
Proof.
 rewrite mux_integer_206 reduction_55_reference log2_130_reference log2_205_reference.
 unfold Reference.v223, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_207_reference s i ghost : to_Zpos (word_207 (encoded_leaves s i ghost)) = Reference.v224 s i.
Proof.
 pose proof (@to_Zpos_ge0 (word_207 (encoded_leaves s i ghost))) as lower.
 pose proof (@to_Zpos_bounded (word_207 (encoded_leaves s i ghost))) as upper.
 rewrite encoded_word_207_size in upper.
 rewrite concat_integer_207 reduction_55_reference log2_206_reference in lower upper.
 rewrite concat_integer_207 reduction_55_reference log2_206_reference.
 unfold Reference.v224, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite Z.shiftl_mul_pow2; last lia.
 rewrite Z.add_comm. symmetry. apply Z.mod_small.
 cbn [modulus Pos.of_succ_nat Z.of_nat Z.pow Z.pow_pos Pos.iter] in lower, upper |- *. lia.
Qed.
Lemma log2_228_reference s i ghost : to_Zpos (word_228 (encoded_leaves s i ghost)) = Reference.v240 s i.
Proof.
 rewrite mux_integer_228 slice_226_reference slice_227_reference.
 unfold Reference.v240, Reference.v78, Reference.v239, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_229_reference s i ghost : to_Zpos (word_229 (encoded_leaves s i ghost)) = Reference.v241 s i.
Proof.
 rewrite mux_integer_229 slice_225_reference log2_228_reference.
 unfold Reference.v241, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_233_reference s i ghost : to_Zpos (word_233 (encoded_leaves s i ghost)) = Reference.v246 s i.
Proof.
 rewrite mux_integer_233 slice_231_reference slice_232_reference.
 unfold Reference.v246, Reference.v78, Reference.v245, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_234_reference s i ghost : to_Zpos (word_234 (encoded_leaves s i ghost)) = Reference.v247 s i.
Proof.
 rewrite mux_integer_234 slice_230_reference log2_233_reference.
 unfold Reference.v247, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_235_reference s i ghost : to_Zpos (word_235 (encoded_leaves s i ghost)) = Reference.v248 s i.
Proof.
 rewrite mux_integer_235 reduction_224_reference log2_229_reference log2_234_reference.
 unfold Reference.v248, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_236_reference s i ghost : to_Zpos (word_236 (encoded_leaves s i ghost)) = Reference.v249 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_236 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_236_size.
 -
 rewrite concat_integer_236 reduction_224_reference log2_235_reference.
 unfold Reference.v249, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_243_reference s i ghost : to_Zpos (word_243 (encoded_leaves s i ghost)) = Reference.v256 s i.
Proof.
 rewrite mux_integer_243 slice_241_reference slice_242_reference.
 unfold Reference.v256, Reference.v78, Reference.v255, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_244_reference s i ghost : to_Zpos (word_244 (encoded_leaves s i ghost)) = Reference.v257 s i.
Proof.
 rewrite mux_integer_244 slice_240_reference log2_243_reference.
 unfold Reference.v257, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_248_reference s i ghost : to_Zpos (word_248 (encoded_leaves s i ghost)) = Reference.v262 s i.
Proof.
 rewrite mux_integer_248 slice_246_reference slice_247_reference.
 unfold Reference.v262, Reference.v78, Reference.v261, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_249_reference s i ghost : to_Zpos (word_249 (encoded_leaves s i ghost)) = Reference.v263 s i.
Proof.
 rewrite mux_integer_249 slice_245_reference log2_248_reference.
 unfold Reference.v263, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_250_reference s i ghost : to_Zpos (word_250 (encoded_leaves s i ghost)) = Reference.v264 s i.
Proof.
 rewrite mux_integer_250 reduction_239_reference log2_244_reference log2_249_reference.
 unfold Reference.v264, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_251_reference s i ghost : to_Zpos (word_251 (encoded_leaves s i ghost)) = Reference.v265 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_251 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_251_size.
 -
 rewrite concat_integer_251 reduction_239_reference log2_250_reference.
 unfold Reference.v265, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_252_reference s i ghost : to_Zpos (word_252 (encoded_leaves s i ghost)) = Reference.v266 s i.
Proof.
 rewrite mux_integer_252 reduction_221_reference log2_236_reference log2_251_reference.
 unfold Reference.v266, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_253_reference s i ghost : to_Zpos (word_253 (encoded_leaves s i ghost)) = Reference.v267 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_253 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_253_size.
 -
 rewrite concat_integer_253 reduction_221_reference log2_252_reference.
 unfold Reference.v267, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_263_reference s i ghost : to_Zpos (word_263 (encoded_leaves s i ghost)) = Reference.v276 s i.
Proof.
 rewrite mux_integer_263 slice_261_reference slice_262_reference.
 unfold Reference.v276, Reference.v78, Reference.v275, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_264_reference s i ghost : to_Zpos (word_264 (encoded_leaves s i ghost)) = Reference.v277 s i.
Proof.
 rewrite mux_integer_264 slice_260_reference log2_263_reference.
 unfold Reference.v277, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_268_reference s i ghost : to_Zpos (word_268 (encoded_leaves s i ghost)) = Reference.v282 s i.
Proof.
 rewrite mux_integer_268 slice_266_reference slice_267_reference.
 unfold Reference.v282, Reference.v78, Reference.v281, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_269_reference s i ghost : to_Zpos (word_269 (encoded_leaves s i ghost)) = Reference.v283 s i.
Proof.
 rewrite mux_integer_269 slice_265_reference log2_268_reference.
 unfold Reference.v283, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_270_reference s i ghost : to_Zpos (word_270 (encoded_leaves s i ghost)) = Reference.v284 s i.
Proof.
 rewrite mux_integer_270 reduction_259_reference log2_264_reference log2_269_reference.
 unfold Reference.v284, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_271_reference s i ghost : to_Zpos (word_271 (encoded_leaves s i ghost)) = Reference.v285 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_271 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_271_size.
 -
 rewrite concat_integer_271 reduction_259_reference log2_270_reference.
 unfold Reference.v285, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_278_reference s i ghost : to_Zpos (word_278 (encoded_leaves s i ghost)) = Reference.v292 s i.
Proof.
 rewrite mux_integer_278 slice_276_reference slice_277_reference.
 unfold Reference.v292, Reference.v78, Reference.v291, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_279_reference s i ghost : to_Zpos (word_279 (encoded_leaves s i ghost)) = Reference.v293 s i.
Proof.
 rewrite mux_integer_279 slice_275_reference log2_278_reference.
 unfold Reference.v293, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_283_reference s i ghost : to_Zpos (word_283 (encoded_leaves s i ghost)) = Reference.v298 s i.
Proof.
 rewrite mux_integer_283 slice_281_reference slice_282_reference.
 unfold Reference.v298, Reference.v78, Reference.v297, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_284_reference s i ghost : to_Zpos (word_284 (encoded_leaves s i ghost)) = Reference.v299 s i.
Proof.
 rewrite mux_integer_284 slice_280_reference log2_283_reference.
 unfold Reference.v299, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_285_reference s i ghost : to_Zpos (word_285 (encoded_leaves s i ghost)) = Reference.v300 s i.
Proof.
 rewrite mux_integer_285 reduction_274_reference log2_279_reference log2_284_reference.
 unfold Reference.v300, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_286_reference s i ghost : to_Zpos (word_286 (encoded_leaves s i ghost)) = Reference.v301 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_286 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_286_size.
 -
 rewrite concat_integer_286 reduction_274_reference log2_285_reference.
 unfold Reference.v301, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_287_reference s i ghost : to_Zpos (word_287 (encoded_leaves s i ghost)) = Reference.v302 s i.
Proof.
 rewrite mux_integer_287 reduction_256_reference log2_271_reference log2_286_reference.
 unfold Reference.v302, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_288_reference s i ghost : to_Zpos (word_288 (encoded_leaves s i ghost)) = Reference.v303 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_288 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_288_size.
 -
 rewrite concat_integer_288 reduction_256_reference log2_287_reference.
 unfold Reference.v303, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_289_reference s i ghost : to_Zpos (word_289 (encoded_leaves s i ghost)) = Reference.v304 s i.
Proof.
 rewrite mux_integer_289 reduction_218_reference log2_253_reference log2_288_reference.
 unfold Reference.v304, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_290_reference s i ghost : to_Zpos (word_290 (encoded_leaves s i ghost)) = Reference.v305 s i.
Proof.
 transitivity (normalize 5 (to_Zpos (word_290 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_290_size.
 -
 rewrite concat_integer_290 reduction_218_reference log2_289_reference.
 unfold Reference.v305, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 5))). apply Z.add_comm.
Qed.
Lemma log2_303_reference s i ghost : to_Zpos (word_303 (encoded_leaves s i ghost)) = Reference.v316 s i.
Proof.
 rewrite mux_integer_303 slice_301_reference slice_302_reference.
 unfold Reference.v316, Reference.v78, Reference.v315, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_304_reference s i ghost : to_Zpos (word_304 (encoded_leaves s i ghost)) = Reference.v317 s i.
Proof.
 rewrite mux_integer_304 slice_300_reference log2_303_reference.
 unfold Reference.v317, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_308_reference s i ghost : to_Zpos (word_308 (encoded_leaves s i ghost)) = Reference.v322 s i.
Proof.
 rewrite mux_integer_308 slice_306_reference slice_307_reference.
 unfold Reference.v322, Reference.v78, Reference.v321, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_309_reference s i ghost : to_Zpos (word_309 (encoded_leaves s i ghost)) = Reference.v323 s i.
Proof.
 rewrite mux_integer_309 slice_305_reference log2_308_reference.
 unfold Reference.v323, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_310_reference s i ghost : to_Zpos (word_310 (encoded_leaves s i ghost)) = Reference.v324 s i.
Proof.
 rewrite mux_integer_310 reduction_299_reference log2_304_reference log2_309_reference.
 unfold Reference.v324, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_311_reference s i ghost : to_Zpos (word_311 (encoded_leaves s i ghost)) = Reference.v325 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_311 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_311_size.
 -
 rewrite concat_integer_311 reduction_299_reference log2_310_reference.
 unfold Reference.v325, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_318_reference s i ghost : to_Zpos (word_318 (encoded_leaves s i ghost)) = Reference.v332 s i.
Proof.
 rewrite mux_integer_318 slice_316_reference slice_317_reference.
 unfold Reference.v332, Reference.v78, Reference.v331, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_319_reference s i ghost : to_Zpos (word_319 (encoded_leaves s i ghost)) = Reference.v333 s i.
Proof.
 rewrite mux_integer_319 slice_315_reference log2_318_reference.
 unfold Reference.v333, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_323_reference s i ghost : to_Zpos (word_323 (encoded_leaves s i ghost)) = Reference.v338 s i.
Proof.
 rewrite mux_integer_323 slice_321_reference slice_322_reference.
 unfold Reference.v338, Reference.v78, Reference.v337, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_324_reference s i ghost : to_Zpos (word_324 (encoded_leaves s i ghost)) = Reference.v339 s i.
Proof.
 rewrite mux_integer_324 slice_320_reference log2_323_reference.
 unfold Reference.v339, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_325_reference s i ghost : to_Zpos (word_325 (encoded_leaves s i ghost)) = Reference.v340 s i.
Proof.
 rewrite mux_integer_325 reduction_314_reference log2_319_reference log2_324_reference.
 unfold Reference.v340, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_326_reference s i ghost : to_Zpos (word_326 (encoded_leaves s i ghost)) = Reference.v341 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_326 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_326_size.
 -
 rewrite concat_integer_326 reduction_314_reference log2_325_reference.
 unfold Reference.v341, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_327_reference s i ghost : to_Zpos (word_327 (encoded_leaves s i ghost)) = Reference.v342 s i.
Proof.
 rewrite mux_integer_327 reduction_296_reference log2_311_reference log2_326_reference.
 unfold Reference.v342, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_328_reference s i ghost : to_Zpos (word_328 (encoded_leaves s i ghost)) = Reference.v343 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_328 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_328_size.
 -
 rewrite concat_integer_328 reduction_296_reference log2_327_reference.
 unfold Reference.v343, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_338_reference s i ghost : to_Zpos (word_338 (encoded_leaves s i ghost)) = Reference.v352 s i.
Proof.
 rewrite mux_integer_338 slice_336_reference slice_337_reference.
 unfold Reference.v352, Reference.v78, Reference.v351, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_339_reference s i ghost : to_Zpos (word_339 (encoded_leaves s i ghost)) = Reference.v353 s i.
Proof.
 rewrite mux_integer_339 slice_335_reference log2_338_reference.
 unfold Reference.v353, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_343_reference s i ghost : to_Zpos (word_343 (encoded_leaves s i ghost)) = Reference.v358 s i.
Proof.
 rewrite mux_integer_343 slice_341_reference slice_342_reference.
 unfold Reference.v358, Reference.v78, Reference.v357, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_344_reference s i ghost : to_Zpos (word_344 (encoded_leaves s i ghost)) = Reference.v359 s i.
Proof.
 rewrite mux_integer_344 slice_340_reference log2_343_reference.
 unfold Reference.v359, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_345_reference s i ghost : to_Zpos (word_345 (encoded_leaves s i ghost)) = Reference.v360 s i.
Proof.
 rewrite mux_integer_345 reduction_334_reference log2_339_reference log2_344_reference.
 unfold Reference.v360, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_346_reference s i ghost : to_Zpos (word_346 (encoded_leaves s i ghost)) = Reference.v361 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_346 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_346_size.
 -
 rewrite concat_integer_346 reduction_334_reference log2_345_reference.
 unfold Reference.v361, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_353_reference s i ghost : to_Zpos (word_353 (encoded_leaves s i ghost)) = Reference.v368 s i.
Proof.
 rewrite mux_integer_353 slice_351_reference slice_352_reference.
 unfold Reference.v368, Reference.v78, Reference.v367, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_354_reference s i ghost : to_Zpos (word_354 (encoded_leaves s i ghost)) = Reference.v369 s i.
Proof.
 rewrite mux_integer_354 slice_350_reference log2_353_reference.
 unfold Reference.v369, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_358_reference s i ghost : to_Zpos (word_358 (encoded_leaves s i ghost)) = Reference.v374 s i.
Proof.
 rewrite mux_integer_358 slice_356_reference slice_357_reference.
 unfold Reference.v374, Reference.v78, Reference.v373, Reference.v26, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_359_reference s i ghost : to_Zpos (word_359 (encoded_leaves s i ghost)) = Reference.v375 s i.
Proof.
 rewrite mux_integer_359 slice_355_reference log2_358_reference.
 unfold Reference.v375, Reference.v76, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_360_reference s i ghost : to_Zpos (word_360 (encoded_leaves s i ghost)) = Reference.v376 s i.
Proof.
 rewrite mux_integer_360 reduction_349_reference log2_354_reference log2_359_reference.
 unfold Reference.v376, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_361_reference s i ghost : to_Zpos (word_361 (encoded_leaves s i ghost)) = Reference.v377 s i.
Proof.
 transitivity (normalize 3 (to_Zpos (word_361 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_361_size.
 -
 rewrite concat_integer_361 reduction_349_reference log2_360_reference.
 unfold Reference.v377, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 3))). apply Z.add_comm.
Qed.
Lemma log2_362_reference s i ghost : to_Zpos (word_362 (encoded_leaves s i ghost)) = Reference.v378 s i.
Proof.
 rewrite mux_integer_362 reduction_331_reference log2_346_reference log2_361_reference.
 unfold Reference.v378, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_363_reference s i ghost : to_Zpos (word_363 (encoded_leaves s i ghost)) = Reference.v379 s i.
Proof.
 transitivity (normalize 4 (to_Zpos (word_363 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_363_size.
 -
 rewrite concat_integer_363 reduction_331_reference log2_362_reference.
 unfold Reference.v379, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 4))). apply Z.add_comm.
Qed.
Lemma log2_364_reference s i ghost : to_Zpos (word_364 (encoded_leaves s i ghost)) = Reference.v380 s i.
Proof.
 rewrite mux_integer_364 reduction_293_reference log2_328_reference log2_363_reference.
 unfold Reference.v380, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_365_reference s i ghost : to_Zpos (word_365 (encoded_leaves s i ghost)) = Reference.v381 s i.
Proof.
 transitivity (normalize 5 (to_Zpos (word_365 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_365_size.
 -
 rewrite concat_integer_365 reduction_293_reference log2_364_reference.
 unfold Reference.v381, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 5))). apply Z.add_comm.
Qed.
Lemma log2_366_reference s i ghost : to_Zpos (word_366 (encoded_leaves s i ghost)) = Reference.v382 s i.
Proof.
 rewrite mux_integer_366 reduction_215_reference log2_290_reference log2_365_reference.
 unfold Reference.v382, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_367_reference s i ghost : to_Zpos (word_367 (encoded_leaves s i ghost)) = Reference.v383 s i.
Proof.
 transitivity (normalize 6 (to_Zpos (word_367 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_367_size.
 -
 rewrite concat_integer_367 reduction_215_reference log2_366_reference.
 unfold Reference.v383, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 6))). apply Z.add_comm.
Qed.
Lemma log2_368_reference s i ghost : to_Zpos (word_368 (encoded_leaves s i ghost)) = Reference.v384 s i.
Proof.
 rewrite mux_integer_368 reduction_212_reference log2_367_reference.
 unfold Reference.v384, Reference.v62, Radix2Divider.CIRCTBits.word, normalize, modulus.
 repeat match goal with |- context [if ?guard then _ else _] => destruct guard end;
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r;
 repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.
Lemma log2_369_reference s i ghost : to_Zpos (word_369 (encoded_leaves s i ghost)) = Reference.v385 s i.
Proof.
 transitivity (normalize 7 (to_Zpos (word_369 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_369_size.
 -
 rewrite concat_integer_369 reduction_212_reference log2_368_reference.
 unfold Reference.v385, Radix2Divider.CIRCTBits.word, normalize, modulus.
 rewrite Z.shiftl_mul_pow2; last lia.
 apply (f_equal (fun z : Z => z mod (2 ^ Z.of_nat 7))). apply Z.add_comm.
Qed.
Print Assumptions log2_207_reference.
Print Assumptions log2_367_reference.
