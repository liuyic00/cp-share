From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation ReferenceNodes Slices Typing.
Local Open Scope Z_scope.
Lemma fold_or_nonzero bits : foldr orb false bits = negb (is_zero bits).
Proof. induction bits as [|bit bits IH]; first reflexivity.
 destruct bit; cbn [foldr is_zero all]; [reflexivity|exact IH]. Qed.

Transparent word_55.
Lemma reduction_55_reference s i ghost : to_Zpos (word_55 (encoded_leaves s i ghost)) = Reference.v65 s i.
Proof. unfold word_55, closed_55, expr_55, word_of_eval.
 change (to_Zpos [::foldr orb false (word_53 (encoded_leaves s i ghost))] = Reference.v65 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_53_reference.
 unfold Reference.v65, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v63 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v63 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v63 s i) 0); reflexivity. Qed.
Opaque word_55.
Transparent word_58.
Lemma reduction_58_reference s i ghost : to_Zpos (word_58 (encoded_leaves s i ghost)) = Reference.v68 s i.
Proof. unfold word_58, closed_58, expr_58, word_of_eval.
 change (to_Zpos [::foldr orb false (word_56 (encoded_leaves s i ghost))] = Reference.v68 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_56_reference.
 unfold Reference.v68, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v66 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v66 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v66 s i) 0); reflexivity. Qed.
Opaque word_58.
Transparent word_61.
Lemma reduction_61_reference s i ghost : to_Zpos (word_61 (encoded_leaves s i ghost)) = Reference.v71 s i.
Proof. unfold word_61, closed_61, expr_61, word_of_eval.
 change (to_Zpos [::foldr orb false (word_59 (encoded_leaves s i ghost))] = Reference.v71 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_59_reference.
 unfold Reference.v71, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v69 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v69 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v69 s i) 0); reflexivity. Qed.
Opaque word_61.
Transparent word_64.
Lemma reduction_64_reference s i ghost : to_Zpos (word_64 (encoded_leaves s i ghost)) = Reference.v74 s i.
Proof. unfold word_64, closed_64, expr_64, word_of_eval.
 change (to_Zpos [::foldr orb false (word_62 (encoded_leaves s i ghost))] = Reference.v74 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_62_reference.
 unfold Reference.v74, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v72 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v72 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v72 s i) 0); reflexivity. Qed.
Opaque word_64.
Transparent word_79.
Lemma reduction_79_reference s i ghost : to_Zpos (word_79 (encoded_leaves s i ghost)) = Reference.v92 s i.
Proof. unfold word_79, closed_79, expr_79, word_of_eval.
 change (to_Zpos [::foldr orb false (word_77 (encoded_leaves s i ghost))] = Reference.v92 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_77_reference.
 unfold Reference.v92, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v91 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v91 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v91 s i) 0); reflexivity. Qed.
Opaque word_79.
Transparent word_96.
Lemma reduction_96_reference s i ghost : to_Zpos (word_96 (encoded_leaves s i ghost)) = Reference.v110 s i.
Proof. unfold word_96, closed_96, expr_96, word_of_eval.
 change (to_Zpos [::foldr orb false (word_94 (encoded_leaves s i ghost))] = Reference.v110 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_94_reference.
 unfold Reference.v110, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v109 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v109 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v109 s i) 0); reflexivity. Qed.
Opaque word_96.
Transparent word_99.
Lemma reduction_99_reference s i ghost : to_Zpos (word_99 (encoded_leaves s i ghost)) = Reference.v112 s i.
Proof. unfold word_99, closed_99, expr_99, word_of_eval.
 change (to_Zpos [::foldr orb false (word_97 (encoded_leaves s i ghost))] = Reference.v112 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_97_reference.
 unfold Reference.v112, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v111 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v111 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v111 s i) 0); reflexivity. Qed.
Opaque word_99.
Transparent word_114.
Lemma reduction_114_reference s i ghost : to_Zpos (word_114 (encoded_leaves s i ghost)) = Reference.v128 s i.
Proof. unfold word_114, closed_114, expr_114, word_of_eval.
 change (to_Zpos [::foldr orb false (word_112 (encoded_leaves s i ghost))] = Reference.v128 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_112_reference.
 unfold Reference.v128, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v127 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v127 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v127 s i) 0); reflexivity. Qed.
Opaque word_114.
Transparent word_133.
Lemma reduction_133_reference s i ghost : to_Zpos (word_133 (encoded_leaves s i ghost)) = Reference.v148 s i.
Proof. unfold word_133, closed_133, expr_133, word_of_eval.
 change (to_Zpos [::foldr orb false (word_131 (encoded_leaves s i ghost))] = Reference.v148 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_131_reference.
 unfold Reference.v148, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v147 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v147 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v147 s i) 0); reflexivity. Qed.
Opaque word_133.
Transparent word_136.
Lemma reduction_136_reference s i ghost : to_Zpos (word_136 (encoded_leaves s i ghost)) = Reference.v150 s i.
Proof. unfold word_136, closed_136, expr_136, word_of_eval.
 change (to_Zpos [::foldr orb false (word_134 (encoded_leaves s i ghost))] = Reference.v150 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_134_reference.
 unfold Reference.v150, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v149 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v149 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v149 s i) 0); reflexivity. Qed.
Opaque word_136.
Transparent word_139.
Lemma reduction_139_reference s i ghost : to_Zpos (word_139 (encoded_leaves s i ghost)) = Reference.v152 s i.
Proof. unfold word_139, closed_139, expr_139, word_of_eval.
 change (to_Zpos [::foldr orb false (word_137 (encoded_leaves s i ghost))] = Reference.v152 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_137_reference.
 unfold Reference.v152, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v151 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v151 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v151 s i) 0); reflexivity. Qed.
Opaque word_139.
Transparent word_154.
Lemma reduction_154_reference s i ghost : to_Zpos (word_154 (encoded_leaves s i ghost)) = Reference.v168 s i.
Proof. unfold word_154, closed_154, expr_154, word_of_eval.
 change (to_Zpos [::foldr orb false (word_152 (encoded_leaves s i ghost))] = Reference.v168 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_152_reference.
 unfold Reference.v168, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v167 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v167 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v167 s i) 0); reflexivity. Qed.
Opaque word_154.
Transparent word_171.
Lemma reduction_171_reference s i ghost : to_Zpos (word_171 (encoded_leaves s i ghost)) = Reference.v186 s i.
Proof. unfold word_171, closed_171, expr_171, word_of_eval.
 change (to_Zpos [::foldr orb false (word_169 (encoded_leaves s i ghost))] = Reference.v186 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_169_reference.
 unfold Reference.v186, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v185 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v185 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v185 s i) 0); reflexivity. Qed.
Opaque word_171.
Transparent word_174.
Lemma reduction_174_reference s i ghost : to_Zpos (word_174 (encoded_leaves s i ghost)) = Reference.v188 s i.
Proof. unfold word_174, closed_174, expr_174, word_of_eval.
 change (to_Zpos [::foldr orb false (word_172 (encoded_leaves s i ghost))] = Reference.v188 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_172_reference.
 unfold Reference.v188, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v187 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v187 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v187 s i) 0); reflexivity. Qed.
Opaque word_174.
Transparent word_189.
Lemma reduction_189_reference s i ghost : to_Zpos (word_189 (encoded_leaves s i ghost)) = Reference.v204 s i.
Proof. unfold word_189, closed_189, expr_189, word_of_eval.
 change (to_Zpos [::foldr orb false (word_187 (encoded_leaves s i ghost))] = Reference.v204 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_187_reference.
 unfold Reference.v204, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v203 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v203 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v203 s i) 0); reflexivity. Qed.
Opaque word_189.
Transparent word_212.
Lemma reduction_212_reference s i ghost : to_Zpos (word_212 (encoded_leaves s i ghost)) = Reference.v227 s i.
Proof. unfold word_212, closed_212, expr_212, word_of_eval.
 change (to_Zpos [::foldr orb false (word_210 (encoded_leaves s i ghost))] = Reference.v227 s i).
 rewrite -(slice_210_reference s i ghost).
 pose proof (encoded_word_210_size s i ghost) as sized.
 destruct (word_210 (encoded_leaves s i ghost)) as [|bit bits]; first discriminate.
 destruct bits; last discriminate. destruct bit; reflexivity. Qed.
Opaque word_212.
Transparent word_215.
Lemma reduction_215_reference s i ghost : to_Zpos (word_215 (encoded_leaves s i ghost)) = Reference.v229 s i.
Proof. unfold word_215, closed_215, expr_215, word_of_eval.
 change (to_Zpos [::foldr orb false (word_213 (encoded_leaves s i ghost))] = Reference.v229 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_213_reference.
 unfold Reference.v229, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v228 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v228 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v228 s i) 0); reflexivity. Qed.
Opaque word_215.
Transparent word_218.
Lemma reduction_218_reference s i ghost : to_Zpos (word_218 (encoded_leaves s i ghost)) = Reference.v231 s i.
Proof. unfold word_218, closed_218, expr_218, word_of_eval.
 change (to_Zpos [::foldr orb false (word_216 (encoded_leaves s i ghost))] = Reference.v231 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_216_reference.
 unfold Reference.v231, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v230 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v230 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v230 s i) 0); reflexivity. Qed.
Opaque word_218.
Transparent word_221.
Lemma reduction_221_reference s i ghost : to_Zpos (word_221 (encoded_leaves s i ghost)) = Reference.v233 s i.
Proof. unfold word_221, closed_221, expr_221, word_of_eval.
 change (to_Zpos [::foldr orb false (word_219 (encoded_leaves s i ghost))] = Reference.v233 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_219_reference.
 unfold Reference.v233, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v232 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v232 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v232 s i) 0); reflexivity. Qed.
Opaque word_221.
Transparent word_224.
Lemma reduction_224_reference s i ghost : to_Zpos (word_224 (encoded_leaves s i ghost)) = Reference.v235 s i.
Proof. unfold word_224, closed_224, expr_224, word_of_eval.
 change (to_Zpos [::foldr orb false (word_222 (encoded_leaves s i ghost))] = Reference.v235 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_222_reference.
 unfold Reference.v235, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v234 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v234 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v234 s i) 0); reflexivity. Qed.
Opaque word_224.
Transparent word_239.
Lemma reduction_239_reference s i ghost : to_Zpos (word_239 (encoded_leaves s i ghost)) = Reference.v251 s i.
Proof. unfold word_239, closed_239, expr_239, word_of_eval.
 change (to_Zpos [::foldr orb false (word_237 (encoded_leaves s i ghost))] = Reference.v251 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_237_reference.
 unfold Reference.v251, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v250 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v250 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v250 s i) 0); reflexivity. Qed.
Opaque word_239.
Transparent word_256.
Lemma reduction_256_reference s i ghost : to_Zpos (word_256 (encoded_leaves s i ghost)) = Reference.v269 s i.
Proof. unfold word_256, closed_256, expr_256, word_of_eval.
 change (to_Zpos [::foldr orb false (word_254 (encoded_leaves s i ghost))] = Reference.v269 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_254_reference.
 unfold Reference.v269, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v268 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v268 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v268 s i) 0); reflexivity. Qed.
Opaque word_256.
Transparent word_259.
Lemma reduction_259_reference s i ghost : to_Zpos (word_259 (encoded_leaves s i ghost)) = Reference.v271 s i.
Proof. unfold word_259, closed_259, expr_259, word_of_eval.
 change (to_Zpos [::foldr orb false (word_257 (encoded_leaves s i ghost))] = Reference.v271 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_257_reference.
 unfold Reference.v271, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v270 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v270 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v270 s i) 0); reflexivity. Qed.
Opaque word_259.
Transparent word_274.
Lemma reduction_274_reference s i ghost : to_Zpos (word_274 (encoded_leaves s i ghost)) = Reference.v287 s i.
Proof. unfold word_274, closed_274, expr_274, word_of_eval.
 change (to_Zpos [::foldr orb false (word_272 (encoded_leaves s i ghost))] = Reference.v287 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_272_reference.
 unfold Reference.v287, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v286 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v286 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v286 s i) 0); reflexivity. Qed.
Opaque word_274.
Transparent word_293.
Lemma reduction_293_reference s i ghost : to_Zpos (word_293 (encoded_leaves s i ghost)) = Reference.v307 s i.
Proof. unfold word_293, closed_293, expr_293, word_of_eval.
 change (to_Zpos [::foldr orb false (word_291 (encoded_leaves s i ghost))] = Reference.v307 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_291_reference.
 unfold Reference.v307, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v306 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v306 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v306 s i) 0); reflexivity. Qed.
Opaque word_293.
Transparent word_296.
Lemma reduction_296_reference s i ghost : to_Zpos (word_296 (encoded_leaves s i ghost)) = Reference.v309 s i.
Proof. unfold word_296, closed_296, expr_296, word_of_eval.
 change (to_Zpos [::foldr orb false (word_294 (encoded_leaves s i ghost))] = Reference.v309 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_294_reference.
 unfold Reference.v309, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v308 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v308 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v308 s i) 0); reflexivity. Qed.
Opaque word_296.
Transparent word_299.
Lemma reduction_299_reference s i ghost : to_Zpos (word_299 (encoded_leaves s i ghost)) = Reference.v311 s i.
Proof. unfold word_299, closed_299, expr_299, word_of_eval.
 change (to_Zpos [::foldr orb false (word_297 (encoded_leaves s i ghost))] = Reference.v311 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_297_reference.
 unfold Reference.v311, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v310 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v310 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v310 s i) 0); reflexivity. Qed.
Opaque word_299.
Transparent word_314.
Lemma reduction_314_reference s i ghost : to_Zpos (word_314 (encoded_leaves s i ghost)) = Reference.v327 s i.
Proof. unfold word_314, closed_314, expr_314, word_of_eval.
 change (to_Zpos [::foldr orb false (word_312 (encoded_leaves s i ghost))] = Reference.v327 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_312_reference.
 unfold Reference.v327, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v326 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v326 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v326 s i) 0); reflexivity. Qed.
Opaque word_314.
Transparent word_331.
Lemma reduction_331_reference s i ghost : to_Zpos (word_331 (encoded_leaves s i ghost)) = Reference.v345 s i.
Proof. unfold word_331, closed_331, expr_331, word_of_eval.
 change (to_Zpos [::foldr orb false (word_329 (encoded_leaves s i ghost))] = Reference.v345 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_329_reference.
 unfold Reference.v345, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v344 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v344 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v344 s i) 0); reflexivity. Qed.
Opaque word_331.
Transparent word_334.
Lemma reduction_334_reference s i ghost : to_Zpos (word_334 (encoded_leaves s i ghost)) = Reference.v347 s i.
Proof. unfold word_334, closed_334, expr_334, word_of_eval.
 change (to_Zpos [::foldr orb false (word_332 (encoded_leaves s i ghost))] = Reference.v347 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_332_reference.
 unfold Reference.v347, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v346 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v346 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v346 s i) 0); reflexivity. Qed.
Opaque word_334.
Transparent word_349.
Lemma reduction_349_reference s i ghost : to_Zpos (word_349 (encoded_leaves s i ghost)) = Reference.v363 s i.
Proof. unfold word_349, closed_349, expr_349, word_of_eval.
 change (to_Zpos [::foldr orb false (word_347 (encoded_leaves s i ghost))] = Reference.v363 s i).
 rewrite unsigned_singleton fold_or_nonzero is_zero_unsigned slice_347_reference.
 unfold Reference.v363, Radix2Divider.CIRCTBits.word.
 change ((if negb (Z.eqb (Reference.v362 s i) 0) then 1 else 0) = ((if negb (Z.eqb (Reference.v362 s i) 0) then 1 else 0) mod 2)).
 destruct (Z.eqb (Reference.v362 s i) 0); reflexivity. Qed.
Opaque word_349.
Print Assumptions reduction_55_reference.
