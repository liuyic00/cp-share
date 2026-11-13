From Coq Require Import ZArith Lia.
From Proofs Require Import LeadingBits RadixLeadingLeaves RadixLeadingMerge.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import LeadingBits.LeadingBits RadixLeadingLeaves.RadixLeadingLeaves RadixLeadingMerge.RadixLeadingMerge.
Open Scope Z_scope.
Module RadixLeadingTree.
Lemma correct_82 s i : Encodes (chunk 4 60 (word 64 (r5_nbReg s))) (v82 s i) /\ 0 <= v82 s i < 4.
Proof. rewrite node_82.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 60))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_88 s i : Encodes (chunk 4 56 (word 64 (r5_nbReg s))) (v88 s i) /\ 0 <= v88 s i < 4.
Proof. rewrite node_88.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 56))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_98 s i : Encodes (chunk 4 52 (word 64 (r5_nbReg s))) (v98 s i) /\ 0 <= v98 s i < 4.
Proof. rewrite node_98.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 52))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_104 s i : Encodes (chunk 4 48 (word 64 (r5_nbReg s))) (v104 s i) /\ 0 <= v104 s i < 4.
Proof. rewrite node_104.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 48))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_118 s i : Encodes (chunk 4 44 (word 64 (r5_nbReg s))) (v118 s i) /\ 0 <= v118 s i < 4.
Proof. rewrite node_118.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 44))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_124 s i : Encodes (chunk 4 40 (word 64 (r5_nbReg s))) (v124 s i) /\ 0 <= v124 s i < 4.
Proof. rewrite node_124.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 40))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_134 s i : Encodes (chunk 4 36 (word 64 (r5_nbReg s))) (v134 s i) /\ 0 <= v134 s i < 4.
Proof. rewrite node_134.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 36))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_140 s i : Encodes (chunk 4 32 (word 64 (r5_nbReg s))) (v140 s i) /\ 0 <= v140 s i < 4.
Proof. rewrite node_140.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 32))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_158 s i : Encodes (chunk 4 28 (word 64 (r5_nbReg s))) (v158 s i) /\ 0 <= v158 s i < 4.
Proof. rewrite node_158.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 28))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_164 s i : Encodes (chunk 4 24 (word 64 (r5_nbReg s))) (v164 s i) /\ 0 <= v164 s i < 4.
Proof. rewrite node_164.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 24))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_174 s i : Encodes (chunk 4 20 (word 64 (r5_nbReg s))) (v174 s i) /\ 0 <= v174 s i < 4.
Proof. rewrite node_174.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 20))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_180 s i : Encodes (chunk 4 16 (word 64 (r5_nbReg s))) (v180 s i) /\ 0 <= v180 s i < 4.
Proof. rewrite node_180.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 16))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_194 s i : Encodes (chunk 4 12 (word 64 (r5_nbReg s))) (v194 s i) /\ 0 <= v194 s i < 4.
Proof. rewrite node_194.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 12))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_200 s i : Encodes (chunk 4 8 (word 64 (r5_nbReg s))) (v200 s i) /\ 0 <= v200 s i < 4.
Proof. rewrite node_200.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 8))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_210 s i : Encodes (chunk 4 4 (word 64 (r5_nbReg s))) (v210 s i) /\ 0 <= v210 s i < 4.
Proof. rewrite node_210.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 4))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_216 s i : Encodes (chunk 4 0 (word 64 (r5_nbReg s))) (v216 s i) /\ 0 <= v216 s i < 4.
Proof. rewrite node_216.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 0))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_241 s i : Encodes (chunk 4 60 (word 65 (r6_naValx2Reg s))) (v241 s i) /\ 0 <= v241 s i < 4.
Proof. rewrite node_241.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 60))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_247 s i : Encodes (chunk 4 56 (word 65 (r6_naValx2Reg s))) (v247 s i) /\ 0 <= v247 s i < 4.
Proof. rewrite node_247.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 56))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_257 s i : Encodes (chunk 4 52 (word 65 (r6_naValx2Reg s))) (v257 s i) /\ 0 <= v257 s i < 4.
Proof. rewrite node_257.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 52))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_263 s i : Encodes (chunk 4 48 (word 65 (r6_naValx2Reg s))) (v263 s i) /\ 0 <= v263 s i < 4.
Proof. rewrite node_263.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 48))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_277 s i : Encodes (chunk 4 44 (word 65 (r6_naValx2Reg s))) (v277 s i) /\ 0 <= v277 s i < 4.
Proof. rewrite node_277.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 44))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_283 s i : Encodes (chunk 4 40 (word 65 (r6_naValx2Reg s))) (v283 s i) /\ 0 <= v283 s i < 4.
Proof. rewrite node_283.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 40))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_293 s i : Encodes (chunk 4 36 (word 65 (r6_naValx2Reg s))) (v293 s i) /\ 0 <= v293 s i < 4.
Proof. rewrite node_293.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 36))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_299 s i : Encodes (chunk 4 32 (word 65 (r6_naValx2Reg s))) (v299 s i) /\ 0 <= v299 s i < 4.
Proof. rewrite node_299.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 32))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_317 s i : Encodes (chunk 4 28 (word 65 (r6_naValx2Reg s))) (v317 s i) /\ 0 <= v317 s i < 4.
Proof. rewrite node_317.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 28))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_323 s i : Encodes (chunk 4 24 (word 65 (r6_naValx2Reg s))) (v323 s i) /\ 0 <= v323 s i < 4.
Proof. rewrite node_323.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 24))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_333 s i : Encodes (chunk 4 20 (word 65 (r6_naValx2Reg s))) (v333 s i) /\ 0 <= v333 s i < 4.
Proof. rewrite node_333.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 20))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_339 s i : Encodes (chunk 4 16 (word 65 (r6_naValx2Reg s))) (v339 s i) /\ 0 <= v339 s i < 4.
Proof. rewrite node_339.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 16))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_353 s i : Encodes (chunk 4 12 (word 65 (r6_naValx2Reg s))) (v353 s i) /\ 0 <= v353 s i < 4.
Proof. rewrite node_353.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 12))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_359 s i : Encodes (chunk 4 8 (word 65 (r6_naValx2Reg s))) (v359 s i) /\ 0 <= v359 s i < 4.
Proof. rewrite node_359.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 8))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_369 s i : Encodes (chunk 4 4 (word 65 (r6_naValx2Reg s))) (v369 s i) /\ 0 <= v369 s i < 4.
Proof. rewrite node_369.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 4))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_375 s i : Encodes (chunk 4 0 (word 65 (r6_naValx2Reg s))) (v375 s i) /\ 0 <= v375 s i < 4.
Proof. rewrite node_375.
  pose proof (leaf4_correct (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 0))) as h.
  unfold Words.word, word in h; rewrite Z.mod_mod in h by discriminate; exact h. Qed.

Lemma correct_90 s i : Encodes (chunk 8 56 (word 64 (r5_nbReg s))) (v90 s i) /\ 0 <= v90 s i < 8.
Proof.
  destruct (correct_82 s i) as [hh rh].
  destruct (correct_88 s i) as [hl rl].
  assert (wire : v90 s i = combine 4 (chunk 4 60 (word 64 (r5_nbReg s))) (v82 s i) (v88 s i)).
  { unfold v90, v89, v74, v72, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 60 (word 64 (r5_nbReg s))) (v82 s i) (v88 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 56 (word 64 (r5_nbReg s)) (v82 s i) (v88 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 60 (word 64 (r5_nbReg s))) (v82 s i) (v88 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_106 s i : Encodes (chunk 8 48 (word 64 (r5_nbReg s))) (v106 s i) /\ 0 <= v106 s i < 8.
Proof.
  destruct (correct_98 s i) as [hh rh].
  destruct (correct_104 s i) as [hl rl].
  assert (wire : v106 s i = combine 4 (chunk 4 52 (word 64 (r5_nbReg s))) (v98 s i) (v104 s i)).
  { unfold v106, v105, v92, v91, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 52 (word 64 (r5_nbReg s))) (v98 s i) (v104 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 48 (word 64 (r5_nbReg s)) (v98 s i) (v104 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 52 (word 64 (r5_nbReg s))) (v98 s i) (v104 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_108 s i : Encodes (chunk 16 48 (word 64 (r5_nbReg s))) (v108 s i) /\ 0 <= v108 s i < 16.
Proof.
  destruct (correct_90 s i) as [hh rh].
  destruct (correct_106 s i) as [hl rl].
  assert (wire : v108 s i = combine 8 (chunk 8 56 (word 64 (r5_nbReg s))) (v90 s i) (v106 s i)).
  { unfold v108, v107, v71, v69, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 56 (word 64 (r5_nbReg s))) (v90 s i) (v106 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 48 (word 64 (r5_nbReg s)) (v90 s i) (v106 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 56 (word 64 (r5_nbReg s))) (v90 s i) (v106 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_126 s i : Encodes (chunk 8 40 (word 64 (r5_nbReg s))) (v126 s i) /\ 0 <= v126 s i < 8.
Proof.
  destruct (correct_118 s i) as [hh rh].
  destruct (correct_124 s i) as [hl rl].
  assert (wire : v126 s i = combine 4 (chunk 4 44 (word 64 (r5_nbReg s))) (v118 s i) (v124 s i)).
  { unfold v126, v125, v112, v111, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 44 (word 64 (r5_nbReg s))) (v118 s i) (v124 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 40 (word 64 (r5_nbReg s)) (v118 s i) (v124 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 44 (word 64 (r5_nbReg s))) (v118 s i) (v124 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_142 s i : Encodes (chunk 8 32 (word 64 (r5_nbReg s))) (v142 s i) /\ 0 <= v142 s i < 8.
Proof.
  destruct (correct_134 s i) as [hh rh].
  destruct (correct_140 s i) as [hl rl].
  assert (wire : v142 s i = combine 4 (chunk 4 36 (word 64 (r5_nbReg s))) (v134 s i) (v140 s i)).
  { unfold v142, v141, v128, v127, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 36 (word 64 (r5_nbReg s))) (v134 s i) (v140 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 32 (word 64 (r5_nbReg s)) (v134 s i) (v140 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 36 (word 64 (r5_nbReg s))) (v134 s i) (v140 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_144 s i : Encodes (chunk 16 32 (word 64 (r5_nbReg s))) (v144 s i) /\ 0 <= v144 s i < 16.
Proof.
  destruct (correct_126 s i) as [hh rh].
  destruct (correct_142 s i) as [hl rl].
  assert (wire : v144 s i = combine 8 (chunk 8 40 (word 64 (r5_nbReg s))) (v126 s i) (v142 s i)).
  { unfold v144, v143, v110, v109, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 40 (word 64 (r5_nbReg s))) (v126 s i) (v142 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 32 (word 64 (r5_nbReg s)) (v126 s i) (v142 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 40 (word 64 (r5_nbReg s))) (v126 s i) (v142 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_146 s i : Encodes (chunk 32 32 (word 64 (r5_nbReg s))) (v146 s i) /\ 0 <= v146 s i < 32.
Proof.
  destruct (correct_108 s i) as [hh rh].
  destruct (correct_144 s i) as [hl rl].
  assert (wire : v146 s i = combine 16 (chunk 16 48 (word 64 (r5_nbReg s))) (v108 s i) (v144 s i)).
  { unfold v146, v145, v68, v66, v67.
    change (word 16 0) with 0.
    exact (merge_wire 4 5 (chunk 16 48 (word 64 (r5_nbReg s))) (v108 s i) (v144 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 16 32 (word 64 (r5_nbReg s)) (v108 s i) (v144 s i) ltac:(lia) hh hl).
  - exact (combine_range 16 (chunk 16 48 (word 64 (r5_nbReg s))) (v108 s i) (v144 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_166 s i : Encodes (chunk 8 24 (word 64 (r5_nbReg s))) (v166 s i) /\ 0 <= v166 s i < 8.
Proof.
  destruct (correct_158 s i) as [hh rh].
  destruct (correct_164 s i) as [hl rl].
  assert (wire : v166 s i = combine 4 (chunk 4 28 (word 64 (r5_nbReg s))) (v158 s i) (v164 s i)).
  { unfold v166, v165, v152, v151, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 28 (word 64 (r5_nbReg s))) (v158 s i) (v164 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 24 (word 64 (r5_nbReg s)) (v158 s i) (v164 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 28 (word 64 (r5_nbReg s))) (v158 s i) (v164 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_182 s i : Encodes (chunk 8 16 (word 64 (r5_nbReg s))) (v182 s i) /\ 0 <= v182 s i < 8.
Proof.
  destruct (correct_174 s i) as [hh rh].
  destruct (correct_180 s i) as [hl rl].
  assert (wire : v182 s i = combine 4 (chunk 4 20 (word 64 (r5_nbReg s))) (v174 s i) (v180 s i)).
  { unfold v182, v181, v168, v167, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 20 (word 64 (r5_nbReg s))) (v174 s i) (v180 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 16 (word 64 (r5_nbReg s)) (v174 s i) (v180 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 20 (word 64 (r5_nbReg s))) (v174 s i) (v180 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_184 s i : Encodes (chunk 16 16 (word 64 (r5_nbReg s))) (v184 s i) /\ 0 <= v184 s i < 16.
Proof.
  destruct (correct_166 s i) as [hh rh].
  destruct (correct_182 s i) as [hl rl].
  assert (wire : v184 s i = combine 8 (chunk 8 24 (word 64 (r5_nbReg s))) (v166 s i) (v182 s i)).
  { unfold v184, v183, v150, v149, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 24 (word 64 (r5_nbReg s))) (v166 s i) (v182 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 16 (word 64 (r5_nbReg s)) (v166 s i) (v182 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 24 (word 64 (r5_nbReg s))) (v166 s i) (v182 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_202 s i : Encodes (chunk 8 8 (word 64 (r5_nbReg s))) (v202 s i) /\ 0 <= v202 s i < 8.
Proof.
  destruct (correct_194 s i) as [hh rh].
  destruct (correct_200 s i) as [hl rl].
  assert (wire : v202 s i = combine 4 (chunk 4 12 (word 64 (r5_nbReg s))) (v194 s i) (v200 s i)).
  { unfold v202, v201, v188, v187, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 12 (word 64 (r5_nbReg s))) (v194 s i) (v200 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 8 (word 64 (r5_nbReg s)) (v194 s i) (v200 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 12 (word 64 (r5_nbReg s))) (v194 s i) (v200 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_218 s i : Encodes (chunk 8 0 (word 64 (r5_nbReg s))) (v218 s i) /\ 0 <= v218 s i < 8.
Proof.
  destruct (correct_210 s i) as [hh rh].
  destruct (correct_216 s i) as [hl rl].
  assert (wire : v218 s i = combine 4 (chunk 4 4 (word 64 (r5_nbReg s))) (v210 s i) (v216 s i)).
  { unfold v218, v217, v204, v203, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 4 (word 64 (r5_nbReg s))) (v210 s i) (v216 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 0 (word 64 (r5_nbReg s)) (v210 s i) (v216 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 4 (word 64 (r5_nbReg s))) (v210 s i) (v216 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_220 s i : Encodes (chunk 16 0 (word 64 (r5_nbReg s))) (v220 s i) /\ 0 <= v220 s i < 16.
Proof.
  destruct (correct_202 s i) as [hh rh].
  destruct (correct_218 s i) as [hl rl].
  assert (wire : v220 s i = combine 8 (chunk 8 8 (word 64 (r5_nbReg s))) (v202 s i) (v218 s i)).
  { unfold v220, v219, v186, v185, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 8 (word 64 (r5_nbReg s))) (v202 s i) (v218 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 0 (word 64 (r5_nbReg s)) (v202 s i) (v218 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 8 (word 64 (r5_nbReg s))) (v202 s i) (v218 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_222 s i : Encodes (chunk 32 0 (word 64 (r5_nbReg s))) (v222 s i) /\ 0 <= v222 s i < 32.
Proof.
  destruct (correct_184 s i) as [hh rh].
  destruct (correct_220 s i) as [hl rl].
  assert (wire : v222 s i = combine 16 (chunk 16 16 (word 64 (r5_nbReg s))) (v184 s i) (v220 s i)).
  { unfold v222, v221, v148, v147, v67.
    change (word 16 0) with 0.
    exact (merge_wire 4 5 (chunk 16 16 (word 64 (r5_nbReg s))) (v184 s i) (v220 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 16 0 (word 64 (r5_nbReg s)) (v184 s i) (v220 s i) ltac:(lia) hh hl).
  - exact (combine_range 16 (chunk 16 16 (word 64 (r5_nbReg s))) (v184 s i) (v220 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_249 s i : Encodes (chunk 8 56 (word 65 (r6_naValx2Reg s))) (v249 s i) /\ 0 <= v249 s i < 8.
Proof.
  destruct (correct_241 s i) as [hh rh].
  destruct (correct_247 s i) as [hl rl].
  assert (wire : v249 s i = combine 4 (chunk 4 60 (word 65 (r6_naValx2Reg s))) (v241 s i) (v247 s i)).
  { unfold v249, v248, v235, v234, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 60 (word 65 (r6_naValx2Reg s))) (v241 s i) (v247 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 56 (word 65 (r6_naValx2Reg s)) (v241 s i) (v247 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 60 (word 65 (r6_naValx2Reg s))) (v241 s i) (v247 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_265 s i : Encodes (chunk 8 48 (word 65 (r6_naValx2Reg s))) (v265 s i) /\ 0 <= v265 s i < 8.
Proof.
  destruct (correct_257 s i) as [hh rh].
  destruct (correct_263 s i) as [hl rl].
  assert (wire : v265 s i = combine 4 (chunk 4 52 (word 65 (r6_naValx2Reg s))) (v257 s i) (v263 s i)).
  { unfold v265, v264, v251, v250, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 52 (word 65 (r6_naValx2Reg s))) (v257 s i) (v263 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 48 (word 65 (r6_naValx2Reg s)) (v257 s i) (v263 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 52 (word 65 (r6_naValx2Reg s))) (v257 s i) (v263 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_267 s i : Encodes (chunk 16 48 (word 65 (r6_naValx2Reg s))) (v267 s i) /\ 0 <= v267 s i < 16.
Proof.
  destruct (correct_249 s i) as [hh rh].
  destruct (correct_265 s i) as [hl rl].
  assert (wire : v267 s i = combine 8 (chunk 8 56 (word 65 (r6_naValx2Reg s))) (v249 s i) (v265 s i)).
  { unfold v267, v266, v233, v232, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 56 (word 65 (r6_naValx2Reg s))) (v249 s i) (v265 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 48 (word 65 (r6_naValx2Reg s)) (v249 s i) (v265 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 56 (word 65 (r6_naValx2Reg s))) (v249 s i) (v265 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_285 s i : Encodes (chunk 8 40 (word 65 (r6_naValx2Reg s))) (v285 s i) /\ 0 <= v285 s i < 8.
Proof.
  destruct (correct_277 s i) as [hh rh].
  destruct (correct_283 s i) as [hl rl].
  assert (wire : v285 s i = combine 4 (chunk 4 44 (word 65 (r6_naValx2Reg s))) (v277 s i) (v283 s i)).
  { unfold v285, v284, v271, v270, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 44 (word 65 (r6_naValx2Reg s))) (v277 s i) (v283 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 40 (word 65 (r6_naValx2Reg s)) (v277 s i) (v283 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 44 (word 65 (r6_naValx2Reg s))) (v277 s i) (v283 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_301 s i : Encodes (chunk 8 32 (word 65 (r6_naValx2Reg s))) (v301 s i) /\ 0 <= v301 s i < 8.
Proof.
  destruct (correct_293 s i) as [hh rh].
  destruct (correct_299 s i) as [hl rl].
  assert (wire : v301 s i = combine 4 (chunk 4 36 (word 65 (r6_naValx2Reg s))) (v293 s i) (v299 s i)).
  { unfold v301, v300, v287, v286, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 36 (word 65 (r6_naValx2Reg s))) (v293 s i) (v299 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 32 (word 65 (r6_naValx2Reg s)) (v293 s i) (v299 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 36 (word 65 (r6_naValx2Reg s))) (v293 s i) (v299 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_303 s i : Encodes (chunk 16 32 (word 65 (r6_naValx2Reg s))) (v303 s i) /\ 0 <= v303 s i < 16.
Proof.
  destruct (correct_285 s i) as [hh rh].
  destruct (correct_301 s i) as [hl rl].
  assert (wire : v303 s i = combine 8 (chunk 8 40 (word 65 (r6_naValx2Reg s))) (v285 s i) (v301 s i)).
  { unfold v303, v302, v269, v268, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 40 (word 65 (r6_naValx2Reg s))) (v285 s i) (v301 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 32 (word 65 (r6_naValx2Reg s)) (v285 s i) (v301 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 40 (word 65 (r6_naValx2Reg s))) (v285 s i) (v301 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_305 s i : Encodes (chunk 32 32 (word 65 (r6_naValx2Reg s))) (v305 s i) /\ 0 <= v305 s i < 32.
Proof.
  destruct (correct_267 s i) as [hh rh].
  destruct (correct_303 s i) as [hl rl].
  assert (wire : v305 s i = combine 16 (chunk 16 48 (word 65 (r6_naValx2Reg s))) (v267 s i) (v303 s i)).
  { unfold v305, v304, v231, v230, v67.
    change (word 16 0) with 0.
    exact (merge_wire 4 5 (chunk 16 48 (word 65 (r6_naValx2Reg s))) (v267 s i) (v303 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 16 32 (word 65 (r6_naValx2Reg s)) (v267 s i) (v303 s i) ltac:(lia) hh hl).
  - exact (combine_range 16 (chunk 16 48 (word 65 (r6_naValx2Reg s))) (v267 s i) (v303 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_325 s i : Encodes (chunk 8 24 (word 65 (r6_naValx2Reg s))) (v325 s i) /\ 0 <= v325 s i < 8.
Proof.
  destruct (correct_317 s i) as [hh rh].
  destruct (correct_323 s i) as [hl rl].
  assert (wire : v325 s i = combine 4 (chunk 4 28 (word 65 (r6_naValx2Reg s))) (v317 s i) (v323 s i)).
  { unfold v325, v324, v311, v310, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 28 (word 65 (r6_naValx2Reg s))) (v317 s i) (v323 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 24 (word 65 (r6_naValx2Reg s)) (v317 s i) (v323 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 28 (word 65 (r6_naValx2Reg s))) (v317 s i) (v323 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_341 s i : Encodes (chunk 8 16 (word 65 (r6_naValx2Reg s))) (v341 s i) /\ 0 <= v341 s i < 8.
Proof.
  destruct (correct_333 s i) as [hh rh].
  destruct (correct_339 s i) as [hl rl].
  assert (wire : v341 s i = combine 4 (chunk 4 20 (word 65 (r6_naValx2Reg s))) (v333 s i) (v339 s i)).
  { unfold v341, v340, v327, v326, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 20 (word 65 (r6_naValx2Reg s))) (v333 s i) (v339 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 16 (word 65 (r6_naValx2Reg s)) (v333 s i) (v339 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 20 (word 65 (r6_naValx2Reg s))) (v333 s i) (v339 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_343 s i : Encodes (chunk 16 16 (word 65 (r6_naValx2Reg s))) (v343 s i) /\ 0 <= v343 s i < 16.
Proof.
  destruct (correct_325 s i) as [hh rh].
  destruct (correct_341 s i) as [hl rl].
  assert (wire : v343 s i = combine 8 (chunk 8 24 (word 65 (r6_naValx2Reg s))) (v325 s i) (v341 s i)).
  { unfold v343, v342, v309, v308, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 24 (word 65 (r6_naValx2Reg s))) (v325 s i) (v341 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 16 (word 65 (r6_naValx2Reg s)) (v325 s i) (v341 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 24 (word 65 (r6_naValx2Reg s))) (v325 s i) (v341 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_361 s i : Encodes (chunk 8 8 (word 65 (r6_naValx2Reg s))) (v361 s i) /\ 0 <= v361 s i < 8.
Proof.
  destruct (correct_353 s i) as [hh rh].
  destruct (correct_359 s i) as [hl rl].
  assert (wire : v361 s i = combine 4 (chunk 4 12 (word 65 (r6_naValx2Reg s))) (v353 s i) (v359 s i)).
  { unfold v361, v360, v347, v346, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 12 (word 65 (r6_naValx2Reg s))) (v353 s i) (v359 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 8 (word 65 (r6_naValx2Reg s)) (v353 s i) (v359 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 12 (word 65 (r6_naValx2Reg s))) (v353 s i) (v359 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_377 s i : Encodes (chunk 8 0 (word 65 (r6_naValx2Reg s))) (v377 s i) /\ 0 <= v377 s i < 8.
Proof.
  destruct (correct_369 s i) as [hh rh].
  destruct (correct_375 s i) as [hl rl].
  assert (wire : v377 s i = combine 4 (chunk 4 4 (word 65 (r6_naValx2Reg s))) (v369 s i) (v375 s i)).
  { unfold v377, v376, v363, v362, v73.
    change (word 4 0) with 0.
    exact (merge_wire 2 3 (chunk 4 4 (word 65 (r6_naValx2Reg s))) (v369 s i) (v375 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 4 0 (word 65 (r6_naValx2Reg s)) (v369 s i) (v375 s i) ltac:(lia) hh hl).
  - exact (combine_range 4 (chunk 4 4 (word 65 (r6_naValx2Reg s))) (v369 s i) (v375 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_379 s i : Encodes (chunk 16 0 (word 65 (r6_naValx2Reg s))) (v379 s i) /\ 0 <= v379 s i < 16.
Proof.
  destruct (correct_361 s i) as [hh rh].
  destruct (correct_377 s i) as [hl rl].
  assert (wire : v379 s i = combine 8 (chunk 8 8 (word 65 (r6_naValx2Reg s))) (v361 s i) (v377 s i)).
  { unfold v379, v378, v345, v344, v70.
    change (word 8 0) with 0.
    exact (merge_wire 3 4 (chunk 8 8 (word 65 (r6_naValx2Reg s))) (v361 s i) (v377 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 8 0 (word 65 (r6_naValx2Reg s)) (v361 s i) (v377 s i) ltac:(lia) hh hl).
  - exact (combine_range 8 (chunk 8 8 (word 65 (r6_naValx2Reg s))) (v361 s i) (v377 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_381 s i : Encodes (chunk 32 0 (word 65 (r6_naValx2Reg s))) (v381 s i) /\ 0 <= v381 s i < 32.
Proof.
  destruct (correct_343 s i) as [hh rh].
  destruct (correct_379 s i) as [hl rl].
  assert (wire : v381 s i = combine 16 (chunk 16 16 (word 65 (r6_naValx2Reg s))) (v343 s i) (v379 s i)).
  { unfold v381, v380, v307, v306, v67.
    change (word 16 0) with 0.
    exact (merge_wire 4 5 (chunk 16 16 (word 65 (r6_naValx2Reg s))) (v343 s i) (v379 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 16 0 (word 65 (r6_naValx2Reg s)) (v343 s i) (v379 s i) ltac:(lia) hh hl).
  - exact (combine_range 16 (chunk 16 16 (word 65 (r6_naValx2Reg s))) (v343 s i) (v379 s i) ltac:(lia) rh rl).
Qed.

Lemma correct_383 s i : Encodes (chunk 64 0 (word 65 (r6_naValx2Reg s))) (v383 s i) /\ 0 <= v383 s i < 64.
Proof.
  destruct (correct_305 s i) as [hh rh].
  destruct (correct_381 s i) as [hl rl].
  assert (wire : v383 s i = combine 32 (chunk 32 32 (word 65 (r6_naValx2Reg s))) (v305 s i) (v381 s i)).
  { unfold v383, v382, v229, v228, v64.
    change (word 32 0) with 0.
    exact (merge_wire 5 6 (chunk 32 32 (word 65 (r6_naValx2Reg s))) (v305 s i) (v381 s i) ltac:(lia) ltac:(vm_compute; discriminate) rh rl). }
  rewrite wire; split.
  - exact (chunk_merge_correct 32 0 (word 65 (r6_naValx2Reg s)) (v305 s i) (v381 s i) ltac:(lia) hh hl).
  - exact (combine_range 32 (chunk 32 32 (word 65 (r6_naValx2Reg s))) (v305 s i) (v381 s i) ltac:(lia) rh rl).
Qed.
End RadixLeadingTree.
Print Assumptions RadixLeadingTree.correct_383.
