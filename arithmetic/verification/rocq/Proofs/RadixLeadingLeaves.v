From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits LeadingBits RadixControl RadixDatapath.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixDatapath.RadixDatapath.
Open Scope Z_scope.
Module RadixLeadingLeaves.
Lemma extract_window x o j (hj : 0 <= j) (fit : j+1 <= 4) :
  word 1 (Z.shiftr (word 4 (Z.shiftr x o)) j) = word 1 (Z.shiftr x (o+j)).
Proof. exact (WordBits.WordBits.extract_extract 4 1 o j x ltac:(lia) hj fit). Qed.
Lemma leaf_window x o :
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr x o)) =
  (if word 1 (Z.shiftr x (o+3)) =? 1 then 3 else
   if word 1 (Z.shiftr x (o+2)) =? 1 then 2 else word 1 (Z.shiftr x (o+1))).
Proof.
  unfold LeadingBits.LeadingBits.leaf4.
  change ((if word 1 (Z.shiftr (word 4 (word 4 (Z.shiftr x o))) 3) =? 1 then 3 else
    if word 1 (Z.shiftr (word 4 (word 4 (Z.shiftr x o))) 2) =? 1 then 2 else
    word 1 (Z.shiftr (word 4 (word 4 (Z.shiftr x o))) 1)) = (if word 1 (Z.shiftr x (o+3)) =? 1 then 3 else if word 1 (Z.shiftr x (o+2)) =? 1 then 2 else word 1 (Z.shiftr x (o+1)))).
  rewrite normalize by lia; rewrite !extract_window by lia; reflexivity.
Qed.
Lemma leaf_circuit x o :
  word 2 (if word 1 (Z.shiftr x (o+3)) =? 1 then 3 else
    word 2 (if word 1 (Z.shiftr x (o+2)) =? 1 then 2 else
      word 2 (word 1 (Z.shiftr x (o+1))))) =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr x o)).
Proof.
  rewrite leaf_window; destruct (word 1 (Z.shiftr x (o+3)) =? 1); [reflexivity |].
  destruct (word 1 (Z.shiftr x (o+2)) =? 1); [reflexivity |].
  repeat rewrite normalize by lia; apply widen; lia.
Qed.
(* Generated node connections; regenerate with scripts/prove-rocq-radix-leading.py. *)
Lemma node_82 s i : v82 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 60)).
Proof.
  unfold v82, v81, v80, v75, v77, v79, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 60).
Qed.

Lemma node_88 s i : v88 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 56)).
Proof.
  unfold v88, v87, v86, v83, v84, v85, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 56).
Qed.

Lemma node_98 s i : v98 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 52)).
Proof.
  unfold v98, v97, v96, v93, v94, v95, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 52).
Qed.

Lemma node_104 s i : v104 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 48)).
Proof.
  unfold v104, v103, v102, v99, v100, v101, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 48).
Qed.

Lemma node_118 s i : v118 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 44)).
Proof.
  unfold v118, v117, v116, v113, v114, v115, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 44).
Qed.

Lemma node_124 s i : v124 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 40)).
Proof.
  unfold v124, v123, v122, v119, v120, v121, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 40).
Qed.

Lemma node_134 s i : v134 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 36)).
Proof.
  unfold v134, v133, v132, v129, v130, v131, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 36).
Qed.

Lemma node_140 s i : v140 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 32)).
Proof.
  unfold v140, v139, v138, v135, v136, v137, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 32).
Qed.

Lemma node_158 s i : v158 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 28)).
Proof.
  unfold v158, v157, v156, v153, v154, v155, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 28).
Qed.

Lemma node_164 s i : v164 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 24)).
Proof.
  unfold v164, v163, v162, v159, v160, v161, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 24).
Qed.

Lemma node_174 s i : v174 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 20)).
Proof.
  unfold v174, v173, v172, v169, v170, v171, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 20).
Qed.

Lemma node_180 s i : v180 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 16)).
Proof.
  unfold v180, v179, v178, v175, v176, v177, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 16).
Qed.

Lemma node_194 s i : v194 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 12)).
Proof.
  unfold v194, v193, v192, v189, v190, v191, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 12).
Qed.

Lemma node_200 s i : v200 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 8)).
Proof.
  unfold v200, v199, v198, v195, v196, v197, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 8).
Qed.

Lemma node_210 s i : v210 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 4)).
Proof.
  unfold v210, v209, v208, v205, v206, v207, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 4).
Qed.

Lemma node_216 s i : v216 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 64 (r5_nbReg s)) 0)).
Proof.
  unfold v216, v215, v214, v211, v212, v213, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 64 (r5_nbReg s)) 0).
Qed.

Lemma node_241 s i : v241 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 60)).
Proof.
  unfold v241, v240, v239, v236, v237, v238, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 60).
Qed.

Lemma node_247 s i : v247 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 56)).
Proof.
  unfold v247, v246, v245, v242, v243, v244, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 56).
Qed.

Lemma node_257 s i : v257 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 52)).
Proof.
  unfold v257, v256, v255, v252, v253, v254, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 52).
Qed.

Lemma node_263 s i : v263 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 48)).
Proof.
  unfold v263, v262, v261, v258, v259, v260, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 48).
Qed.

Lemma node_277 s i : v277 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 44)).
Proof.
  unfold v277, v276, v275, v272, v273, v274, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 44).
Qed.

Lemma node_283 s i : v283 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 40)).
Proof.
  unfold v283, v282, v281, v278, v279, v280, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 40).
Qed.

Lemma node_293 s i : v293 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 36)).
Proof.
  unfold v293, v292, v291, v288, v289, v290, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 36).
Qed.

Lemma node_299 s i : v299 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 32)).
Proof.
  unfold v299, v298, v297, v294, v295, v296, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 32).
Qed.

Lemma node_317 s i : v317 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 28)).
Proof.
  unfold v317, v316, v315, v312, v313, v314, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 28).
Qed.

Lemma node_323 s i : v323 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 24)).
Proof.
  unfold v323, v322, v321, v318, v319, v320, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 24).
Qed.

Lemma node_333 s i : v333 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 20)).
Proof.
  unfold v333, v332, v331, v328, v329, v330, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 20).
Qed.

Lemma node_339 s i : v339 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 16)).
Proof.
  unfold v339, v338, v337, v334, v335, v336, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 16).
Qed.

Lemma node_353 s i : v353 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 12)).
Proof.
  unfold v353, v352, v351, v348, v349, v350, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 12).
Qed.

Lemma node_359 s i : v359 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 8)).
Proof.
  unfold v359, v358, v357, v354, v355, v356, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 8).
Qed.

Lemma node_369 s i : v369 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 4)).
Proof.
  unfold v369, v368, v367, v364, v365, v366, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 4).
Qed.

Lemma node_375 s i : v375 s i =
  LeadingBits.LeadingBits.leaf4 (word 4 (Z.shiftr (word 65 (r6_naValx2Reg s)) 0)).
Proof.
  unfold v375, v374, v373, v370, v371, v372, v76, v78, v26.
  change (word 1 0) with 0; rewrite Z.shiftl_0_l, Z.add_0_l.
  exact (leaf_circuit (word 65 (r6_naValx2Reg s)) 0).
Qed.

End RadixLeadingLeaves.
Print Assumptions RadixLeadingLeaves.node_82.
