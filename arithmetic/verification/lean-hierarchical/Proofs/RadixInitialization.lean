import Proofs.RadixRequest
import Proofs.RadixArithmetic
import Proofs.RadixScale

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def loadBits (twiceDividend : BitVec 65) (skip : BitVec 6) : BitVec 129 :=
  0#1 ++ ((0#63 ++ twiceDividend) <<< skip.toNat)

/-- The generated leading-bit circuit chooses a safe first restoring candidate. -/
theorem skip_bound_bits (s : State) (i : Inputs)
    (nonzero : s.r5_nbReg ≠ 0#64) (normal : s.r1_ndivBy0Reg = 0#1) :
    BitVec.extractLsb' 64 65 (loadBits s.r6_naValx2Reg (v391 s i)) < (s.r5_nbReg ++ 0#1) := by
  simp only [loadBits, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249, v250, v251, v252, v253, v254, v255, v256, v257, v258, v259, v260, v261, v262, v263, v264, v265, v266, v267, v268, v269, v270, v271, v272, v273, v274, v275, v276, v277, v278, v279, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291, v292, v293, v294, v295, v296, v297, v298, v299, v300, v301, v302, v303, v304, v305, v306, v307, v308, v309, v310, v311, v312, v313, v314, v315, v316, v317, v318, v319, v320, v321, v322, v323, v324, v325, v326, v327, v328, v329, v330, v331, v332, v333, v334, v335, v336, v337, v338, v339, v340, v341, v342, v343, v344, v345, v346, v347, v348, v349, v350, v351, v352, v353, v354, v355, v356, v357, v358, v359, v360, v361, v362, v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, v379, v380, v381, v382, v383, v384, v385, v386, v387, v388, v389, v390, v391, normal]
  simp only [← BitVec.lt_def, ← BitVec.le_def]
  bv_decide (config := { timeout := 60 })

theorem initialized_fields (s : State) (i j : Inputs)
    (setup : s.r0_nstate = 1) (reset : i.nreset = 0) (nextReset : j.nreset = 0) :
    let loaded := step (step s i) j
    loaded.r0_nstate = 3 ∧ loaded.r5_nbReg = s.r5_nbReg ∧
    loaded.r6_naValx2Reg = s.r6_naValx2Reg ∧
    loaded.r9_ncnt_5Fvalue = v391 s i ∧
    loaded.r2_nshiftReg = loadBits s.r6_naValx2Reg (v391 s i) := by
  have extend (c : BitVec 6) : (0#122 ++ c).toNat = c.toNat := by
    rw [BitVec.toNat_append]
    simp
  simp [step, eval_eq_spec, evalSpec, loadBits, setup, reset, nextReset, extend, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v392, v393, v394, v395, v396, v397, v398]

theorem initialized_bound (s : State) (i j : Inputs)
    (setup : s.r0_nstate = 1) (reset : i.nreset = 0) (nextReset : j.nreset = 0)
    (nonzero : s.r5_nbReg ≠ 0#64) (normal : s.r1_ndivBy0Reg = 0#1) :
    let loaded := step (step s i) j
    candidate loaded.r2_nshiftReg < 2 * loaded.r5_nbReg.toNat := by
  have fields := initialized_fields s i j setup reset nextReset
  dsimp only
  rw [fields.2.1, fields.2.2.2.2]
  have bound := skip_bound_bits s i nonzero normal
  change candidate (loadBits s.r6_naValx2Reg (v391 s i)) < (s.r5_nbReg ++ 0#1).toNat at bound
  rw [append_value] at bound
  simpa [Nat.mul_comm] using bound

#print axioms skip_bound_bits
end HierarchicalRadix
