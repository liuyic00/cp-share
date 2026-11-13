import Generated.MulDiv
import Proofs.RadixArithmetic

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def divisionAdvance (bits : BitVec 130) (divisor : BitVec 65) : BitVec 130 :=
  let delta := BitVec.extractLsb' 64 65 bits - divisor
  let negative := BitVec.extractLsb' 64 1 delta
  let remainder := if negative = 1 then BitVec.extractLsb' 64 64 bits
                   else BitVec.extractLsb' 0 64 delta
  ((0#1 ++ remainder) ++ BitVec.extractLsb' 0 64 bits) ++ (negative ^^^ 1#1)

/-- The division-state data transition is independent of the live request pins. -/
theorem division_edge (s : State) (i : Inputs) (dividing : s.r0_nstate = 3) :
    (step s i).r8_nremainder = divisionAdvance s.r8_nremainder s.r7_ndivisor := by
  simp [step, eval_eq_spec, evalSpec, divisionAdvance, dividing, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151]

/-- With a normalized divisor and the restoring bound, the sign-of-subtraction
    circuit implements the same digit operation as unsigned comparison. This
    reuses the new generic division arithmetic without relating old/new models. -/
theorem division_digit (bits : BitVec 129) (divisor : BitVec 64)
    (bound : HierarchicalRadix.candidate bits < 2 * divisor.toNat) :
    divisionAdvance (0#1 ++ bits) (0#1 ++ divisor) =
      0#1 ++ HierarchicalRadix.advance bits divisor := by
  have bounded : BitVec.extractLsb' 64 65 bits < divisor ++ 0#1 := by
    change HierarchicalRadix.candidate bits < (divisor ++ 0#1).toNat
    rw [HierarchicalRadix.append_value]
    simpa [Nat.mul_comm] using bound
  have extend : (0#1 ++ divisor).toNat = divisor.toNat := by
    rw [HierarchicalRadix.append_value]
    simp
  unfold divisionAdvance HierarchicalRadix.advance
  rw [← extend]
  simp only [← BitVec.le_def]
  bv_decide

#print axioms division_edge
#print axioms division_digit
end HierarchicalMulDiv
