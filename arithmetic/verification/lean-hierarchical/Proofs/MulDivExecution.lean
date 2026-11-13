import Proofs.MulDivTransition

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109

def finishState (negative : BitVec 1) : BitVec 3 :=
  (1#1 ++ (negative ^^^ 1#1)) ++ 1#1

theorem division_control (s : State) (i : Inputs) (dividing : s.r0_nstate = 3)
    (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = (if s.r3_ncount = 64#7 then finishState s.r4_nneg_5Fout else 3#3) ∧
    (step s i).r3_ncount = s.r3_ncount + 1#7 ∧
    (step s i).r7_ndivisor = s.r7_ndivisor := by
  by_cases last : s.r3_ncount = 64#7
  all_goals simp [step, eval_eq_spec, evalSpec, dividing, reset, alive, finishState, last]

/-- Starting after the leading digit, the normalized hardware state follows
    the already-proved restoring recurrence at every edge. -/
theorem division_prefix (s : State) (inputs : Nat → Inputs) (bits : BitVec 129) (d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#1 ++ bits)
    (bound : HierarchicalRadix.candidate bits < 2 * d.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0)
    (n : Nat) (beforeLast : n < 64) :
    (run s inputs n).r0_nstate = 3 ∧
    (run s inputs n).r3_ncount.toNat = n + 1 ∧
    (run s inputs n).r7_ndivisor = 0#1 ++ d ∧
    (run s inputs n).r8_nremainder = 0#1 ++ HierarchicalRadix.advanceMany d n bits := by
  induction n with
  | zero => simp [run, HierarchicalRadix.advanceMany, dividing, count, divisor, initial]
  | succ n ih =>
    obtain ⟨state, counter, storedDivisor, remainder⟩ := ih (by omega)
    have control := division_control (run s inputs n) (inputs n) state
      (reset n (by omega)) (alive n (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 64#7 := by
      intro h
      have hNat := congrArg BitVec.toNat h
      change (run s inputs n).r3_ncount.toNat = 64 at hNat
      omega
    simp only [run]
    refine ⟨?_, ?_, control.2.2.trans storedDivisor, ?_⟩
    · simpa [notLast] using control.1
    · rw [control.2.1, BitVec.toNat_add, counter]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · rw [division_edge _ _ state, remainder, storedDivisor,
        division_digit _ _ (HierarchicalRadix.iterated_bound bits d bound n)]
      rfl

theorem division_finish (s : State) (inputs : Nat → Inputs) (bits : BitVec 129) (d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#1 ++ bits)
    (bound : HierarchicalRadix.candidate bits < 2 * d.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 64).r0_nstate = finishState (run s inputs 63).r4_nneg_5Fout ∧
    (run s inputs 64).r8_nremainder = 0#1 ++ HierarchicalRadix.advanceMany d 64 bits := by
  obtain ⟨state, counter, storedDivisor, remainder⟩ :=
    division_prefix s inputs bits d dividing count divisor initial bound reset alive 63 (by omega)
  have last : (run s inputs 63).r3_ncount = 64#7 := by
    apply BitVec.eq_of_toNat_eq
    exact counter
  have control := division_control (run s inputs 63) (inputs 63) state
    (reset 63 (by omega)) (alive 63 (by omega))
  constructor
  · change (step (run s inputs 63) (inputs 63)).r0_nstate = _
    simpa [last] using control.1
  · change (step (run s inputs 63) (inputs 63)).r8_nremainder = _
    rw [division_edge _ _ state, remainder, storedDivisor,
      division_digit _ _ (HierarchicalRadix.iterated_bound bits d bound 63)]
    rfl

/-- The final hardware slices satisfy Euclidean division once normalization has
    loaded twice the dividend and the count is one. -/
theorem division_arithmetic (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initial : s.r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1))
    (nonzero : 0 < d.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (BitVec.extractLsb' 0 64 (run s inputs 64).r8_nremainder).toNat = a.toNat / d.toNat ∧
    (BitVec.extractLsb' 65 64 (run s inputs 64).r8_nremainder).toNat = a.toNat % d.toNat := by
  let bits : BitVec 129 := (0#64 ++ a) ++ 0#1
  have value : bits.toNat = 2 * a.toNat := by
    dsimp [bits]
    rw [HierarchicalRadix.append_value, HierarchicalRadix.append_value]
    simp [Nat.mul_comm]
  have bound : HierarchicalRadix.candidate bits < 2 * d.toNat := by
    rw [HierarchicalRadix.candidate_value, value]
    have width := a.isLt
    omega
  have result := (division_finish s inputs bits d dividing count divisor initial bound reset alive).2
  have scale : 2 ^ 64 * bits.toNat = a.toNat * 36893488147419103232 := by rw [value]; omega
  have arithmetic := HierarchicalRadix.completed_arithmetic bits d a.toNat 64 bound (by omega) scale
  rw [result]
  simpa only [BitVec.extractLsb'_append_eq_of_add_le (by omega : 0 + 64 ≤ 129),
    BitVec.extractLsb'_append_eq_of_add_le (by omega : 65 + 64 ≤ 129)] using arithmetic

#print axioms division_arithmetic
#print axioms division_prefix
end HierarchicalMulDiv
