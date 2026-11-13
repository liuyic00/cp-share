import Proofs.MulDivSignedZero

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

/-- The leading zero digit establishes the shared iteration interface and
    preserves the correction bit for a nonzero divisor. -/
theorem normalized_leading (s : State) (i : Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (nonzero : d ≠ 0#64) (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 1#7 ∧
    (step s i).r7_ndivisor = 0#1 ++ d ∧
    (step s i).r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1) ∧
    (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout ∧ metadata (step s i) = metadata s := by
  have control := division_control s i dividing reset alive
  refine ⟨?_, ?_, control.2.2.trans divisor, ?_, ?_, ?_⟩
  · simpa [count] using control.1
  · rw [control.2.1, count]; rfl
  · rw [division_edge s i dividing, divisor, initial, leading_digit a d nonzero]
  · simpa [nonzero] using leading_sign s i a d dividing count divisor initial
  · exact metadata_stable s i (by rw [dividing]; decide)

/-- Starting at count zero, a normalized nonzero divisor produces the signed
    or unsigned corrected result after 65 or 66 actual hardware edges. -/
theorem normalized_nonzero_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (nonzero : d ≠ 0#64)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 65 ∨ n = 66) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        formatCorrected (BitVec.ofNat 64 (a.toNat / d.toNat))
          (BitVec.ofNat 64 (a.toNat % d.toNat)) s.r1_nreq_5Fdw s.r5_nisHi s.r4_nneg_5Fout := by
  have leading := normalized_leading s (inputs 0) a d dividing count divisor initial nonzero
    (reset 0 (by omega)) (alive 0 (by omega))
  have positive : 0 < d.toNat := by
    have notZero : d.toNat ≠ 0 := by
      intro zero
      apply nonzero
      exact BitVec.eq_of_toNat_eq zero
    omega
  obtain ⟨n, time, valid, tag, data⟩ := corrected_core_result (step s (inputs 0))
    (fun t => inputs (1 + t)) a d leading.1 leading.2.1 leading.2.2.1 leading.2.2.2.1 positive
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  have trajectory : run s inputs (1 + n) = run (step s (inputs 0)) (fun t => inputs (1 + t)) n :=
    run_offset s inputs 1 n
  refine ⟨1 + n, by omega, ?_, ?_, ?_⟩
  · rw [trajectory]; exact valid
  · rw [trajectory]
    exact tag.trans (congrArg (fun m => m.2.1) leading.2.2.2.2.2)
  · rw [trajectory, data, leading.2.2.2.2.1,
      show (step s (inputs 0)).r1_nreq_5Fdw = s.r1_nreq_5Fdw from
        congrArg (fun m => m.1) leading.2.2.2.2.2,
      show (step s (inputs 0)).r5_nisHi = s.r5_nisHi from
        congrArg (fun m => m.2.2) leading.2.2.2.2.2]

def normalizedSpecification (a d : BitVec 64) (dw hi negative : BitVec 1) : BitVec 64 :=
  if d = 0#64 then formatCorrected (BitVec.allOnes 64) a dw hi
    (if hi = 0#1 then 0#1 else negative)
  else formatCorrected (BitVec.ofNat 64 (a.toNat / d.toNat))
    (BitVec.ofNat 64 (a.toNat % d.toNat)) dw hi negative

/-- One magnitude interface covers both zero and nonzero divisors. -/
theorem normalized_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 65 ∨ n = 66) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        normalizedSpecification a d s.r1_nreq_5Fdw s.r5_nisHi s.r4_nneg_5Fout := by
  by_cases zero : d = 0#64
  · have result := corrected_zero_result s inputs a dividing count
      (by simpa [zero] using divisor) initial reset alive
    simpa [normalizedSpecification, zero, zeroCorrection] using result
  · have result := normalized_nonzero_result s inputs a d dividing count divisor initial zero reset alive
    simpa only [normalizedSpecification, zero, if_neg] using result

#print axioms normalized_result
#print axioms normalized_nonzero_result
end HierarchicalMulDiv
