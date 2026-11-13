import Proofs.MulDivSignedCore

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

/-- For a zero divisor the leading digit suppresses quotient correction, while
    a remainder request keeps the captured dividend sign. -/
def zeroCorrection (s : State) : BitVec 1 :=
  if s.r5_nisHi = 0#1 then 0#1 else s.r4_nneg_5Fout

 theorem zero_magnitude_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#65) (initial : s.r8_nremainder = 0#66 ++ a)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    let result := run s inputs 65
    result.r0_nstate = finishState (zeroCorrection s) ∧
    BitVec.extractLsb' 0 64 result.r8_nremainder = BitVec.allOnes 64 ∧
    BitVec.extractLsb' 65 64 result.r8_nremainder = a ∧
    result.r6_nresHi = s.r5_nisHi ∧ metadata result = metadata s := by
  have traceFacts := zero_prefix s inputs a dividing count divisor initial reset alive
  have active (t : Nat) (h : t < 65) : (run s inputs t).r0_nstate = 3 :=
    (traceFacts t (by omega)).1
  have sign (t : Nat) (positive : 0 < t) (bound : t ≤ 64) :
      (run s inputs t).r4_nneg_5Fout = zeroCorrection s := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases first : t = 0
      · subst t
        change (step s (inputs 0)).r4_nneg_5Fout = _
        have leading := leading_sign s (inputs 0) a 0 dividing count
          (by simpa using divisor) initial
        simpa [zeroCorrection] using leading
      · have counter := (traceFacts t (by omega)).2.1
        have nonzero : (run s inputs t).r3_ncount ≠ 0#7 := by
          intro zero
          rw [zero] at counter
          change 0 = t at counter
          omega
        rw [run, division_sign_stable _ _ (active t (by omega)) nonzero]
        exact ih (by omega) (by omega)
  have last := traceFacts 64 (by omega)
  have counter : (run s inputs 64).r3_ncount = 64#7 := BitVec.eq_of_toNat_eq last.2.1
  have control := division_control (run s inputs 64) (inputs 64) last.1
    (reset 64 (by omega)) (alive 64 (by omega))
  have finished : (run s inputs 65).r0_nstate = finishState (zeroCorrection s) := by
    change (step (run s inputs 64) (inputs 64)).r0_nstate = _
    rw [control.1, counter, if_pos rfl, sign 64 (by omega) (by omega)]
  have bits : (run s inputs 65).r8_nremainder = zeroBits a 65 := by
    change (step (run s inputs 64) (inputs 64)).r8_nremainder = _
    rw [division_edge _ _ last.1, last.2.2.1, last.2.2.2, zeroBits_step _ _ (by omega)]
  have earlier := metadata_run s inputs 64 (by intro t h; rw [active t (by omega)]; decide)
  have later := metadata_run s inputs 65 (by intro t h; rw [active t h]; decide)
  have mode : (run s inputs 65).r6_nresHi = s.r5_nisHi :=
    (select_response _ _ last.1 counter).trans (congrArg (fun f => f.2.2) earlier)
  refine ⟨finished, ?_, ?_, mode, later⟩
  · rw [bits]; exact (zeroBits_result a).1
  · rw [bits]; exact (zeroBits_result a).2

/-- The zero-divisor path uses the same final correction contract, and emits
    a response after 65 or 66 edges. -/
theorem corrected_zero_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#65)
    (initial : s.r8_nremainder = 0#66 ++ a)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 65 ∨ n = 66) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        formatCorrected (BitVec.allOnes 64)
          a s.r1_nreq_5Fdw s.r5_nisHi (zeroCorrection s) := by
  have core := zero_magnitude_result s inputs a dividing count divisor initial
    (by intro t h; exact reset t (by omega)) (by intro t h; exact alive t (by omega))
  let n : Nat := if zeroCorrection s = 1 then 66 else 65
  have output := corrected_response (run s inputs 65) (inputs 65) (inputs n) (zeroCorrection s)
    core.1 (reset 65 (by omega)) (alive 65 (by omega))
  have ready : (if zeroCorrection s = 1 then step (run s inputs 65) (inputs 65)
      else run s inputs 65) = run s inputs n := by
    dsimp [n]
    split <;> rfl
  dsimp only at output
  rw [ready] at output
  refine ⟨n, ?_, output.1, ?_, ?_⟩
  · dsimp [n]
    split <;> simp
  · exact output.2.1.trans (congrArg (fun m => m.2.1) core.2.2.2.2)
  · rw [output.2.2, core.2.1, core.2.2.1, core.2.2.2.1,
      show (run s inputs 65).r1_nreq_5Fdw = s.r1_nreq_5Fdw from
        congrArg (fun m => m.1) core.2.2.2.2]

#print axioms corrected_zero_result
#print axioms zero_magnitude_result
end HierarchicalMulDiv
