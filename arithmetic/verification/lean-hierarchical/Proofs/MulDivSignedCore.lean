import Proofs.MulDivSignedPreparation

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

/-- The correction bit is stable throughout a trace whose division counter
    has already passed the leading digit. -/
theorem division_sign_run (s : State) (inputs : Nat → Inputs) (n : Nat)
    (active : ∀ t, t < n → (run s inputs t).r0_nstate = 3 ∧
      (run s inputs t).r3_ncount ≠ 0#7) :
    (run s inputs n).r4_nneg_5Fout = s.r4_nneg_5Fout := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, division_sign_stable _ _ (active n (by omega)).1 (active n (by omega)).2]
    exact ih (by intro t h; exact active t (by omega))

/-- Signed and unsigned requests share the magnitude computation. This
    contract retains the correction bit and response metadata at completion. -/
theorem magnitude_core_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initial : s.r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1))
    (positive : 0 < d.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    let result := run s inputs 64
    result.r0_nstate = finishState s.r4_nneg_5Fout ∧
    BitVec.extractLsb' 0 64 result.r8_nremainder = BitVec.ofNat 64 (a.toNat / d.toNat) ∧
    BitVec.extractLsb' 65 64 result.r8_nremainder = BitVec.ofNat 64 (a.toNat % d.toNat) ∧
    result.r6_nresHi = s.r5_nisHi ∧ metadata result = metadata s := by
  let bits : BitVec 129 := (0#64 ++ a) ++ 0#1
  have bound : HierarchicalRadix.candidate bits < 2 * d.toNat := by
    rw [HierarchicalRadix.candidate_value]
    have value : bits.toNat = 2 * a.toNat := by
      dsimp [bits]
      rw [HierarchicalRadix.append_value, HierarchicalRadix.append_value]
      simp [Nat.mul_comm]
    rw [value]
    have width := a.isLt
    omega
  have traceFacts := division_prefix s inputs bits d dividing count divisor initial bound reset alive
  have active (t : Nat) (h : t < 64) : (run s inputs t).r0_nstate = 3 ∧
      (run s inputs t).r3_ncount ≠ 0#7 := by
    refine ⟨(traceFacts t h).1, ?_⟩
    intro zero
    have counter := (traceFacts t h).2.1
    rw [zero] at counter
    change 0 = t + 1 at counter
    omega
  have finish := division_finish s inputs bits d dividing count divisor initial bound reset alive
  have sign := division_sign_run s inputs 63 (by intro t h; exact active t (by omega))
  have lastCount : (run s inputs 63).r3_ncount = 64#7 := by
    apply BitVec.eq_of_toNat_eq
    exact (traceFacts 63 (by omega)).2.1
  have earlier := metadata_run s inputs 63 (by intro t h; rw [(active t (by omega)).1]; decide)
  have later := metadata_run s inputs 64 (by intro t h; rw [(active t h).1]; decide)
  have mode : (run s inputs 64).r6_nresHi = s.r5_nisHi :=
    (select_response _ _ (active 63 (by omega)).1 lastCount).trans (congrArg (fun f => f.2.2) earlier)
  have arithmetic := division_arithmetic s inputs a d dividing count divisor initial positive reset alive
  have q := congrArg (BitVec.ofNat 64) arithmetic.1
  have r := congrArg (BitVec.ofNat 64) arithmetic.2
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at q r
  exact ⟨finish.1.trans (congrArg finishState sign), q, r, mode, later⟩

def formatCorrected (q r : BitVec 64) (dw hi negative : BitVec 1) : BitVec 64 :=
  let selected := if hi = 1 then r else q
  let corrected := if negative = 1 then -selected else selected
  if dw = 1 then corrected else (BitVec.extractLsb' 0 32 corrected).signExtend 64

/-- The final correction adds exactly one edge when requested, preserving the
    tag and applying word formatting after the sign correction. -/
theorem corrected_response (s : State) (i observeInput : Inputs) (negative : BitVec 1)
    (finished : s.r0_nstate = finishState negative)
    (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    let ready := if negative = 1 then step s i else s
    (observe ready observeInput).nio_5Fresp_5Fvalid = 1 ∧
    (observe ready observeInput).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe ready observeInput).nio_5Fresp_5Fbits_5Fdata =
      formatCorrected (BitVec.extractLsb' 0 64 s.r8_nremainder)
        (BitVec.extractLsb' 65 64 s.r8_nremainder) s.r1_nreq_5Fdw s.r6_nresHi negative := by
  dsimp only
  by_cases neg : negative = 1
  · simp only [neg, if_pos]
    have correcting : s.r0_nstate = 5 := by simpa [finishState, neg] using finished
    have corrected := correction_edge s i correcting reset alive
    have output := observe_division (step s i) observeInput corrected.1
    refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) corrected.2.2.2), ?_⟩
    rw [output.2.2, corrected.2.1, corrected.2.2.1,
      show (step s i).r1_nreq_5Fdw = s.r1_nreq_5Fdw from congrArg (fun m => m.1) corrected.2.2.2]
    simp [formatUnsigned, formatCorrected]
    bv_decide
  · simp only [neg, if_neg]
    have zero : negative = 0#1 := by bv_decide
    have responding : s.r0_nstate = 7 := by simpa [finishState, zero] using finished
    have output := observe_division s observeInput responding
    refine ⟨output.1, output.2.1, ?_⟩
    simpa only [formatUnsigned, formatCorrected, neg, if_neg] using output.2.2

/-- From the shared normalized interface, the actual circuit emits the
    corrected arithmetic result after 64 or 65 edges. -/
theorem corrected_core_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initial : s.r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1))
    (positive : 0 < d.toNat)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 64 ∨ n = 65) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        formatCorrected (BitVec.ofNat 64 (a.toNat / d.toNat))
          (BitVec.ofNat 64 (a.toNat % d.toNat)) s.r1_nreq_5Fdw s.r5_nisHi s.r4_nneg_5Fout := by
  have core := magnitude_core_result s inputs a d dividing count divisor initial positive
    (by intro t h; exact reset t (by omega)) (by intro t h; exact alive t (by omega))
  let n : Nat := if s.r4_nneg_5Fout = 1 then 65 else 64
  have output := corrected_response (run s inputs 64) (inputs 64) (inputs n) s.r4_nneg_5Fout
    core.1 (reset 64 (by omega)) (alive 64 (by omega))
  have ready : (if s.r4_nneg_5Fout = 1 then step (run s inputs 64) (inputs 64)
      else run s inputs 64) = run s inputs n := by
    dsimp [n]
    split <;> rfl
  dsimp only at output
  rw [ready] at output
  refine ⟨n, ?_, output.1, ?_, ?_⟩
  · dsimp [n]
    split <;> simp
  · exact output.2.1.trans (congrArg (fun m => m.2.1) core.2.2.2.2)
  · rw [output.2.2, core.2.1, core.2.2.1, core.2.2.2.1,
      show (run s inputs 64).r1_nreq_5Fdw = s.r1_nreq_5Fdw from
        congrArg (fun m => m.1) core.2.2.2.2]

#print axioms corrected_core_result
#print axioms corrected_response
#print axioms magnitude_core_result
end HierarchicalMulDiv
