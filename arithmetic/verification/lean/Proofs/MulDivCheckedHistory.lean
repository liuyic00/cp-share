import Proofs.MulDivCheckedProjection
import Std.Tactic

namespace MulDivCheckedHistory
open nMulDivChecked

def captured (s : State) : nMulDiv.Inputs := {
  nreset := 0, nio_5Freq_5Fvalid := 1, nio_5Freq_5Fbits_5Ffn := s.r11_ncontractFn,
  nio_5Freq_5Fbits_5Fdw := s.r12_ncontractDw, nio_5Freq_5Fbits_5Fin1 := s.r13_ncontractA,
  nio_5Freq_5Fbits_5Fin2 := s.r14_ncontractB, nio_5Freq_5Fbits_5Ftag := s.r15_ncontractTag,
  nio_5Fkill := 0, nio_5Fresp_5Fready := 0 }

def requestView (i : Inputs) : nMulDiv.Inputs := {
  nreset := 0, nio_5Freq_5Fvalid := 1, nio_5Freq_5Fbits_5Ffn := i.nio_5Freq_5Fbits_5Ffn,
  nio_5Freq_5Fbits_5Fdw := i.nio_5Freq_5Fbits_5Fdw, nio_5Freq_5Fbits_5Fin1 := i.nio_5Freq_5Fbits_5Fin1,
  nio_5Freq_5Fbits_5Fin2 := i.nio_5Freq_5Fbits_5Fin2, nio_5Freq_5Fbits_5Ftag := i.nio_5Freq_5Fbits_5Ftag,
  nio_5Fkill := 0, nio_5Fresp_5Fready := 0 }

def legal (i : Inputs) : Prop := i.nio_5Freq_5Fbits_5Ffn.toNat < 8 ∧
  (i.nio_5Freq_5Fbits_5Fdw = 1 ∨ i.nio_5Freq_5Fbits_5Ffn = 0 ∨ 4 ≤ i.nio_5Freq_5Fbits_5Ffn.toNat)

theorem capture (s : State) (i : Inputs) (ready : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1) : captured (step s i) = requestView i := by
  simp [captured, requestView, step, eval, ready, valid]

theorem hold (s : State) (i : Inputs)
    (noRequest : s.r0_nstate ≠ 0 ∨ i.nio_5Freq_5Fvalid = 0) :
    captured (step s i) = captured s := by
  rcases noRequest with busy | invalid
  · change s.r0_nstate ≠ 0#3 at busy
    simp [captured, step, eval, busy]
  · simp [captured, step, eval, invalid]

theorem reset_monitors (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r9_ncontractPending = 0 ∧ (step s i).r10_ncontractAge = 0 ∧
    (step s i).r16_ncontractWasNegated = 0 ∧ (step s i).r21_ncontractWasStalled = 0 := by
  simp [step, eval, reset]

theorem capture_age (s : State) (i : Inputs) (ready : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1) : (step s i).r10_ncontractAge = 0 := by
  simp [step, eval, ready, valid]

theorem capture_pending (s : State) (i : Inputs) (ready : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1) (reset : i.nreset = 0) (notKilled : i.nio_5Fkill = 0)
    (operation : legal i) : (step s i).r9_ncontractPending = 1 := by
  have range := operation.1
  have cases : i.nio_5Freq_5Fbits_5Ffn = 0#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 1#4 ∨
      i.nio_5Freq_5Fbits_5Ffn = 2#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 3#4 ∨
      i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 5#4 ∨
      i.nio_5Freq_5Fbits_5Ffn = 6#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 7#4 := by
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rcases cases with fn | fn | fn | fn | fn | fn | fn | fn <;>
    simp [legal, fn] at operation <;>
    simp only [step, eval, ready, valid, reset, notKilled, fn] <;> bv_decide

def witness (s : State) : BitVec 1 × BitVec 64 × BitVec 64 :=
  (s.r16_ncontractWasNegated, s.r17_ncontractQuotient, s.r18_ncontractResidue)

/-- Both magnitudes are recorded before output negation overwrites the core register. -/
theorem capture_witness (s : State) (i : Inputs) (negating : s.r0_nstate = 5)
    (reset : i.nreset = 0) : witness (step s i) =
      (1, s.r8_nremainder.extractLsb' 0 64, s.r8_nremainder.extractLsb' 65 64) := by
  simp [witness, step, eval, negating, reset]
  bv_decide

theorem hold_witness (s : State) (i : Inputs) (notNegating : s.r0_nstate ≠ 5)
    (noRequest : s.r0_nstate ≠ 0 ∨ i.nio_5Freq_5Fvalid = 0) (reset : i.nreset = 0) :
    witness (step s i) = witness s := by
  change s.r0_nstate ≠ 5#3 at notNegating
  rcases noRequest with busy | invalid
  · change s.r0_nstate ≠ 0#3 at busy
    simp [witness, step, eval, notNegating, busy, reset]
    bv_decide
  · simp [witness, step, eval, notNegating, invalid, reset]
    bv_decide

end MulDivCheckedHistory
