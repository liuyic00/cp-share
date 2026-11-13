import Proofs.MulDivCheckedMetadata
import Proofs.MulDivCheckedMulTiming
import Proofs.MulDivCheckedUnsignedTiming
import Proofs.MulDivCheckedSignedTiming

namespace MulDivCheckedTiming
open nMulDivChecked

theorem inactive (s : State) (i : Inputs) (pending : s.r9_ncontractPending ≠ 1) :
    ((eval s i).assertions.take 2).all id = true := by
  rw [MulDivCheckedLatency.timing_checks]
  have disabled : MulDivCheckedLatency.gate s i = 0 := by
    simp only [MulDivCheckedLatency.gate]
    bv_decide
  simp [disabled]

/-- Both generated timing checks hold at every observation after reset, for
all thirteen legal modes and arbitrary subsequent reset, kill, and handshake pins. -/
theorem timing_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat) :
    ((eval (run (step initial resetInput) pins n) (pins n)).assertions.take 2).all id = true := by
  let s := run (step initial resetInput) pins n
  by_cases pending : s.r9_ncontractPending = 1
  · have legal := MulDivCheckedMetadata.legal_run initial resetInput reset pins n pending
    have range : s.r11_ncontractFn < 8#4 := legal.1
    have operations : s.r11_ncontractFn < 4#4 ∨
        (s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6) ∨
        (s.r11_ncontractFn = 5 ∨ s.r11_ncontractFn = 7) := by bv_decide
    rcases operations with multiply | signed | unsigned
    · exact MulDivCheckedMulTiming.timing_assertions_after_reset initial resetInput reset pins n multiply
    · exact MulDivCheckedSignedTiming.timing_assertions_after_reset initial resetInput reset pins n signed
    · exact MulDivCheckedUnsignedTiming.timing_assertions_after_reset initial resetInput reset pins n unsigned
  · exact inactive s (pins n) pending

end MulDivCheckedTiming
