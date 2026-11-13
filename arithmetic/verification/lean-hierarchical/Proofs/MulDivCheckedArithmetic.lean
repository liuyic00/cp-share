import Proofs.MulDivCheckedCore
import Proofs.MulDivArithmeticContract

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def arithmeticSpecification (i : Inputs) : BitVec 64 :=
  HierarchicalMulDiv.arithmeticSpecification (coreInputs i)

def legalArithmetic (i : Inputs) : Prop :=
  HierarchicalMulDiv.legalArithmetic (coreInputs i)

/-- The checked datapath reuses the core arithmetic contract through the
    projection of its execution trace, independently of monitor contents. -/
theorem arithmetic_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (legal : legalArithmetic (inputs 0))
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 33 ≤ n ∧ n ≤ 68 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = arithmeticSpecification (inputs 0) := by
  obtain ⟨n, lower, upper, response⟩ := HierarchicalMulDiv.arithmetic_accepted
    (coreState s) (fun t => coreInputs (inputs t)) idle valid legal reset alive
  rw [← core_run, ← core_observe] at response
  exact ⟨n, lower, upper, response⟩

theorem arithmetic_after_reset (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (legal : legalArithmetic (inputs 0))
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 33 ≤ n ∧ n ≤ 68 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = arithmeticSpecification (inputs 0) := by
  apply arithmetic_accepted _ inputs _ valid legal reset alive
  simp [step, eval_eq_spec, evalSpec, v0, resetEdge]

end HierarchicalMulDivChecked
