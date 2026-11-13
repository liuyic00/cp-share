import Proofs.MulDivCheckedArithmetic

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- The request retained by the monitor, with inactive reset and kill. -/
def recordedRequest (s : State) : Inputs :=
  { nreset := 0, nio_5Freq_5Fvalid := 1,
    nio_5Freq_5Fbits_5Ffn := s.r11_ncontractFn,
    nio_5Freq_5Fbits_5Fdw := s.r12_ncontractDw,
    nio_5Freq_5Fbits_5Fin1 := s.r13_ncontractA,
    nio_5Freq_5Fbits_5Fin2 := s.r14_ncontractB,
    nio_5Freq_5Fbits_5Ftag := s.r15_ncontractTag,
    nio_5Fkill := 0, nio_5Fresp_5Fready := 0 }

theorem recorded_capture (s : State) (i : Inputs) (capture : v2 s i = 1) :
    recordedRequest (step s i) =
      { i with nreset := 0, nio_5Freq_5Fvalid := 1, nio_5Fkill := 0, nio_5Fresp_5Fready := 0 } := by
  simp only [recordedRequest, step, eval_eq_spec, evalSpec,
    v169, v170, v171, v172, v173, capture, if_true]

theorem recorded_hold (s : State) (i : Inputs) (idleCapture : v2 s i ≠ 1) :
    recordedRequest (step s i) = recordedRequest s := by
  simp only [recordedRequest, step, eval_eq_spec, evalSpec,
    v169, v170, v171, v172, v173, idleCapture, if_false]

theorem monitor_accepts_legal (s : State) (i : Inputs) (accepted : v160 s i = 1) :
    legalArithmetic i := by
  simp only [v160, v153, v152, v158, v155, v154, v157, v156, v15,
    v159, v31] at accepted
  simp only [legalArithmetic, HierarchicalMulDiv.legalArithmetic, coreInputs]
  bv_decide

def LegalInvariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → legalArithmetic (recordedRequest s)

theorem legal_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    LegalInvariant (step s i) := by
  simp [LegalInvariant, step, eval_eq_spec, evalSpec, reset, v8]

theorem legal_preserved (s : State) (i : Inputs) (inv : LegalInvariant s) :
    LegalInvariant (step s i) := by
  have accepted := monitor_accepts_legal s i
  simp only [LegalInvariant, legalArithmetic, HierarchicalMulDiv.legalArithmetic,
    recordedRequest, coreInputs] at inv ⊢
  simp only [legalArithmetic, HierarchicalMulDiv.legalArithmetic, coreInputs] at accepted
  simp only [step, eval_eq_spec, evalSpec, v8, v163, v162, v169, v170]
  bv_decide

theorem legal_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    LegalInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact legal_reset s resetInput reset
  | succ n ih => exact legal_preserved _ _ ih

end HierarchicalMulDivChecked
