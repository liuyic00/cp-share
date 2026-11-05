import Proofs.Contract
namespace NutShellProofs
open nNutCore

theorem reference_mxlen_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    (step s i).g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64 := by
  change v24245 s i = 64
  simp [v24245, v14555, v14554, v14553, v11455, reset, v23532]

theorem reference_mxlen_step (s : State) (i : Inputs)
    (old : s.g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64) :
    (step s i).g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64 := by
  change v24245 s i = 64
  simp [v24245, v23532, v24244, v23487, old]

theorem reference_mxlen_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    (run initial inputs (t + 1)).g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64 := by
  induction t with
  | zero => exact reference_mxlen_reset _ _ reset
  | succ t ih => exact reference_mxlen_step _ _ ih
#print axioms reference_mxlen_run
end NutShellProofs
