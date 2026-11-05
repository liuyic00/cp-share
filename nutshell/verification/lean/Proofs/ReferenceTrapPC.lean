import Proofs.ReferenceMXLEN
namespace NutShellProofs
open nNutCore

def ReferenceTrapVectorsZero (s : State) : Prop :=
  s.g46.r1480_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5Fmtvec = 0 ∧
  s.g46.r1492_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5Fstvec = 0

theorem reference_trap_vectors_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ReferenceTrapVectorsZero (step s i) := by
  change v23880 s i = 0 ∧ v24122 s i = 0
  simp [v23880, v24122, v14555, v14554, v14553, v11455, reset, v4051]

theorem reference_trap_vectors_step (s : State) (i : Inputs)
    (old : ReferenceTrapVectorsZero s) : ReferenceTrapVectorsZero (step s i) := by
  change v23880 s i = 0 ∧ v24122 s i = 0
  simp [v23880, v24122, v23879, v23542, v24121, v23489, old.1, old.2, v4051]

theorem reference_trap_vectors_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    ReferenceTrapVectorsZero (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact reference_trap_vectors_reset _ _ reset
  | succ t ih => exact reference_trap_vectors_step _ _ ih

theorem reference_exception_pc_zero (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) (exception : v23407 s i = 1)
    (vectors : ReferenceTrapVectorsZero s)
    (mxlen : s.g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = 0 := by
  have supervisor : v23645 s i = 0 := by
    simp [v23645, v23488, v23486, v23487, mxlen, v23644, v23533, v23532,
      v23642, v23535, v23534, v23489, vectors.2, v4079, v23632, v23631, v23630]
  have machine : v23675 s i = 0 := by
    simp [v23675, v23541, v23486, v23487, mxlen, v23674, v23548, v23532,
      v23672, v23550, v23549, v23542, vectors.1, v4079, v23662, v23661, v23660]
  change v23683 s i = 0
  simp [v23683, v14555, v14554, v14553, v11455, reset, v23682, v23681,
    v23680, v14560, v14559, v14558, commit, v23678, exception, v23676,
    supervisor, machine]

#print axioms reference_exception_pc_zero
#print axioms reference_trap_vectors_run
end NutShellProofs
