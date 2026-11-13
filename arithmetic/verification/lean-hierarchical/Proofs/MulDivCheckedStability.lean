import Proofs.MulDivCheckedTimingInvariant

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem stalled_core (s : State) (i : Inputs) (valid : v38 s i = 1)
    (ready : i.nio_5Fresp_5Fready = 0) (alive : i.nio_5Fkill = 0)
    (reset : i.nreset = 0) : coreState (step s i) = coreState s := by
  have state := stalled_control s i valid ready alive reset
  obtain ⟨bits, high, word, tag⟩ := terminal_payload s i valid
  have done : s.r0_nstate = 6 ∨ s.r0_nstate = 7 := by
    simp only [v38, v36, v37, v35, v4] at valid
    bv_decide
  have rest : (step s i).r3_ncount = s.r3_ncount ∧
      (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout ∧
      (step s i).r5_nisHi = s.r5_nisHi ∧ (step s i).r7_ndivisor = s.r7_ndivisor := by
    rcases done with h | h <;>
      simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v7, v31, v41, v42,
        v48, v54, v55, v71, v72, v73, v89, v90, v91, v92, v93, v107, v108, v109, h]
    all_goals bv_decide
  simp only [coreState, state, bits, high, word, tag, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2]

theorem pending_not_idle (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat)
    (pending : (run (step s resetInput) inputs n).r9_ncontractPending = 1) :
    (run (step s resetInput) inputs n).r0_nstate ≠ 0 := by
  let current := run (step s resetInput) inputs n
  have legal := legal_after_reset s resetInput reset inputs n pending
  change HierarchicalMulDiv.legalArithmetic (coreInputs (recordedRequest current)) at legal
  simp only [HierarchicalMulDiv.legalArithmetic, coreInputs, recordedRequest] at legal
  rcases legal with mul | sign | unsign
  · have operation : BitVec.extractLsb' 2 1 current.r11_ncontractFn = 0 := by bv_decide
    have state := multiply_timing_after_reset s resetInput reset inputs n pending operation
    dsimp only at state
    bv_decide
  · have state := signed_timing_after_reset s resetInput reset inputs n pending sign
    dsimp only at state
    rcases state.2 with h | h | h | h <;> rw [h.1] <;> decide
  · have state := unsigned_timing_after_reset s resetInput reset inputs n pending unsign
    bv_decide

end HierarchicalMulDivChecked
