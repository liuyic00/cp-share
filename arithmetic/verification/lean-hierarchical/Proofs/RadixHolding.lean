import Proofs.RadixHistory

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

theorem done_output_stable (s : State) (i later : Inputs) (done : s.r0_nstate = 4) :
    v412 (step s i) later = v412 s i := by
  simp [v412, v411, v410, v409, v408, v407, v406, v405, v404, v403, v402,
    v40, v20, step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5,
    v6, v7, v8, v25, v42, v43, v44, v47, v52, v60, v61, done]

theorem stalled_state (s : State) (i : Inputs) (done : s.r0_nstate = 4)
    (blocked : i.nio_5Fout_5Fready = 0) (reset : i.nreset ≠ 1) :
    (step s i).r0_nstate = 4 := by
  simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6, v7,
    v8, v11, v13, v14, v15, v16, v17, v18, v19, done, blocked, reset]
  exact reset

def StallInvariant (s : State) : Prop :=
  s.r13_nwasStalled = 1 → s.r0_nstate = 4 ∧ ∀ i, v412 s i = s.r14_npreviousOutput

private theorem stalled_condition (reset ready : BitVec 1) (state : BitVec 3)
    (active : (if reset = 1 then 0#1 else
      (if state = 4 then 1#1 else 0#1) &&& (ready ^^^ 1#1)) = 1) :
    reset ≠ 1 ∧ state = 4 ∧ ready = 0 := by bv_decide

theorem stall_after_step (s : State) (i : Inputs) : StallInvariant (step s i) := by
  intro active
  have flag : (step s i).r13_nwasStalled =
      (if i.nreset = 1 then 0#1 else
        (if s.r0_nstate = 4 then 1#1 else 0#1) &&& (i.nio_5Fout_5Fready ^^^ 1#1)) := by
    simp only [step, eval_eq_spec, evalSpec, v26, v401, v399, v11, v400, v22]
    rfl
  rw [flag] at active
  obtain ⟨reset, done, blocked⟩ := stalled_condition _ _ _ active
  constructor
  · exact stalled_state s i done blocked reset
  · intro later
    rw [done_output_stable s i later done]
    simp only [step, eval_eq_spec, evalSpec]

theorem stall_checks (s : State) (i : Inputs) (inv : StallInvariant s) :
    ((v444 s i) ≠ 1 ∨ (v399 s i) = 1) ∧
    ((v444 s i) ≠ 1 ∨ (v445 s i) = 1) := by
  have h : s.r13_nwasStalled = 1 → s.r0_nstate = 4 ∧ v412 s i = s.r14_npreviousOutput :=
    fun active => ⟨(inv active).1, (inv active).2 i⟩
  simp only [v444, v416, v22, v399, v11, v445]
  bv_decide

theorem control_invariants_after_reset (s : State) (resetInput : Inputs)
    (inputs : Nat → Inputs) (n : Nat) :
    HistoryInvariant (run (step s resetInput) inputs n) ∧
    StallInvariant (run (step s resetInput) inputs n) := by
  cases n with
  | zero => exact ⟨history_after_step s resetInput, stall_after_step s resetInput⟩
  | succ n => exact ⟨history_after_step _ _, stall_after_step _ _⟩

end HierarchicalRadix
