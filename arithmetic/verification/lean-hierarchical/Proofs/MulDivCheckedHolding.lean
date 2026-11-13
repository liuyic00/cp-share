import Proofs.MulDivCheckedTag

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

private theorem terminal_cases (s : State) (i : Inputs) (valid : v38 s i = 1) :
    s.r0_nstate = 6 ∨ s.r0_nstate = 7 := by
  simp only [v38, v36, v37, v35, v4] at valid
  bv_decide

theorem stalled_control (s : State) (i : Inputs) (valid : v38 s i = 1)
    (ready : i.nio_5Fresp_5Fready = 0) (alive : i.nio_5Fkill = 0)
    (reset : i.nreset = 0) : (step s i).r0_nstate = s.r0_nstate := by
  rcases terminal_cases s i valid with done | done <;>
    simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v4, v7, v35, v36, v37,
      v38, v39, v40, v41, v42, v45, v48, v51, v52, v53, v54, v55, v56,
      v57, v58, v59, v60, v61, done, ready, alive, reset]

theorem terminal_payload (s : State) (i : Inputs) (valid : v38 s i = 1) :
    (step s i).r8_nremainder = s.r8_nremainder ∧
    (step s i).r6_nresHi = s.r6_nresHi ∧
    (step s i).r1_nreq_5Fdw = s.r1_nreq_5Fdw ∧
    (step s i).r2_nreq_5Ftag = s.r2_nreq_5Ftag := by
  rcases terminal_cases s i valid with done | done <;>
    simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v7, v31, v41, v42, v48,
      v51, v52, v53, v54, v55, v62, v63, v94, v95, v96, v97, v98, v99,
      v100, v141, v142, v148, v149, v150, v151, done]
  all_goals bv_decide

theorem stalled_output (s : State) (i later : Inputs) (valid : v38 s i = 1)
    (ready : i.nio_5Fresp_5Fready = 0) (alive : i.nio_5Fkill = 0)
    (reset : i.nreset = 0) :
    v38 (step s i) later = 1 ∧ v187 (step s i) later = v187 s i ∧
      (step s i).r2_nreq_5Ftag = s.r2_nreq_5Ftag := by
  have state := stalled_control s i valid ready alive reset
  obtain ⟨bits, high, word, tag⟩ := terminal_payload s i valid
  refine ⟨?_, ?_, tag⟩
  · simpa only [v38, v36, v37, v35, v4, state] using valid
  · simp only [v187, v186, v185, v184, v183, v182, v181, v180, v179,
      v145, v144, v119, bits, high, word, state]

def StallInvariant (s : State) : Prop :=
  s.r21_ncontractWasStalled = 1 → ∀ i,
    v38 s i = 1 ∧ v187 s i = s.r19_ncontractPreviousData ∧
      s.r2_nreq_5Ftag = s.r20_ncontractPreviousTag

private theorem stall_condition (reset pending valid ready kill : BitVec 1)
    (h : (if reset = 1 then 0#1 else
      ((pending &&& valid) &&& (ready ^^^ 1#1)) &&& (kill ^^^ 1#1)) = 1) :
    reset = 0 ∧ valid = 1 ∧ ready = 0 ∧ kill = 0 := by bv_decide

theorem stall_after_step (s : State) (i : Inputs) : StallInvariant (step s i) := by
  intro active later
  have flag : (step s i).r21_ncontractWasStalled =
      (if i.nreset = 1 then 0#1 else
        ((s.r9_ncontractPending &&& v38 s i) &&& (i.nio_5Fresp_5Fready ^^^ 1#1)) &&&
          (i.nio_5Fkill ^^^ 1#1)) := by
    simp only [step, eval_eq_spec, evalSpec, v8, v190, v188, v189, v31]
  rw [flag] at active
  obtain ⟨reset, valid, ready, alive⟩ := stall_condition _ _ _ _ _ active
  have result := stalled_output s i later valid ready alive reset
  simpa only [step, eval_eq_spec, evalSpec] using result

theorem stall_checks (s : State) (i : Inputs) (inv : StallInvariant s) :
    (v285 s i ≠ 1 ∨ v38 s i = 1) ∧
    (v285 s i ≠ 1 ∨ v286 s i = 1) ∧
    (v285 s i ≠ 1 ∨ v287 s i = 1) := by
  have h := fun active => inv active i
  simp only [v285, v286, v287]
  bv_decide

end HierarchicalMulDivChecked
