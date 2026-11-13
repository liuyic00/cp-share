import Generated.MulDiv
import Std.Tactic

namespace MulDivControl
open nMulDiv

theorem reset_ready (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r0_nstate = 0 := by
  simp [step, eval, reset]

theorem mul_edge (s : State) (i : Inputs) (state : s.r0_nstate = 2)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = (if s.r3_ncount = 63 then 6 else 2) ∧
    (step s i).r3_ncount = s.r3_ncount + 1 := by
  simp only [step, eval, state, reset, kill]
  bv_decide

theorem div_edge (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate =
      (if s.r3_ncount = 64 then (if s.r4_nneg_5Fout = 1 then 5 else 7) else 3) ∧
    (step s i).r3_ncount = s.r3_ncount + 1 := by
  simp only [step, eval, state, reset, kill]
  bv_decide

theorem negate_inputs_edge (s : State) (i : Inputs) (state : s.r0_nstate = 1)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = s.r3_ncount := by
  simp only [step, eval, state, reset, kill]
  bv_decide

theorem negate_output_edge (s : State) (i : Inputs) (state : s.r0_nstate = 5)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 7 := by
  simp only [step, eval, state, reset, kill]
  bv_decide

theorem done_valid (s : State) (i : Inputs) (done : s.r0_nstate = 6 ∨ s.r0_nstate = 7) :
    (observe s i).nio_5Fresp_5Fvalid = 1 := by
  rcases done with done | done <;> simp [observe, eval, done]

theorem acceptance (s : State) (i : Inputs) (ready : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1) (reset : i.nreset = 0) :
    ((step s i).r0_nstate = 2 ∨ (step s i).r0_nstate = 1 ∨
      (step s i).r0_nstate = 3) ∧
    ((step s i).r3_ncount = 0 ∨ (step s i).r3_ncount = 32) := by
  simp only [step, eval, ready, valid, reset]
  bv_decide

def Done (s : State) : Prop := s.r0_nstate = 6 ∨ s.r0_nstate = 7

def Live (s : State) : Prop :=
  (s.r0_nstate = 1 ∧ s.r3_ncount.toNat ≤ 64) ∨
  (s.r0_nstate = 2 ∧ s.r3_ncount.toNat ≤ 63) ∨
  (s.r0_nstate = 3 ∧ s.r3_ncount.toNat ≤ 64) ∨
  s.r0_nstate = 5 ∨ Done s

def remaining (s : State) : Nat :=
  if s.r0_nstate = 1 then 67 - s.r3_ncount.toNat
  else if s.r0_nstate = 2 then 64 - s.r3_ncount.toNat
  else if s.r0_nstate = 3 then 66 - s.r3_ncount.toNat
  else if s.r0_nstate = 5 then 1 else 0

private theorem increment (count : BitVec 7) (bound : count.toNat ≤ 64) :
    (count + 1).toNat = count.toNat + 1 := by
  rw [BitVec.toNat_add]
  change (count.toNat + 1) % 128 = count.toNat + 1
  omega

theorem live_progress (s : State) (i : Inputs) (live : Live s) (busy : ¬ Done s)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    Live (step s i) ∧ remaining (step s i) < remaining s := by
  rcases live with ⟨state, bound⟩ | ⟨state, bound⟩ | ⟨state, bound⟩ | state | done
  · have edge := negate_inputs_edge s i state reset kill
    constructor
    · exact Or.inr (Or.inr (Or.inl ⟨edge.1, by simpa [edge.2] using bound⟩))
    · simp only [remaining, state, edge.1, edge.2]
      simp
      omega
  · have edge := mul_edge s i state reset kill
    have count := increment s.r3_ncount (by omega)
    by_cases last : s.r3_ncount = 63
    · have nextState : (step s i).r0_nstate = 6 := by simpa only [last, if_true, if_false] using edge.1
      constructor
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl nextState))))
      · simp [remaining, state, nextState, last]
    · have nextState : (step s i).r0_nstate = 2 := by simpa only [last, if_true, if_false] using edge.1
      have notLast : s.r3_ncount.toNat ≠ 63 := by
        intro h
        apply last
        apply BitVec.eq_of_toNat_eq
        exact h
      constructor
      · exact Or.inr (Or.inl ⟨nextState, by rw [edge.2, count]; omega⟩)
      · simp [remaining, state, nextState, edge.2]
        omega
  · have edge := div_edge s i state reset kill
    have count := increment s.r3_ncount bound
    by_cases last : s.r3_ncount = 64
    · by_cases negative : s.r4_nneg_5Fout = 1
      · have nextState : (step s i).r0_nstate = 5 := by simpa only [last, negative, if_true, if_false] using edge.1
        constructor
        · exact Or.inr (Or.inr (Or.inr (Or.inl nextState)))
        · simp [remaining, state, nextState, last]
      · have nextState : (step s i).r0_nstate = 7 := by simpa only [last, negative, if_true, if_false] using edge.1
        constructor
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr nextState))))
        · simp [remaining, state, nextState, last]
    · have nextState : (step s i).r0_nstate = 3 := by simpa only [last, if_true, if_false] using edge.1
      have notLast : s.r3_ncount.toNat ≠ 64 := by
        intro h
        apply last
        apply BitVec.eq_of_toNat_eq
        exact h
      constructor
      · exact Or.inr (Or.inr (Or.inl ⟨nextState, by rw [edge.2, count]; omega⟩))
      · simp [remaining, state, nextState, edge.2]
        omega
  · have nextState := negate_output_edge s i state reset kill
    constructor
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr nextState))))
    · simp [remaining, state, nextState]
  · exact (busy done).elim

private theorem positive_remaining (s : State) (live : Live s) (busy : ¬ Done s) :
    0 < remaining s := by
  rcases live with ⟨state, bound⟩ | ⟨state, bound⟩ | ⟨state, bound⟩ | state | done
  · simp [remaining, state]; omega
  · simp [remaining, state]; omega
  · simp [remaining, state]; omega
  · simp [remaining, state]
  · exact (busy done).elim

theorem run_from_next (s : State) (inputs : Nat → Inputs) (n : Nat) :
    run s inputs (n + 1) =
      run (step s (inputs 0)) (fun t => inputs (t + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step (run s inputs (n + 1)) (inputs (n + 1)) = _
      rw [ih]
      rfl

theorem live_completes (fuel : Nat) (s : State) (inputs : Nat → Inputs)
    (live : Live s) (bound : remaining s ≤ fuel)
    (reset : ∀ t, t < fuel → (inputs t).nreset = 0)
    (kill : ∀ t, t < fuel → (inputs t).nio_5Fkill = 0) :
    ∃ n, n ≤ fuel ∧ Done (run s inputs n) := by
  induction fuel generalizing s inputs with
  | zero =>
    have done : Done s := by
      by_cases done : Done s
      · exact done
      · have positive := positive_remaining s live done
        omega
    exact ⟨0, Nat.le_refl _, done⟩
  | succ fuel ih =>
    by_cases done : Done s
    · exact ⟨0, Nat.zero_le _, done⟩
    · have progress := live_progress s (inputs 0) live done (reset 0 (by omega)) (kill 0 (by omega))
      obtain ⟨n, within, finished⟩ := ih (step s (inputs 0)) (fun t => inputs (t + 1))
        progress.1 (by omega)
        (fun t h => reset (t + 1) (by omega))
        (fun t h => kill (t + 1) (by omega))
      refine ⟨n + 1, by omega, ?_⟩
      rw [run_from_next]
      exact finished

/-- Default 64-bit Rocket MulDiv completes within 67 further edges after
acceptance, including input/output sign handling. Later request pins and
response readiness are unrestricted; reset and kill must remain low. -/
theorem accepted_completes (s : State) (inputs : Nat → Inputs)
    (ready : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 1 ≤ n ∧ n ≤ 68 ∧ (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 := by
  have accepted := acceptance s (inputs 0) ready valid (reset 0 (by omega))
  have count : (step s (inputs 0)).r3_ncount.toNat ≤ 32 := by
    rcases accepted.2 with h | h <;> simp [h]
  have live : Live (step s (inputs 0)) := by
    rcases accepted.1 with h | h | h
    · exact Or.inr (Or.inl ⟨h, by omega⟩)
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h, by omega⟩))
  have bound : remaining (step s (inputs 0)) ≤ 67 := by
    rcases accepted.1 with h | h | h <;> simp [remaining, h] <;> omega
  obtain ⟨n, within, finished⟩ := live_completes 67 (step s (inputs 0))
    (fun t => inputs (t + 1)) live bound
    (fun t h => reset (t + 1) (by omega))
    (fun t h => kill (t + 1) (by omega))
  refine ⟨n + 1, by omega, by omega, ?_⟩
  apply done_valid
  rw [run_from_next]
  exact finished

theorem after_reset_completes (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 1 ≤ n ∧ n ≤ 68 ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 := by
  exact accepted_completes _ inputs (reset_ready initial resetInput resetEdge) valid reset kill

/-- Completed data and tag remain stable under backpressure. -/
theorem stall_stable (s : State) (i later : Inputs) (done : Done s)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0)
    (stall : i.nio_5Fresp_5Fready = 0) :
    (observe (step s i) later).nio_5Fresp_5Fvalid = 1 ∧
    (observe (step s i) later).nio_5Fresp_5Fbits_5Fdata = (observe s i).nio_5Fresp_5Fbits_5Fdata ∧
    (observe (step s i) later).nio_5Fresp_5Fbits_5Ftag = (observe s i).nio_5Fresp_5Fbits_5Ftag := by
  rcases done with state | state <;>
    simp only [observe, step, eval, state, reset, kill, stall] <;> bv_decide

end MulDivControl
