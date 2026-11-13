import Proofs.RadixFutureInitialization

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

def SetupFuture (s : State) : Prop :=
  ∀ setup load : Inputs, setup.nreset = 0 → load.nreset = 0 →
    FutureResult (step (step s setup) load)

def LoadFuture (s : State) : Prop :=
  ∀ load : Inputs, load.nreset = 0 → FutureResult (step s load)

def ArithmeticInvariant (s : State) : Prop :=
  s.r0_nstate = 0 ∨
  (s.r0_nstate = 1 ∧ SetupFuture s) ∨
  (s.r0_nstate = 2 ∧ LoadFuture s) ∨
  (s.r0_nstate = 3 ∧ FutureResult s) ∨
  (s.r0_nstate = 4 ∧ ResultInvariant s)

private theorem bit_cases (x : BitVec 1) : x = 0 ∨ x = 1 := by bv_decide

private theorem idle_wait (s : State) (i : Inputs) (idle : s.r0_nstate = 0)
    (invalid : i.nio_5Fin_5Fvalid = 0) (reset : i.nreset = 0) : (step s i).r0_nstate = 0 := by
  simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6, v7, v8,
    v11, v13, v14, v15, v16, v17, v18, v19, idle, invalid, reset]

private theorem done_accept (s : State) (i : Inputs) (done : s.r0_nstate = 4)
    (ready : i.nio_5Fout_5Fready = 1) (reset : i.nreset = 0) : (step s i).r0_nstate = 0 := by
  simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6, v7, v8,
    v11, v13, v14, v15, v16, v17, v18, v19, done, ready, reset]

theorem arithmetic_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    ArithmeticInvariant (step s i) := Or.inl (reset_control s i reset)

theorem arithmetic_preserved (s : State) (i : Inputs) (inv : ArithmeticInvariant s) :
    ArithmeticInvariant (step s i) := by
  rcases bit_cases i.nreset with reset | reset
  · rcases inv with idle | ⟨setup, future⟩ | ⟨loading, future⟩ | ⟨computing, future⟩ | ⟨done, result⟩
    · rcases bit_cases i.nio_5Fin_5Fvalid with valid | valid
      · exact Or.inl (idle_wait s i idle valid reset)
      · refine Or.inr (Or.inl ⟨(capture_request s i idle valid reset).1, ?_⟩)
        intro setup load r1 r2
        exact initialized_future s i setup load idle valid reset r1 r2
    · refine Or.inr (Or.inr (Or.inl ⟨setup_control s i setup reset, ?_⟩))
      intro load r2
      exact future i load reset r2
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(load_control s i loading reset).1, future i reset⟩)))
    · have control := (computing_control s i computing reset).1
      by_cases last : s.r9_ncnt_5Fvalue = 63#6
      · have next : (step s i).r0_nstate = 4 := by simpa [last] using control
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨next, future_finishes s i computing last future⟩)))
      · have next : (step s i).r0_nstate = 3 := by simpa [last] using control
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨next, future_compute s i computing reset last future⟩)))
    · rcases bit_cases i.nio_5Fout_5Fready with ready | ready
      · have next := stalled_state s i done ready (by rw [reset]; decide)
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨next, completed_result_preserved s i done result⟩)))
      · exact Or.inl (done_accept s i done ready reset)
  · exact arithmetic_reset s i reset

theorem arithmetic_result (s : State) (inv : ArithmeticInvariant s) : ResultInvariant s := by
  intro done
  rcases inv with idle | ⟨setup, _⟩ | ⟨loading, _⟩ | ⟨computing, _⟩ | ⟨_, result⟩
  · rw [done] at idle; contradiction
  · rw [done] at setup; contradiction
  · rw [done] at loading; contradiction
  · rw [done] at computing; contradiction
  · exact result done

theorem arithmetic_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    ArithmeticInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact arithmetic_reset s resetInput reset
  | succ n ih => exact arithmetic_preserved _ _ ih

theorem asserts_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    asserts (run (step s resetInput) inputs n) (inputs n) := by
  have controls := control_invariants_after_reset s resetInput inputs n
  exact asserts_of_invariants _ _
    (arithmetic_result _ (arithmetic_after_reset s resetInput reset inputs n))
    (divisor_after_reset s resetInput reset inputs n) controls.1 controls.2

end HierarchicalRadix
