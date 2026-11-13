import Proofs.RadixSetupInvariant

namespace nRadix2Divider
set_option maxRecDepth 8192

def ComputeCorrect (s : State) : Prop :=
  ∀ inputs : Nat → Inputs,
    (∀ t, t < 64 - s.r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0) →
    MagnitudeCorrect (run s inputs (64 - s.r9_ncnt_5Fvalue.toNat))

def ShiftCorrect (s : State) : Prop :=
  ∀ i : Inputs, i.nreset = 0 → ComputeCorrect (step s i)

def CaptureCorrect (s : State) : Prop :=
  (s.r1_ndivBy0Reg = 1 ↔ s.r5_nbReg = 0) ∧
  s.r6_naValx2Reg.toNat = 2 * (s.r6_naValx2Reg.extractLsb' 1 64).toNat

def TraceInvariant (s : State) : Prop :=
  s.r0_nstate = 0 ∨
  (s.r0_nstate = 1 ∧ CaptureCorrect s) ∨
  (s.r0_nstate = 2 ∧ ShiftCorrect s) ∨
  (s.r0_nstate = 3 ∧ ComputeCorrect s) ∨
  (s.r0_nstate = 4 ∧ MagnitudeCorrect s)

theorem compute_correct_step (s : State) (i : Inputs)
    (state : s.r0_nstate = 3) (reset : i.nreset = 0) (correct : ComputeCorrect s)
    (notLast : s.r9_ncnt_5Fvalue ≠ 63) : ComputeCorrect (step s i) := by
  have oldBound := s.r9_ncnt_5Fvalue.isLt
  have notCount : s.r9_ncnt_5Fvalue.toNat ≠ 63 := by
    intro h
    apply notLast
    exact BitVec.eq_of_toNat_eq h
  have nextCount : (step s i).r9_ncnt_5Fvalue.toNat = s.r9_ncnt_5Fvalue.toNat + 1 := by
    rw [compute_count s i state reset, BitVec.toNat_add]
    change (s.r9_ncnt_5Fvalue.toNat + 1) % 64 = _
    omega
  have remaining : 64 - s.r9_ncnt_5Fvalue.toNat =
      (64 - (step s i).r9_ncnt_5Fvalue.toNat) + 1 := by omega
  intro inputs resets
  let extended : Nat → Inputs := fun t => match t with | 0 => i | n + 1 => inputs n
  have allResets : ∀ t, t < 64 - s.r9_ncnt_5Fvalue.toNat → (extended t).nreset = 0 := by
    intro t h
    cases t with
    | zero => exact reset
    | succ t => exact resets t (by omega)
  have result := correct extended allResets
  rw [remaining, run_from_next] at result
  exact result

theorem compute_correct_last (s : State) (i : Inputs)
    (reset : i.nreset = 0) (correct : ComputeCorrect s) (lastCount : s.r9_ncnt_5Fvalue = 63) :
    MagnitudeCorrect (step s i) := by
  have countNat : s.r9_ncnt_5Fvalue.toNat = 63 := congrArg BitVec.toNat lastCount
  have result := correct (fun _ => i) (fun _ _ => reset)
  have remaining : 64 - s.r9_ncnt_5Fvalue.toNat = 1 := by omega
  rw [remaining] at result
  exact result

theorem trace_invariant_step (s : State) (i : Inputs) (invariant : TraceInvariant s) :
    TraceInvariant (step s i) := by
  by_cases resetting : i.nreset = 1
  · exact Or.inl (reset_idle s i resetting)
  have reset : i.nreset = 0 := by bv_decide
  rcases invariant with idle | ⟨logState, captured⟩ | ⟨shiftState, shifted⟩ |
    ⟨computeState, computing⟩ | ⟨finishState, finished⟩
  · by_cases valid : i.nio_5Fin_5Fvalid = 1
    · exact Or.inr (Or.inl ⟨accept_state s i idle reset valid, capture_invariant s i idle valid reset⟩)
    · left
      simp only [step, eval, idle, reset]
      bv_decide
  · refine Or.inr (Or.inr (Or.inl ⟨log2_state s i logState reset, ?_⟩))
    intro shift shiftReset inputs resets
    exact (setup_segment_correct s i shift inputs logState reset shiftReset
      captured.1 captured.2 resets).2
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨shift_state s i shiftState reset, shifted i reset⟩)))
  · by_cases lastCount : s.r9_ncnt_5Fvalue = 63
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, compute_correct_last s i reset computing lastCount⟩)))
      rw [compute_state s i computeState reset, if_pos lastCount]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, compute_correct_step s i computeState reset computing lastCount⟩)))
      rw [compute_state s i computeState reset, if_neg lastCount]
  · have control : (step s i).r0_nstate = 0 ∨ (step s i).r0_nstate = 4 := by
      simp only [step, eval, finishState, reset]
      bv_decide
    rcases control with idle | finish
    · exact Or.inl idle
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨finish, finish_preserves_correct s i finishState finished⟩)))

theorem trace_invariant_run (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat) : TraceInvariant (run (step initial resetInput) inputs n) := by
  induction n with
  | zero => exact Or.inl (reset_idle initial resetInput reset)
  | succ n ih => exact trace_invariant_step _ _ ih

theorem trace_invariant_finish (s : State) (invariant : TraceInvariant s) : FinishInvariant s := by
  intro finish
  rcases invariant with idle | ⟨logState, _⟩ | ⟨shiftState, _⟩ | ⟨computeState, _⟩ | ⟨_, correct⟩
  · rw [idle] at finish; contradiction
  · rw [logState] at finish; contradiction
  · rw [shiftState] at finish; contradiction
  · rw [computeState] at finish; contradiction
  · exact correct

/-- Every exported assertion holds on every cycle after reset. Subsequent
requests, operand/control pins, response readiness, and resets are arbitrary. -/
theorem all_assertions_after_reset (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat) : asserts (run (step initial resetInput) inputs n) (inputs n) := by
  cases n with
  | zero => exact asserts_reset_edge initial resetInput (inputs 0) reset
  | succ n =>
    exact finish_invariant_asserts _ _ _ (trace_invariant_finish _
      (trace_invariant_run initial resetInput reset inputs (n + 1)))

end nRadix2Divider
