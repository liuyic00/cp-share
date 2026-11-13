import Generated.Radix2Divider

namespace nRadix2Divider
set_option maxRecDepth 4096

/-- Every compute edge advances the six-bit counter. -/
theorem compute_count (s : State) (i : Inputs)
    (state : s.r0_nstate = 3) (reset : i.nreset = 0) :
    (step s i).r9_ncnt_5Fvalue = s.r9_ncnt_5Fvalue + 1 := by
  simp [step, eval, state, reset]

/-- The last iteration enters finish; earlier iterations stay in compute. -/
theorem compute_state (s : State) (i : Inputs)
    (state : s.r0_nstate = 3) (reset : i.nreset = 0) :
    (step s i).r0_nstate = if s.r9_ncnt_5Fvalue = 63 then 4 else 3 := by
  simp [step, eval, state, reset]

theorem accept_state (s : State) (i : Inputs)
    (state : s.r0_nstate = 0) (reset : i.nreset = 0)
    (valid : i.nio_5Fin_5Fvalid = 1) : (step s i).r0_nstate = 1 := by
  simp [step, eval, state, reset, valid]

theorem log2_state (s : State) (i : Inputs)
    (state : s.r0_nstate = 1) (reset : i.nreset = 0) :
    (step s i).r0_nstate = 2 := by
  simp [step, eval, state, reset]

theorem shift_state (s : State) (i : Inputs)
    (state : s.r0_nstate = 2) (reset : i.nreset = 0) :
    (step s i).r0_nstate = 3 := by
  simp [step, eval, state, reset]

theorem finish_valid (s : State) (i : Inputs) (state : s.r0_nstate = 4) :
    (observe s i).nio_5Fout_5Fvalid = 1 := by
  simp [observe, eval, state]

theorem reset_idle (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r0_nstate = 0 := by
  simp [step, eval, reset]

theorem stall_stable (s : State) (i j : Inputs) (state : s.r0_nstate = 4)
    (reset : i.nreset = 0) (ready : i.nio_5Fout_5Fready = 0) :
    (observe (step s i) j).nio_5Fout_5Fvalid = 1 ∧
    (observe (step s i) j).nio_5Fout_5Fbits_5Fdata =
      (observe s i).nio_5Fout_5Fbits_5Fdata := by
  simp [observe, step, eval, state, reset, ready]
theorem run_from_next (s : State) (inputs : Nat → Inputs) (n : Nat) :
    run s inputs (n + 1) =
      run (step s (inputs 0)) (fun t => inputs (t + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step (run s inputs (n + 1)) (inputs (n + 1)) = _
      rw [ih]
      rfl

/-- From any compute state, exactly the remaining counter iterations reach
    finish. Readiness and all data pins are unrestricted. -/
theorem compute_finishes (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (count : s.r9_ncnt_5Fvalue.toNat + n = 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0) :
    (run s inputs n).r0_nstate = 4 := by
  induction n generalizing s inputs with
  | zero =>
      have bound := s.r9_ncnt_5Fvalue.isLt
      omega
  | succ n ih =>
      have r0 := reset 0 (by omega)
      rw [run_from_next]
      by_cases last : s.r9_ncnt_5Fvalue = 63
      · have nzero : n = 0 := by simp [last] at count; omega
        subst n
        simpa [run, last] using compute_state s (inputs 0) state r0
      · have less : s.r9_ncnt_5Fvalue.toNat < 63 := by
          have bound := s.r9_ncnt_5Fvalue.isLt
          have ne : s.r9_ncnt_5Fvalue.toNat ≠ 63 := by
            intro eq
            apply last
            apply BitVec.eq_of_toNat_eq
            simpa using eq
          omega
        have ns : (step s (inputs 0)).r0_nstate = 3 := by
          rw [compute_state s (inputs 0) state r0, if_neg last]
        have nc : (step s (inputs 0)).r9_ncnt_5Fvalue.toNat + n = 64 := by
          rw [compute_count s (inputs 0) state r0, BitVec.toNat_add]
          change (s.r9_ncnt_5Fvalue.toNat + 1) % 64 + n = 64
          omega
        exact ih _ _ ns nc (by intro t ht; apply reset; omega)

/-- A ready/valid acceptance reaches valid output after at most 66 further
    edges. Only absence of reset through the transaction is required; the
    precise latency depends on the captured leading-zero skip count. -/
theorem accepted_completes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 := by
  let s1 := step s (inputs 0)
  let s2 := step s1 (inputs 1)
  let s3 := step s2 (inputs 2)
  have h1 : s1.r0_nstate = 1 := accept_state s _ idle (reset 0 (by omega)) valid
  have h2 : s2.r0_nstate = 2 := log2_state s1 _ h1 (reset 1 (by omega))
  have h3 : s3.r0_nstate = 3 := shift_state s2 _ h2 (reset 2 (by omega))
  let remaining := 64 - s3.r9_ncnt_5Fvalue.toNat
  have bound := s3.r9_ncnt_5Fvalue.isLt
  have small : 1 ≤ remaining ∧ remaining ≤ 64 := by dsimp [remaining]; omega
  have complete := compute_finishes remaining s3 (fun t => inputs (t + 3)) h3
    (by dsimp [remaining]; omega)
    (by intro t ht; apply reset; omega)
  refine ⟨remaining + 3, by omega, by omega, ?_⟩
  apply finish_valid
  rw [show remaining + 3 = (remaining + 2) + 1 by omega, run_from_next,
    show remaining + 2 = (remaining + 1) + 1 by omega, run_from_next,
    run_from_next]
  exact complete
end nRadix2Divider
