import Proofs.MulDivSignedInit

namespace MulDivSigned
open nMulDiv
open MulDivDivision (packed)
open MulDivOutput (metadata)

/-- Division by zero suppresses quotient negation, but keeps the dividend's
sign for remainder. This applies to the first restoring edge only. -/
def effectiveNegative (d : BitVec 64) (isHi negative : BitVec 1) : BitVec 1 :=
  if d = 0 then (if isHi = 1 then negative else 0) else negative

theorem first_flag (s : State) (i : Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : packed s = 0#65 ++ a) :
    (step s i).r4_nneg_5Fout = effectiveNegative d s.r5_nisHi s.r4_nneg_5Fout := by
  simp only [step, eval, state, count, divisor, effectiveNegative]
  simp only [packed] at initial
  bv_decide

theorem later_flag (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (count : s.r3_ncount ≠ 0) : (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout := by
  simp only [step, eval, state]
  bv_decide

theorem flags_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (positive : 0 < s.r3_ncount.toNat)
    (remaining : s.r3_ncount.toNat + n ≤ 65)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    metadata (run s inputs n) = metadata s ∧
    (run s inputs n).r4_nneg_5Fout = s.r4_nneg_5Fout := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have control := MulDivDivision.div_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have notZero : (run s inputs n).r3_ncount ≠ 0 := by
      intro eq
      have : (run s inputs n).r3_ncount.toNat = 0 := congrArg BitVec.toNat eq
      omega
    change metadata (step (run s inputs n) (inputs n)) = _ ∧ _
    exact ⟨(MulDivOutput.metadata_edge _ _ control.1).trans prior.1,
      (later_flag _ _ control.1 notZero).trans prior.2⟩

theorem last_signed_edge (s : State) (i : Inputs)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 64)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = (if s.r4_nneg_5Fout = 1 then 5 else 7) ∧
    (step s i).r6_nresHi = s.r5_nisHi := by
  simp only [step, eval, state, count, reset, kill]
  bv_decide

theorem finish64 (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 1)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 64).r0_nstate = (if s.r4_nneg_5Fout = 1 then 5 else 7) ∧
    (run s inputs 64).r6_nresHi = s.r5_nisHi ∧
    metadata (run s inputs 64) = metadata s := by
  have countNat : s.r3_ncount.toNat = 1 := congrArg BitVec.toNat count
  have control := MulDivDivision.div_prefix 63 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have flags := flags_run 63 s inputs state (by omega) (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have lastCount : (run s inputs 63).r3_ncount = 64 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs 63).r3_ncount.toNat = 64
    omega
  have edge := last_signed_edge (run s inputs 63) (inputs 63) control.1 lastCount
    (reset 63 (by decide)) (kill 63 (by decide))
  rw [flags.2] at edge
  exact ⟨edge.1, edge.2.trans (congrArg (fun m => m.2.2) flags.1),
    (flags_run 64 s inputs state (by omega) (by omega) reset kill).1⟩

theorem finish65 (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : packed s = 0#65 ++ a)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 65).r0_nstate =
      (if effectiveNegative d s.r5_nisHi s.r4_nneg_5Fout = 1 then 5 else 7) ∧
    (run s inputs 65).r6_nresHi = s.r5_nisHi ∧
    metadata (run s inputs 65) = metadata s := by
  have edge := MulDivControl.div_edge s (inputs 0) state (reset 0 (by decide)) (kill 0 (by decide))
  have nextState : (step s (inputs 0)).r0_nstate = 3 := by simpa [count] using edge.1
  have nextCount : (step s (inputs 0)).r3_ncount = 1 := by simpa [count] using edge.2
  have result := finish64 (step s (inputs 0)) (fun t => inputs (t + 1)) nextState nextCount
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  have flag := first_flag s (inputs 0) a d state count divisor initial
  have metaStable := MulDivOutput.metadata_edge s (inputs 0) state
  rw [flag] at result
  rw [show 65 = 64 + 1 from rfl, MulDivControl.run_from_next]
  exact ⟨result.1, result.2.1.trans (congrArg (fun m => m.2.2) metaStable), result.2.2.trans metaStable⟩

end MulDivSigned
