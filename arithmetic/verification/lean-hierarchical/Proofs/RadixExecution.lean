import Proofs.RadixTransition

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v22 v392 v393 v394 v395 v396 v397 v398 v399

def advanceMany (divisor : BitVec 64) : Nat → BitVec 129 → BitVec 129
  | 0, bits => bits
  | n + 1, bits => advance (advanceMany divisor n bits) divisor

theorem computing_control (s : State) (i : Inputs)
    (computing : s.r0_nstate = 3) (reset : i.nreset = 0) :
    (step s i).r0_nstate = (if s.r9_ncnt_5Fvalue = 63#6 then 4 else 3) ∧
    (step s i).r9_ncnt_5Fvalue = s.r9_ncnt_5Fvalue + 1#6 := by
  simp [step, eval_eq_spec, evalSpec, computing, reset]

/-- Active computation depends on captured state, regardless of later input
    data and downstream readiness. -/
theorem computing_prefix (s : State) (inputs : Nat → Inputs)
    (computing : s.r0_nstate = 3)
    (reset : ∀ t, t < 64 - s.r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0)
    (n : Nat) (beforeLast : n < 64 - s.r9_ncnt_5Fvalue.toNat) :
    (run s inputs n).r0_nstate = 3 ∧
    (run s inputs n).r9_ncnt_5Fvalue.toNat = s.r9_ncnt_5Fvalue.toNat + n ∧
    (run s inputs n).r5_nbReg = s.r5_nbReg ∧
    (run s inputs n).r2_nshiftReg = advanceMany s.r5_nbReg n s.r2_nshiftReg := by
  induction n with
  | zero => simp [run, advanceMany, computing]
  | succ n ih =>
    obtain ⟨state, count, divisor, bits⟩ := ih (by omega)
    have control := computing_control (run s inputs n) (inputs n) state (reset n (by omega))
    have notLast : (run s inputs n).r9_ncnt_5Fvalue ≠ 63#6 := by
      intro h
      have := congrArg BitVec.toNat h
      change (run s inputs n).r9_ncnt_5Fvalue.toNat = 63 at this
      omega
    simp only [run]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [notLast] using control.1
    · rw [control.2, BitVec.toNat_add, count]
      simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
      omega
    · exact (captured_divisor_stable _ _ state).trans divisor
    · rw [compute_edge _ _ state, bits, divisor]
      rfl

/-- The compute phase takes exactly the remaining counter range. -/
theorem computing_finishes (s : State) (inputs : Nat → Inputs)
    (computing : s.r0_nstate = 3)
    (reset : ∀ t, t < 64 - s.r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0) :
    let cycles := 64 - s.r9_ncnt_5Fvalue.toNat
    (run s inputs cycles).r0_nstate = 4 ∧
    (observe (run s inputs cycles) (inputs cycles)).nio_5Fout_5Fvalid = 1 ∧
    (run s inputs cycles).r2_nshiftReg = advanceMany s.r5_nbReg cycles s.r2_nshiftReg := by
  have width := s.r9_ncnt_5Fvalue.isLt
  let n := 63 - s.r9_ncnt_5Fvalue.toNat
  have beforeLast : n < 64 - s.r9_ncnt_5Fvalue.toNat := by dsimp [n]; omega
  obtain ⟨state, count, divisor, bits⟩ := computing_prefix s inputs computing reset n beforeLast
  have last : (run s inputs n).r9_ncnt_5Fvalue = 63#6 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs n).r9_ncnt_5Fvalue.toNat = 63
    have sum : s.r9_ncnt_5Fvalue.toNat + n = 63 := by dsimp [n]; omega
    exact count.trans sum
  have cycles : 64 - s.r9_ncnt_5Fvalue.toNat = n + 1 := by dsimp [n]; omega
  have control := computing_control (run s inputs n) (inputs n) state (reset n beforeLast)
  have finished : (run s inputs (n + 1)).r0_nstate = 4 := by
    simpa [run, last] using control.1
  dsimp only
  rw [cycles]
  refine ⟨finished, ?_, ?_⟩
  · simp [observe, eval_eq_spec, evalSpec, finished]
  · rw [run, compute_edge _ _ state, bits, divisor]
    rfl

#print axioms computing_finishes
end HierarchicalRadix
