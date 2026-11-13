import Proofs.RadixInitialization

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

def flags (s : State) : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 :=
  (s.r3_naSignReg, s.r4_nqSignReg, s.r7_nctrlReg_5FisW, s.r8_nctrlReg_5FisHi)

theorem flags_stable (s : State) (i : Inputs) (active : s.r0_nstate ≠ 0#3) :
    flags (step s i) = flags s := by
  simp [flags, step, eval_eq_spec, evalSpec, v0, v1, v2, v47, v52, v60, v61, active]

theorem computing_flags (s : State) (inputs : Nat → Inputs)
    (computing : s.r0_nstate = 3)
    (reset : ∀ t, t < 64 - s.r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0)
    (n : Nat) (within : n ≤ 64 - s.r9_ncnt_5Fvalue.toNat) :
    flags (run s inputs n) = flags s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have state := (computing_prefix s inputs computing reset n (by omega)).1
    rw [run, flags_stable _ _ (by rw [state]; decide)]
    exact ih (by omega)

/-- The response-format metadata is retained until the exact completion edge. -/
theorem accepted_flags (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    flags (run s inputs (3 + (64 - (run s inputs 3).r9_ncnt_5Fvalue.toNat))) =
      flags (step s (inputs 0)) := by
  have first : (run s inputs 1).r0_nstate = 1 :=
    (capture_request s (inputs 0) idle valid (reset 0 (by omega))).1
  have second : (run s inputs 2).r0_nstate = 2 :=
    setup_control _ _ first (reset 1 (by omega))
  have third : (run s inputs 3).r0_nstate = 3 :=
    (load_control _ _ second (reset 2 (by omega))).1
  have setupFlags : flags (run s inputs 3) = flags (step s (inputs 0)) := by
    change flags (step (run s inputs 2) (inputs 2)) = _
    rw [flags_stable _ _ (by rw [second]; decide)]
    change flags (step (run s inputs 1) (inputs 1)) = _
    rw [flags_stable _ _ (by rw [first]; decide)]
    rfl
  rw [run_offset]
  exact (computing_flags _ (fun t => inputs (3 + t)) third
    (by intro t bound; apply reset; omega) _ (Nat.le_refl _)).trans setupFlags

#print axioms accepted_flags
end HierarchicalRadix
