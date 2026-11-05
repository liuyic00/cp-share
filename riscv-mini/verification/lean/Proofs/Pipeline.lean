import Proofs.RegisterRelation

namespace RiscvMiniProofs
open nCoreSoc

-- A killed instruction is represented by the NOP in its matching stage.
structure BubbleAlignment (s : State) : Prop where
  fetch : s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 1 →
    s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst = 19
  writeback : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 1 →
    s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst = 19

theorem bubble_alignment_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    BubbleAlignment (step s i) := by
  constructor
  · change v8565 s i = 1 → v7766 s i = 19
    simp [v7766, v1, v0, reset, v427]
  · change v8567 s i = 1 → v7780 s i = 19
    simp [v7780, v1, v0, reset, v427]

theorem no_stall_after_reset (s : State) (i : Inputs) (reset : i.nreset = 0) :
    v13 s i = 0 := by
  simp [v13, v8, v7, v6, v5, v12, v11, v10, v9, v4, reset]

theorem bubble_alignment_step (s : State) (i : Inputs)
    (aligned : BubbleAlignment s) (reset : i.nreset = 0) (trap : v182 s i = 0) :
    BubbleAlignment (step s i) := by
  have stall := no_stall_after_reset s i reset
  constructor
  · change v8565 s i = 1 → v7766 s i = 19
    simp only [v8565, v8564, v8563, v8562, v7766, v7765, v7297,
      v7764, v7761, v7760, v7520, v1, v0, reset, trap, stall, v4, v427]
    simp
    intro yes no
    exact False.elim (no yes)
  · change v8567 s i = 1 → v7780 s i = 19
    simpa [v8567, v8566, v7780, v7779, v7778, v7777, v7776, v7775,
      v7774, v7773, v7772, v1, v0, reset, trap, stall, v4] using aligned.fetch

theorem environment_no_trap (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) : v182 s i = 0 := by
  by_cases h : v182 s i = 0
  · exact h
  · simp [assumes, eval, assumptionChecks, assumptionChecks0,
      v9801, v9800, v9799, v9798, v8625, v8624, v8623, reset, v4] at env
    split at env
    · assumption
    · simp at env

theorem bubble_alignment_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    BubbleAlignment (run initial inputs t) := by
  have base : BubbleAlignment (run initial inputs cycles) := by
    cases cycles with
    | zero => have := reset.1; omega
    | succ n =>
      simp only [run]
      exact bubble_alignment_reset _ _ (reset.2.1 n (Nat.lt_succ_self n))
  induction t with
  | zero => have := reset.1; omega
  | succ n ih =>
    by_cases hn : cycles ≤ n
    · simp only [run]
      exact bubble_alignment_step _ _ (ih hn) (reset.2.2 n hn)
        (environment_no_trap _ _ (reset.2.2 n hn) (env n))
    · have he : n + 1 = cycles := by omega
      simpa only [he] using base

private theorem bit_cases (b : BitVec 1) : b = 0 ∨ b = 1 := by
  by_cases h : b.toNat = 0
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · right
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    change b.toNat = 1
    omega

theorem bubble_does_not_write (s : State) (i : Inputs)
    (aligned : BubbleAlignment s) (reset : i.nreset = 0)
    (commit : v964 s i = 0) : v704 s i = 0 := by
  have stall := no_stall_after_reset s i reset
  have killed : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 1 := by
    rcases bit_cases s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 with hz | ho
    · simp [v964, v963, v962, v961, v960, v959, hz, stall, v1, v0, reset, v4] at commit
    · exact ho
  have instruction := aligned.writeback killed
  simp [v704, v703, v702, v701, instruction, v150]

-- Real executions satisfy the no-write premise of the structural idle lemma.
-- Register agreement on committing steps still requires instruction semantics.
theorem registers_agree_noncommit (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t)
    (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 0) :
    RegisterAgreement (run initial inputs (t+1)) := by
  apply registers_agree_idle _ _ agree (reset.2.2 t ht) commit
  exact bubble_does_not_write _ _
    (bubble_alignment_reachable initial inputs cycles reset env t ht)
    (reset.2.2 t ht) commit

#print axioms bubble_alignment_reachable
#print axioms registers_agree_noncommit
#print axioms bubble_alignment_step
end RiscvMiniProofs
