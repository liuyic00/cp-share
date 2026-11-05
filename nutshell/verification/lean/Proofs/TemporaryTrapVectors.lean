import Proofs.TemporaryRegisterStep
namespace NutShellProofs
open nNutCore

def TrapVectorsZero (s : State) : Prop :=
  s.g42.r1373_nbackend_5Fexu_5Fcsr_5Fmtvec = 0 ∧
  s.g43.r1397_nbackend_5Fexu_5Fcsr_5Fstvec = 0

theorem trap_vectors_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    TrapVectorsZero (step s i) := by
  constructor
  · change v13477 s i = 0
    simp [v13477, v13172, v12103, v11455, reset, v13175]
  · change v14238 s i = 0
    simp [v14238, v13172, v12103, v11455, reset, v14233]

theorem trap_vectors_hold_without_csr (s : State) (i : Inputs)
    (old : TrapVectorsZero s) (inactive : v13181 s i = 0) :
    TrapVectorsZero (step s i) := by
  constructor
  · change v13477 s i = 0
    simp [v13477, v13175, v13476, v13475, v13472, v13454, v13451,
      v13185, inactive, old.1]
  · change v14238 s i = 0
    simp [v14238, v14233, v14237, v14236, v13472, v13454, v13451,
      v13185, inactive, old.2]

theorem temporary_pc32_csr_inactive_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    v13181 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v6 (run initial inputs (t + 1)) (inputs (t + 1))) with zero | one
  · simp [v13181, v13180, v13178, zero]
  · rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t one with alu | lsu
    · simp [v13181, v13180, v13178, v13177, v13176, alu]
    · simp [v13181, v13180, v13178, v13177, v13176, lsu]

theorem temporary_pc32_trap_vectors_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    TrapVectorsZero (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact trap_vectors_reset _ _ reset
  | succ t ih =>
    exact trap_vectors_hold_without_csr _ _ ih
      (temporary_pc32_csr_inactive_run initial inputs reset environment restriction t)

theorem trap_vector_target_zero (s : State) (i : Inputs) (vectors : TrapVectorsZero s) :
    v25360 s i = 0 := by
  simp [v25360, v25359, vectors.1, vectors.2]

theorem committed_trap_target_zero (s : State) (i next : Inputs)
    (vectors : TrapVectorsZero s) (inactive : v13181 s i = 0)
    (noMou : v25339 s i = 0) (trap : v13725 s i = 1)
    (commit : v9 (step s i) next = 1) : v2709 (step s i) next = 0 := by
  have target := trap_vector_target_zero s i vectors
  change v25374 s i = 0
  rw [v25374, if_pos (commit_requires_capture s i next commit)]
  simp [v25373, v25372, noMou, v25371, v25354, v25353, v25349,
    v25348, inactive, trap, v25352, v13454, v13451, v13185,
    v25370, v25369, v25368, target]

theorem temporary_pc32_committed_trap_target_zero_run
    (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (trap : v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v2709 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have units := temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid
  have noMou : v25339 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
    rcases units with alu | lsu
    · simp [v25339, v27, v26, v7, v5, v4, alu]
    · simp [v25339, v27, v26, v7, v5, v4, lsu]
  exact committed_trap_target_zero _ _ _
    (temporary_pc32_trap_vectors_run initial inputs reset environment restriction t)
    (temporary_pc32_csr_inactive_run initial inputs reset environment restriction t)
    noMou trap commit

#print axioms temporary_pc32_committed_trap_target_zero_run
#print axioms temporary_pc32_trap_vectors_run
#print axioms trap_vector_target_zero
end NutShellProofs
