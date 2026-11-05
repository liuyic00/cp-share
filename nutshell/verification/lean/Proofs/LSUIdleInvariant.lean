import Proofs.NonAtomicLSUPipeline
import Proofs.NonAtomicPipeline
import Proofs.LSUNonAtomic
namespace NutShellProofs
open nNutCore

theorem lsu_request_controls (s : State) (i : Inputs) (request : v11525 s i = 1) :
    v3 s i = 1 ∧ v6 s i = 1 := by
  have unit : v3 s i = 1 := by
    by_cases h : v3 s i = 1
    · exact h
    · have inactive : v11521 s i = 0 := if_neg h
      simp [v11525, v11524, v11522, inactive] at request
  have valid : v6 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v6 s i) with zero | one
    · simp [v11525, v11524, v11522, zero] at request
    · exact one
  exact ⟨unit, valid⟩

theorem original_assumptions_non_atomic_lsu_requests (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t)) (t : Nat) :
    NonAtomicLSURequest (run initial inputs (t + 1)) (inputs (t + 1)) := by
  intro request
  obtain ⟨unit, valid⟩ := lsu_request_controls _ _ request
  have instruction := (non_atomic_pipeline_run initial inputs reset environment t).2.2 valid
  exact (lsu_non_atomic_decode_run initial inputs reset t).2 valid instruction unit

theorem original_assumptions_lsu_idle_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t)) (t : Nat) :
    (run initial inputs (t + 1)).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  exact non_atomic_requests_lsu_idle_run initial inputs reset
    (original_assumptions_non_atomic_lsu_requests initial inputs reset environment) t

theorem branch_no_trap_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t))
    (t : Nat) (operation : BranchOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  exact branch_no_trap_with_idle_lsu_run initial inputs reset t operation valid unit matched
    (original_assumptions_lsu_idle_run initial inputs reset environment t)

#print axioms original_assumptions_non_atomic_lsu_requests
#print axioms original_assumptions_lsu_idle_run
#print axioms branch_no_trap_run
end NutShellProofs
