import Proofs.LoadSubwordDataRun
import Proofs.LoadAddressCorrespondence
namespace NutShellProofs
open nNutCore

/-- The narrow-load extra cycle retains the address used to capture its response. -/
theorem subword_latched_address_matches_current_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    (run initial inputs (t + 1)).g41.r1333_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FaddrLatch =
      v11612 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
    rw [extra]; decide
  cases t with
  | zero => exact False.elim (busy (lsu_inner_reset initial (inputs 0) reset))
  | succ t =>
    have prior := load_subword_cycle_predecessor _ _ extra
    have priorBusy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
      rw [prior.1]; decide
    have facts := original_assumptions_memory_busy_run initial inputs reset environment t priorBusy
    obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t facts.valid facts.unit
    obtain ⟨noFault, aligned⟩ := memory_raw_alignment_excludes_fault _ _ facts.aligned
    have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
    have nextOuter := original_assumptions_lsu_idle_run initial inputs reset environment (t + 1)
    have hold := memory_next_busy_prevents_capture _ _ operation op outer
      (lsu_inner_reachable_run initial inputs reset t) facts.unit facts.valid noFault aligned busy
    exact (load_address_latch_step _ _).trans
      (lsu_address_hold_without_capture _ _ _ outer nextOuter hold).symm

theorem committed_subword_address_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    (run initial inputs (t + 1)).g41.r1333_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FaddrLatch =
      v24059 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact (subword_latched_address_matches_current_run initial inputs reset environment t extra).trans
    (load_address_matches_reference_node_run initial inputs reset environment t operation load commit unit matched registers)
#print axioms subword_latched_address_matches_current_run
#print axioms committed_subword_address_matches_reference_run
theorem committed_subword_byte_offset_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    v12359 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v16186 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have address := (subword_latched_address_matches_current_run initial inputs reset environment t extra).trans
    (memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers)
  unfold v12359 v16186 v16185 v16184 v16182 v16183
  rw [address]
  simp [low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]
#print axioms committed_subword_byte_offset_matches_reference_run
end NutShellProofs
