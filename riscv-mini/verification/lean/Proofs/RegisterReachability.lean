import Proofs.SignedLoadCommit
import Proofs.PcBridge
namespace RiscvMiniProofs
open nCoreSoc

-- PC remains an explicit proof obligation, never an Environment assumption.
theorem registers_agree_reachable_of_pc (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (pc : ∀ t, cycles ≤ t → ValidWritebackPcAgreement (run initial inputs t))
    (t : Nat) (ht : cycles ≤ t) : RegisterAgreement (run initial inputs t) := by
  have base := registers_agree_at_reset_boundary initial inputs cycles reset
  induction t with
  | zero => have := reset.1; omega
  | succ t ih =>
    by_cases prev : cycles ≤ t
    · have agree := ih prev
      rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
      · exact registers_agree_noncommit initial inputs cycles reset env t prev agree idle
      · have currentPc := pc t prev ((commit_iff_valid_writeback _ _ (reset.2.2 t prev)).mp commit)
        exact (register_tasks_iff_next _ _ (reset.2.2 t prev) commit).mp
          (register_tasks_reachable_of_pc initial inputs cycles reset env t prev agree commit currentPc)
    · have eq : t + 1 = cycles := by omega
      simpa only [eq] using base

-- The original PC assertion supplies exactly the guarded PC relation above.
theorem registers_agree_reachable_of_pc_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (pc : ∀ t, cycles ≤ t → TaskHolds ⟨7, by decide⟩ (run initial inputs t) (inputs t))
    (t : Nat) (ht : cycles ≤ t) : RegisterAgreement (run initial inputs t) := by
  apply registers_agree_reachable_of_pc initial inputs cycles reset env _ t ht
  intro n hn
  exact (pc_task_iff_valid_agreement _ _ (reset.2.2 n hn)).mp (pc n hn)

#print axioms registers_agree_reachable_of_pc_task
#print axioms registers_agree_reachable_of_pc
end RiscvMiniProofs
