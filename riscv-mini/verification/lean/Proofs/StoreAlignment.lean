import Proofs.ReferenceStorePc
import Proofs.TrapFacts
namespace RiscvMiniProofs
open nCoreSoc

theorem reference_store_word_address (s : State) (i : Inputs) :
    v6535 s i = v1721 s i + v2092 s i := by
  change refExec_v2303 (v1721 s i) (v2092 s i) = _
  exact reference_execution_add _ _

theorem reference_store_half_address (s : State) (i : Inputs) :
    v6542 s i = v1721 s i + v2092 s i := reference_store_word_address s i

theorem reference_store_word_alignment (s : State) (i : Inputs) :
    v6538 s i = 1 ↔ BitVec.extractLsb' 0 2 (v1721 s i + v2092 s i) = 0 := by
  simp [v6538, v6536, v6537, reference_store_word_address]

theorem reference_store_half_alignment (s : State) (i : Inputs) :
    v6544 s i = 1 ↔ BitVec.extractLsb' 0 1 (v1721 s i + v2092 s i) = 0 := by
  simp [v6544, v6543, v4, reference_store_half_address]

theorem no_trap_half_store (s : State) (i : Inputs) (trap : v182 s i = 0)
    (store : s.g4.r129_ndut_5Fdpath_5Fst_5Ftype = 2) :
    BitVec.extractLsb' 0 1 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have clean := (no_trap_checks s i trap).2.2.2
  simpa [v47, v46, v45, v44, v43, v42, v41, v40, v39, v38, v32, v18, store] using clean

theorem sh_event_and_pc_of_address (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131)
    (kind : s.g4.r129_ndut_5Fdpath_5Fst_5Ftype = 2)
    (address : s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v2222 s i + 4 := by
  have aligned := no_trap_half_store s i (environment_no_trap s i reset env) kind
  rw [address] at aligned
  have guard := (reference_store_half_alignment s i).mpr aligned
  exact ⟨reference_sh_event_task s i reset env commit guard known,
    reference_sh_next_pc s i reset commit guard known⟩
#print axioms sh_event_and_pc_of_address

theorem sw_event_and_pc_of_address (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227)
    (kind : s.g4.r129_ndut_5Fdpath_5Fst_5Ftype = 1)
    (address : s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v2222 s i + 4 := by
  have aligned := no_trap_word_store s i (environment_no_trap s i reset env) kind
  rw [address] at aligned
  have guard := (reference_store_word_alignment s i).mpr aligned
  exact ⟨reference_sw_event_task s i reset env commit guard known,
    reference_sw_next_pc s i reset commit guard known⟩
#print axioms sw_event_and_pc_of_address

#print axioms reference_store_word_alignment
#print axioms reference_store_half_alignment
#print axioms no_trap_half_store
end RiscvMiniProofs
