import Proofs.ReferenceBranchTakenPc
import Proofs.ReferenceBranchNotTakenPc
namespace RiscvMiniProofs
open nCoreSoc
theorem reference_beq_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6688 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_beq_target (s : State) (i : Inputs) :
    v6875 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_beq_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99)
    (aligned : v6665 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6665 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6665 s i) with idle | taken
  · exact ⟨reference_beq_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_beq_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_beq_alignment s i config).mpr (aligned taken)
    exact ⟨reference_beq_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_beq_target] using
        reference_beq_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_beq_event_and_pc

theorem reference_bne_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6664 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_bne_target (s : State) (i : Inputs) :
    v6871 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_bne_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195)
    (aligned : v6641 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6641 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6641 s i) with idle | taken
  · exact ⟨reference_bne_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_bne_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_bne_alignment s i config).mpr (aligned taken)
    exact ⟨reference_bne_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_bne_target] using
        reference_bne_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_bne_event_and_pc

theorem reference_blt_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6640 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_blt_target (s : State) (i : Inputs) :
    v6867 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_blt_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483)
    (aligned : v6617 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6617 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6617 s i) with idle | taken
  · exact ⟨reference_blt_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_blt_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_blt_alignment s i config).mpr (aligned taken)
    exact ⟨reference_blt_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_blt_target] using
        reference_blt_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_blt_event_and_pc

theorem reference_bltu_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6616 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_bltu_target (s : State) (i : Inputs) :
    v6863 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_bltu_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675)
    (aligned : v6593 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6593 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6593 s i) with idle | taken
  · exact ⟨reference_bltu_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_bltu_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_bltu_alignment s i config).mpr (aligned taken)
    exact ⟨reference_bltu_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_bltu_target] using
        reference_bltu_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_bltu_event_and_pc

theorem reference_bge_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6592 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_bge_target (s : State) (i : Inputs) :
    v6859 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_bge_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579)
    (aligned : v6569 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6569 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6569 s i) with idle | taken
  · exact ⟨reference_bge_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_bge_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_bge_alignment s i config).mpr (aligned taken)
    exact ⟨reference_bge_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_bge_target] using
        reference_bge_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_bge_event_and_pc

theorem reference_bgeu_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v6568 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 :=
  reference_jal_alignment s i config

theorem reference_bgeu_target (s : State) (i : Inputs) :
    v6855 s i = v2222 s i + v2092 s i := reference_jal_target s i

theorem reference_bgeu_event_and_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (config : ReferenceConfig s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771)
    (aligned : v6545 s i = 1 → BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0) :
    TaskHolds ⟨40, by decide⟩ s i ∧
      (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        if v6545 s i = 1 then v2222 s i + v2092 s i else v2222 s i + 4 := by
  rcases BitVec.eq_zero_or_eq_one (v6545 s i) with idle | taken
  · exact ⟨reference_bgeu_not_taken_event_task s i reset env commit idle known,
      by simpa [idle] using reference_bgeu_not_taken_next_pc s i reset commit idle known⟩
  · have guard := (reference_bgeu_alignment s i config).mpr (aligned taken)
    exact ⟨reference_bgeu_taken_event_task s i reset env commit guard taken known,
      by simpa [taken, reference_bgeu_target] using
        reference_bgeu_taken_next_pc s i reset commit guard taken known⟩
#print axioms reference_bgeu_event_and_pc

end RiscvMiniProofs
