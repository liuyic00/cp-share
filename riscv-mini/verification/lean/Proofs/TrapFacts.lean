import Proofs.Pipeline
namespace RiscvMiniProofs
open nCoreSoc

theorem no_trap_checks (s : State) (i : Inputs) (trap : v182 s i = 0) :
    v16 s i = 0 ∧ v20 s i = 0 ∧ v36 s i = 0 ∧ v47 s i = 0 := by
  change v182 s i = 0#1 at trap
  simp only [v182, v181, v175, v168, v164, v146, v48, v37, v21,
    BitVec.or_eq_zero_iff (w := 1)] at trap
  rcases trap with ⟨⟨⟨⟨⟨⟨⟨⟨illegal, pc⟩, load⟩, store⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  exact ⟨illegal, pc, load, store⟩

theorem no_trap_pc_bit (s : State) (i : Inputs) (trap : v182 s i = 0)
    (checked : s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1) :
    BitVec.extractLsb' 1 1 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have pc := (no_trap_checks s i trap).2.1
  simp only [v20, v17, v19, v18, checked] at pc
  exact (BitVec.allOnes_and).symm.trans pc

theorem environment_pc_bit (s : State) (i : Inputs) (reset : i.nreset = 0)
    (env : assumes s i) (checked : s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1) :
    BitVec.extractLsb' 1 1 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 :=
  no_trap_pc_bit s i (environment_no_trap s i reset env) checked

theorem no_trap_word_load (s : State) (i : Inputs) (trap : v182 s i = 0)
    (load : s.g4.r130_ndut_5Fdpath_5Fld_5Ftype = 1) :
    BitVec.extractLsb' 0 2 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have clean := (no_trap_checks s i trap).2.2.1
  simpa [v36, v35, v34, v33, v32, v31, v30, v29, v27, v26, v24, v23, v22, v18, load] using clean

theorem no_trap_word_store (s : State) (i : Inputs) (trap : v182 s i = 0)
    (store : s.g4.r129_ndut_5Fdpath_5Fst_5Ftype = 1) :
    BitVec.extractLsb' 0 2 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have clean := (no_trap_checks s i trap).2.2.2
  simpa [v47, v46, v45, v44, v43, v42, v40, v39, v38, v32, v18, store] using clean

theorem no_trap_unsigned_half_load (s : State) (i : Inputs) (trap : v182 s i = 0)
    (load : s.g4.r130_ndut_5Fdpath_5Fld_5Ftype = 4) :
    BitVec.extractLsb' 0 1 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have clean := (no_trap_checks s i trap).2.2.1
  simpa [v36, v24, v23, v22, v25, v18, load] using clean

theorem no_trap_signed_half_load (s : State) (i : Inputs) (trap : v182 s i = 0)
    (load : s.g4.r130_ndut_5Fdpath_5Fld_5Ftype = 2) :
    BitVec.extractLsb' 0 1 s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
  have clean := (no_trap_checks s i trap).2.2.1
  simpa [v36, v35, v24, v23, v22, v27, v26, v28, v18, load] using clean

#print axioms no_trap_checks
#print axioms environment_pc_bit
#print axioms no_trap_word_load
#print axioms no_trap_word_store
end RiscvMiniProofs
