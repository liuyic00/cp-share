import Proofs.ReferencePCAdvance
import Proofs.ReferenceBranchSelection
namespace NutShellProofs
open nNutCore

theorem reference_pc_update_normal (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (notMret : v14595 s i = 0) (notSret : v14601 s i = 0) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23529 s i = 0 then v16457 s i + 4 else v23620 s i := by
  change v23683 s i = _
  simp only [v23683, v14555, v14554, v14553, v11455, reset, v23682, v23681,
    v23680, v14560, v14559, v14558, commit, v23678, noException, v23677,
    v23626, v23625, notMret, v23623, notSret, ↓reduceIte,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self, reference_pc_advance_gate s i commit noException,
    reference_pc_plus_four]
  by_cases h : v23529 s i = 0 <;> simp [h, BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]

#print axioms reference_pc_update_normal


theorem reference_branch_beq_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 99)
    (aligned : v23335 s i = 1 → v23358 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23335 s i = 1 then v23588 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_beq_not_v14595 s i matched)
    (reference_branch_beq_not_v14601 s i matched),
    reference_branch_beq_redirect s i matched aligned,
    reference_branch_beq_selection s i matched aligned]
  by_cases taken : v23335 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_beq_pc_update

theorem reference_branch_bne_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 4195)
    (aligned : v23311 s i = 1 → v23334 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23311 s i = 1 then v23584 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_bne_not_v14595 s i matched)
    (reference_branch_bne_not_v14601 s i matched),
    reference_branch_bne_redirect s i matched aligned,
    reference_branch_bne_selection s i matched aligned]
  by_cases taken : v23311 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_bne_pc_update

theorem reference_branch_blt_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 16483)
    (aligned : v23287 s i = 1 → v23310 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23287 s i = 1 then v23580 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_blt_not_v14595 s i matched)
    (reference_branch_blt_not_v14601 s i matched),
    reference_branch_blt_redirect s i matched aligned,
    reference_branch_blt_selection s i matched aligned]
  by_cases taken : v23287 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_blt_pc_update

theorem reference_branch_bge_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 20579)
    (aligned : v23239 s i = 1 → v23262 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23239 s i = 1 then v23572 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_bge_not_v14595 s i matched)
    (reference_branch_bge_not_v14601 s i matched),
    reference_branch_bge_redirect s i matched aligned,
    reference_branch_bge_selection s i matched aligned]
  by_cases taken : v23239 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_bge_pc_update

theorem reference_branch_bltu_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 24675)
    (aligned : v23263 s i = 1 → v23286 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23263 s i = 1 then v23576 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_bltu_not_v14595 s i matched)
    (reference_branch_bltu_not_v14601 s i matched),
    reference_branch_bltu_redirect s i matched aligned,
    reference_branch_bltu_selection s i matched aligned]
  by_cases taken : v23263 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_bltu_pc_update

theorem reference_branch_bgeu_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (noException : v23407 s i = 0)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 28771)
    (aligned : v23215 s i = 1 → v23238 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v23215 s i = 1 then v23568 s i else v16457 s i + 4 := by
  rw [reference_pc_update_normal s i reset commit noException
    (reference_branch_bgeu_not_v14595 s i matched)
    (reference_branch_bgeu_not_v14601 s i matched),
    reference_branch_bgeu_redirect s i matched aligned,
    reference_branch_bgeu_selection s i matched aligned]
  by_cases taken : v23215 s i = 1 <;> simp [taken]
  split <;> simp_all only [↓reduceIte]
#print axioms reference_branch_bgeu_pc_update
end NutShellProofs
