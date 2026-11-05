import Proofs.MemoryAddressWidth
namespace NutShellProofs
open nNutCore

/-- The WBU checker and EXU address latch sample the same selected address. -/
theorem committed_memory_address_is_latch (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1) :
    v30855 (step s i) next =
      (step s i).g44.r1432_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Faddr_5Freal := by
  have reset := (next_commit_controls s i next commit).1
  change v25578 s i = v14447 s i
  simp [v25578, commit_requires_capture s i next commit, v25577, v25576,
    v14447, v12103, v11455, reset, v14446, v14443, v14442, unit]

theorem memory_address_latch_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) :
    (step s i).g44.r1432_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Faddr_5Freal =
      if v12570 s i = 1 then ((0 : BitVec 25) ++ BitVec.extractLsb' 0 39 (v11612 s i))
      else s.g44.r1432_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Faddr_5Freal := by
  change v14447 s i = _
  simp [v14447, v12103, v11455, reset, v14446, v14443, v14442, unit,
    v14445, v14444, v13805, v12607, v12606, v12605, v12604]

theorem checker_memory_address_extension (s : State) (i : Inputs) :
    v31144 s i = (BitVec.extractLsb' 0 39 (v30855 s i)).signExtend 64 := by
  change ((if BitVec.extractLsb' 38 1 (BitVec.extractLsb' 0 39 (v30855 s i)) = 1
      then BitVec.allOnes 25 else 0) ++ BitVec.extractLsb' 0 39 (v30855 s i)) = _
  exact sign_extend_replication _ 25
#print axioms committed_memory_address_is_latch
#print axioms memory_address_latch_step
#print axioms checker_memory_address_extension
end NutShellProofs
