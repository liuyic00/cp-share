import Proofs.ReferenceStoreData
import Proofs.MemoryCompletedMasks
namespace NutShellProofs
open nNutCore

theorem store_data_latch_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) :
    (step s i).g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata =
      if v12570 s i = 1 then v14539 s i
      else s.g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata := by
  change v14542 s i = _
  simp [v14542, v12103, v11455, reset, v14541, v14443, v14442, unit, v14540]

theorem committed_store_data_is_latch (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1) :
    v30873 (step s i) next =
      (step s i).g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata := by
  rw [store_data_latch_step s i (next_commit_controls s i next commit).1 unit]
  change v25600 s i = _
  simp [v25600, commit_requires_capture s i next commit, v25599, v25598,
    v14443, v14442, unit, v14540]

#print axioms store_data_latch_step
#print axioms committed_store_data_is_latch
end NutShellProofs
