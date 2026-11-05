import Proofs.LoadResponseCapture
import Proofs.WritebackSelection
namespace NutShellProofs
open nNutCore

/-- The checker data register captures the full response word, before byte selection. -/
theorem checker_load_data_latch_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) :
    (step s i).g44.r1435_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frdata =
      if v11661 s i = 1 then v12306 s i
      else s.g44.r1435_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frdata := by
  change v14495 s i = _
  simp [v14495, v12103, v11455, reset, v14494, v14443, v14442, unit,
    v14493, v11661, v11660, v12306, v12305]

theorem reference_load_data_capture (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1) :
    v16181 (step s i) next =
      (step s i).g44.r1435_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frdata := by
  rw [checker_load_data_latch_step s i (next_commit_controls s i next commit).1 unit]
  change v25597 s i = _
  simp [v25597, commit_requires_capture s i next commit, v25596, v25595,
    v14443, v14442, unit, v14493, v11661, v11660, v12306, v12305]

theorem response_captures_same_load_data (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1) (response : v11661 s i = 1) :
    (step s i).g44.r1435_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frdata =
      (step s i).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch := by
  rw [checker_load_data_latch_step s i reset unit, if_pos response, load_data_latch_step]

/-- Full-width completion can use the current response directly. -/
theorem committed_response_reference_data (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (response : v11661 s i = 1) : v16181 (step s i) next = v12306 s i := by
  rw [reference_load_data_capture s i next commit unit,
    checker_load_data_latch_step s i (next_commit_controls s i next commit).1 unit,
    if_pos response]
#print axioms reference_load_data_capture
#print axioms response_captures_same_load_data
#print axioms committed_response_reference_data
end NutShellProofs
