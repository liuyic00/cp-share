import Proofs.RegisterFrame
namespace NutShellProofs
open nNutCore
theorem commit_requires_capture (s : State) (i next : Inputs)
    (h : v9 (step s i) next = 1) : v25332 s i = 1 := by
  change v25331 s i = 1 at h
  unfold v25331 at h
  split at h
  · simp [v24] at h
  · unfold v25330 at h
    split at h
    · simp [v24] at h
    · exact h

theorem capture_decode_cf_instr (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g49.r1568_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Finstr = v25333 s i := by
  change v25334 s i = v25333 s i
  simp only [v25334, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_cf_pc (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g49.r1569_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fpc = v25335 s i := by
  change v25336 s i = v25335 s i
  simp only [v25336, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_fuType (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = v25461 s i := by
  change v25462 s i = v25461 s i
  simp only [v25462, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_fuOpType (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1610_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuOpType = v25463 s i := by
  change v25464 s i = v25463 s i
  simp only [v25464, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_rfWen (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1613_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FrfWen = v25485 s i := by
  change v25486 s i = v25485 s i
  simp only [v25486, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_rfDest (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1614_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FrfDest = v25487 s i := by
  change v25488 s i = v25487 s i
  simp only [v25488, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_rfSrc1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1611_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FrfSrc1 = v25466 s i := by
  change v25467 s i = v25466 s i
  simp only [v25467, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_ctrl_rfSrc2 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1612_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FrfSrc2 = v25469 s i := by
  change v25470 s i = v25469 s i
  simp only [v25470, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_data_src1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 = v25503 s i := by
  change v25504 s i = v25503 s i
  simp only [v25504, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_decode_data_src2 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 = v25509 s i := by
  change v25510 s i = v25509 s i
  simp only [v25510, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_commits_0 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1625_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fcommits_5F0 = v25535 s i := by
  change v25536 s i = v25535 s i
  simp only [v25536, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_commits_1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1626_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fcommits_5F1 = v25537 s i := by
  change v25538 s i = v25537 s i
  simp only [v25538, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_commits_2 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1627_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fcommits_5F2 = v25569 s i := by
  change v25570 s i = v25569 s i
  simp only [v25570, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_commits_3 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1628_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fcommits_5F3 = v25572 s i := by
  change v25573 s i = v25572 s i
  simp only [v25573, commit_requires_capture s i next commit, ↓reduceIte]
theorem capture_commits_4 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (step s i).g50.r1629_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fcommits_5F4 = v25574 s i := by
  change v25575 s i = v25574 s i
  simp only [v25575, commit_requires_capture s i next commit, ↓reduceIte]
#print axioms commit_requires_capture
#print axioms capture_commits_0
end NutShellProofs
