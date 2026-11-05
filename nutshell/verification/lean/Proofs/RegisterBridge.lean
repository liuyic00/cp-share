import Proofs.RegisterHold
namespace NutShellProofs
open nNutCore
theorem register_next_iff_1 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1) ↔
      (v31384 s i = v31385 s i) := by
  change (v11857 s i = v16711 s i) ↔ _
  simp only [v11857, v11456, v11455, v16711, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 12 s i ↔ ((step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1) := by
  rw [register_next_iff_1 s i reset]
  change (decide ((v31388 s i) ≠ 1 ∨ (v31386 s i) = 1) = true) ↔ _
  simp [v31388, v14558, v31387, v14554, v14553, v11455, v24, v31386, reset, commit]
theorem register_next_iff_2 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2) ↔
      (v31396 s i = v31397 s i) := by
  change (v11865 s i = v16955 s i) ↔ _
  simp only [v11865, v11456, v11455, v16955, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 13 s i ↔ ((step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2) := by
  rw [register_next_iff_2 s i reset]
  change (decide ((v31400 s i) ≠ 1 ∨ (v31398 s i) = 1) = true) ↔ _
  simp [v31400, v14558, v31399, v14554, v14553, v11455, v24, v31398, reset, commit]
theorem register_next_iff_3 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3) ↔
      (v31408 s i = v31409 s i) := by
  change (v11873 s i = v17199 s i) ↔ _
  simp only [v11873, v11456, v11455, v17199, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 14 s i ↔ ((step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3) := by
  rw [register_next_iff_3 s i reset]
  change (decide ((v31412 s i) ≠ 1 ∨ (v31410 s i) = 1) = true) ↔ _
  simp [v31412, v14558, v31411, v14554, v14553, v11455, v24, v31410, reset, commit]
theorem register_next_iff_4 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4) ↔
      (v31420 s i = v31421 s i) := by
  change (v11881 s i = v17443 s i) ↔ _
  simp only [v11881, v11456, v11455, v17443, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 15 s i ↔ ((step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4) := by
  rw [register_next_iff_4 s i reset]
  change (decide ((v31424 s i) ≠ 1 ∨ (v31422 s i) = 1) = true) ↔ _
  simp [v31424, v14558, v31423, v14554, v14553, v11455, v24, v31422, reset, commit]
theorem register_next_iff_5 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5) ↔
      (v31432 s i = v31433 s i) := by
  change (v11889 s i = v17687 s i) ↔ _
  simp only [v11889, v11456, v11455, v17687, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 16 s i ↔ ((step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5) := by
  rw [register_next_iff_5 s i reset]
  change (decide ((v31436 s i) ≠ 1 ∨ (v31434 s i) = 1) = true) ↔ _
  simp [v31436, v14558, v31435, v14554, v14553, v11455, v24, v31434, reset, commit]
theorem register_next_iff_6 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6) ↔
      (v31444 s i = v31445 s i) := by
  change (v11897 s i = v17931 s i) ↔ _
  simp only [v11897, v11456, v11455, v17931, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 17 s i ↔ ((step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6) := by
  rw [register_next_iff_6 s i reset]
  change (decide ((v31448 s i) ≠ 1 ∨ (v31446 s i) = 1) = true) ↔ _
  simp [v31448, v14558, v31447, v14554, v14553, v11455, v24, v31446, reset, commit]
theorem register_next_iff_7 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7) ↔
      (v31456 s i = v31457 s i) := by
  change (v11905 s i = v18175 s i) ↔ _
  simp only [v11905, v11456, v11455, v18175, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 18 s i ↔ ((step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7) := by
  rw [register_next_iff_7 s i reset]
  change (decide ((v31460 s i) ≠ 1 ∨ (v31458 s i) = 1) = true) ↔ _
  simp [v31460, v14558, v31459, v14554, v14553, v11455, v24, v31458, reset, commit]
theorem register_next_iff_8 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8) ↔
      (v31468 s i = v31469 s i) := by
  change (v11913 s i = v18419 s i) ↔ _
  simp only [v11913, v11456, v11455, v18419, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 19 s i ↔ ((step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8) := by
  rw [register_next_iff_8 s i reset]
  change (decide ((v31472 s i) ≠ 1 ∨ (v31470 s i) = 1) = true) ↔ _
  simp [v31472, v14558, v31471, v14554, v14553, v11455, v24, v31470, reset, commit]
theorem register_next_iff_9 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9) ↔
      (v31480 s i = v31481 s i) := by
  change (v11921 s i = v18663 s i) ↔ _
  simp only [v11921, v11456, v11455, v18663, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 20 s i ↔ ((step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9) := by
  rw [register_next_iff_9 s i reset]
  change (decide ((v31484 s i) ≠ 1 ∨ (v31482 s i) = 1) = true) ↔ _
  simp [v31484, v14558, v31483, v14554, v14553, v11455, v24, v31482, reset, commit]
theorem register_next_iff_10 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10) ↔
      (v31492 s i = v31493 s i) := by
  change (v11929 s i = v18907 s i) ↔ _
  simp only [v11929, v11456, v11455, v18907, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 21 s i ↔ ((step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10) := by
  rw [register_next_iff_10 s i reset]
  change (decide ((v31496 s i) ≠ 1 ∨ (v31494 s i) = 1) = true) ↔ _
  simp [v31496, v14558, v31495, v14554, v14553, v11455, v24, v31494, reset, commit]
theorem register_next_iff_11 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11) ↔
      (v31504 s i = v31505 s i) := by
  change (v11937 s i = v19151 s i) ↔ _
  simp only [v11937, v11456, v11455, v19151, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 22 s i ↔ ((step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11) := by
  rw [register_next_iff_11 s i reset]
  change (decide ((v31508 s i) ≠ 1 ∨ (v31506 s i) = 1) = true) ↔ _
  simp [v31508, v14558, v31507, v14554, v14553, v11455, v24, v31506, reset, commit]
theorem register_next_iff_12 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12) ↔
      (v31516 s i = v31517 s i) := by
  change (v11945 s i = v19395 s i) ↔ _
  simp only [v11945, v11456, v11455, v19395, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 23 s i ↔ ((step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12) := by
  rw [register_next_iff_12 s i reset]
  change (decide ((v31520 s i) ≠ 1 ∨ (v31518 s i) = 1) = true) ↔ _
  simp [v31520, v14558, v31519, v14554, v14553, v11455, v24, v31518, reset, commit]
theorem register_next_iff_13 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13) ↔
      (v31528 s i = v31529 s i) := by
  change (v11953 s i = v19639 s i) ↔ _
  simp only [v11953, v11456, v11455, v19639, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 24 s i ↔ ((step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13) := by
  rw [register_next_iff_13 s i reset]
  change (decide ((v31532 s i) ≠ 1 ∨ (v31530 s i) = 1) = true) ↔ _
  simp [v31532, v14558, v31531, v14554, v14553, v11455, v24, v31530, reset, commit]
theorem register_next_iff_14 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14) ↔
      (v31540 s i = v31541 s i) := by
  change (v11961 s i = v19883 s i) ↔ _
  simp only [v11961, v11456, v11455, v19883, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 25 s i ↔ ((step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14) := by
  rw [register_next_iff_14 s i reset]
  change (decide ((v31544 s i) ≠ 1 ∨ (v31542 s i) = 1) = true) ↔ _
  simp [v31544, v14558, v31543, v14554, v14553, v11455, v24, v31542, reset, commit]
theorem register_next_iff_15 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15) ↔
      (v31552 s i = v31553 s i) := by
  change (v11969 s i = v20127 s i) ↔ _
  simp only [v11969, v11456, v11455, v20127, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 26 s i ↔ ((step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15) := by
  rw [register_next_iff_15 s i reset]
  change (decide ((v31556 s i) ≠ 1 ∨ (v31554 s i) = 1) = true) ↔ _
  simp [v31556, v14558, v31555, v14554, v14553, v11455, v24, v31554, reset, commit]
theorem register_next_iff_16 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16) ↔
      (v31563 s i = v31564 s i) := by
  change (v11977 s i = v20313 s i) ↔ _
  simp only [v11977, v11456, v11455, v20313, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 27 s i ↔ ((step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16) := by
  rw [register_next_iff_16 s i reset]
  change (decide ((v31567 s i) ≠ 1 ∨ (v31565 s i) = 1) = true) ↔ _
  simp [v31567, v14558, v31566, v14554, v14553, v11455, v24, v31565, reset, commit]
theorem register_next_iff_17 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17) ↔
      (v31574 s i = v31575 s i) := by
  change (v11985 s i = v20499 s i) ↔ _
  simp only [v11985, v11456, v11455, v20499, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 28 s i ↔ ((step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17) := by
  rw [register_next_iff_17 s i reset]
  change (decide ((v31578 s i) ≠ 1 ∨ (v31576 s i) = 1) = true) ↔ _
  simp [v31578, v14558, v31577, v14554, v14553, v11455, v24, v31576, reset, commit]
theorem register_next_iff_18 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18) ↔
      (v31585 s i = v31586 s i) := by
  change (v11993 s i = v20685 s i) ↔ _
  simp only [v11993, v11456, v11455, v20685, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 29 s i ↔ ((step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18) := by
  rw [register_next_iff_18 s i reset]
  change (decide ((v31589 s i) ≠ 1 ∨ (v31587 s i) = 1) = true) ↔ _
  simp [v31589, v14558, v31588, v14554, v14553, v11455, v24, v31587, reset, commit]
theorem register_next_iff_19 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19) ↔
      (v31596 s i = v31597 s i) := by
  change (v12001 s i = v20871 s i) ↔ _
  simp only [v12001, v11456, v11455, v20871, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 30 s i ↔ ((step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19) := by
  rw [register_next_iff_19 s i reset]
  change (decide ((v31600 s i) ≠ 1 ∨ (v31598 s i) = 1) = true) ↔ _
  simp [v31600, v14558, v31599, v14554, v14553, v11455, v24, v31598, reset, commit]
theorem register_next_iff_20 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20) ↔
      (v31607 s i = v31608 s i) := by
  change (v12009 s i = v21057 s i) ↔ _
  simp only [v12009, v11456, v11455, v21057, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 31 s i ↔ ((step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20) := by
  rw [register_next_iff_20 s i reset]
  change (decide ((v31611 s i) ≠ 1 ∨ (v31609 s i) = 1) = true) ↔ _
  simp [v31611, v14558, v31610, v14554, v14553, v11455, v24, v31609, reset, commit]
theorem register_next_iff_21 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21) ↔
      (v31618 s i = v31619 s i) := by
  change (v12017 s i = v21243 s i) ↔ _
  simp only [v12017, v11456, v11455, v21243, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 32 s i ↔ ((step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21) := by
  rw [register_next_iff_21 s i reset]
  change (decide ((v31622 s i) ≠ 1 ∨ (v31620 s i) = 1) = true) ↔ _
  simp [v31622, v14558, v31621, v14554, v14553, v11455, v24, v31620, reset, commit]
theorem register_next_iff_22 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22) ↔
      (v31629 s i = v31630 s i) := by
  change (v12025 s i = v21429 s i) ↔ _
  simp only [v12025, v11456, v11455, v21429, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 33 s i ↔ ((step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22) := by
  rw [register_next_iff_22 s i reset]
  change (decide ((v31633 s i) ≠ 1 ∨ (v31631 s i) = 1) = true) ↔ _
  simp [v31633, v14558, v31632, v14554, v14553, v11455, v24, v31631, reset, commit]
theorem register_next_iff_23 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23) ↔
      (v31640 s i = v31641 s i) := by
  change (v12033 s i = v21615 s i) ↔ _
  simp only [v12033, v11456, v11455, v21615, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 34 s i ↔ ((step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23) := by
  rw [register_next_iff_23 s i reset]
  change (decide ((v31644 s i) ≠ 1 ∨ (v31642 s i) = 1) = true) ↔ _
  simp [v31644, v14558, v31643, v14554, v14553, v11455, v24, v31642, reset, commit]
theorem register_next_iff_24 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24) ↔
      (v31651 s i = v31652 s i) := by
  change (v12041 s i = v21801 s i) ↔ _
  simp only [v12041, v11456, v11455, v21801, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 35 s i ↔ ((step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24) := by
  rw [register_next_iff_24 s i reset]
  change (decide ((v31655 s i) ≠ 1 ∨ (v31653 s i) = 1) = true) ↔ _
  simp [v31655, v14558, v31654, v14554, v14553, v11455, v24, v31653, reset, commit]
theorem register_next_iff_25 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25) ↔
      (v31662 s i = v31663 s i) := by
  change (v12049 s i = v21987 s i) ↔ _
  simp only [v12049, v11456, v11455, v21987, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 36 s i ↔ ((step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25) := by
  rw [register_next_iff_25 s i reset]
  change (decide ((v31666 s i) ≠ 1 ∨ (v31664 s i) = 1) = true) ↔ _
  simp [v31666, v14558, v31665, v14554, v14553, v11455, v24, v31664, reset, commit]
theorem register_next_iff_26 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26) ↔
      (v31673 s i = v31674 s i) := by
  change (v12057 s i = v22173 s i) ↔ _
  simp only [v12057, v11456, v11455, v22173, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 37 s i ↔ ((step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26) := by
  rw [register_next_iff_26 s i reset]
  change (decide ((v31677 s i) ≠ 1 ∨ (v31675 s i) = 1) = true) ↔ _
  simp [v31677, v14558, v31676, v14554, v14553, v11455, v24, v31675, reset, commit]
theorem register_next_iff_27 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27) ↔
      (v31684 s i = v31685 s i) := by
  change (v12065 s i = v22359 s i) ↔ _
  simp only [v12065, v11456, v11455, v22359, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 38 s i ↔ ((step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27) := by
  rw [register_next_iff_27 s i reset]
  change (decide ((v31688 s i) ≠ 1 ∨ (v31686 s i) = 1) = true) ↔ _
  simp [v31688, v14558, v31687, v14554, v14553, v11455, v24, v31686, reset, commit]
theorem register_next_iff_28 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28) ↔
      (v31695 s i = v31696 s i) := by
  change (v12073 s i = v22545 s i) ↔ _
  simp only [v12073, v11456, v11455, v22545, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 39 s i ↔ ((step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28) := by
  rw [register_next_iff_28 s i reset]
  change (decide ((v31699 s i) ≠ 1 ∨ (v31697 s i) = 1) = true) ↔ _
  simp [v31699, v14558, v31698, v14554, v14553, v11455, v24, v31697, reset, commit]
theorem register_next_iff_29 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29) ↔
      (v31706 s i = v31707 s i) := by
  change (v12081 s i = v22731 s i) ↔ _
  simp only [v12081, v11456, v11455, v22731, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 40 s i ↔ ((step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29) := by
  rw [register_next_iff_29 s i reset]
  change (decide ((v31710 s i) ≠ 1 ∨ (v31708 s i) = 1) = true) ↔ _
  simp [v31710, v14558, v31709, v14554, v14553, v11455, v24, v31708, reset, commit]
theorem register_next_iff_30 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30) ↔
      (v31717 s i = v31718 s i) := by
  change (v12089 s i = v22917 s i) ↔ _
  simp only [v12089, v11456, v11455, v22917, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 41 s i ↔ ((step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30) := by
  rw [register_next_iff_30 s i reset]
  change (decide ((v31721 s i) ≠ 1 ∨ (v31719 s i) = 1) = true) ↔ _
  simp [v31721, v14558, v31720, v14554, v14553, v11455, v24, v31719, reset, commit]
theorem register_next_iff_31 (s : State) (i : Inputs) (h : i.g0.nreset = 0) :
    ((step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31) ↔
      (v31728 s i = v31729 s i) := by
  change (v12097 s i = v23103 s i) ↔ _
  simp only [v12097, v11456, v11455, v23103, v14555, v14554, v14553, h]
  rfl
theorem register_task_next_iff_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    TaskHolds 42 s i ↔ ((step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31) := by
  rw [register_next_iff_31 s i reset]
  change (decide ((v31732 s i) ≠ 1 ∨ (v31730 s i) = 1) = true) ↔ _
  simp [v31732, v14558, v31731, v14554, v14553, v11455, v24, v31730, reset, commit]
def RegisterTasks (s : State) (i : Inputs) : Prop :=
  TaskHolds 12 s i ∧
  TaskHolds 13 s i ∧
  TaskHolds 14 s i ∧
  TaskHolds 15 s i ∧
  TaskHolds 16 s i ∧
  TaskHolds 17 s i ∧
  TaskHolds 18 s i ∧
  TaskHolds 19 s i ∧
  TaskHolds 20 s i ∧
  TaskHolds 21 s i ∧
  TaskHolds 22 s i ∧
  TaskHolds 23 s i ∧
  TaskHolds 24 s i ∧
  TaskHolds 25 s i ∧
  TaskHolds 26 s i ∧
  TaskHolds 27 s i ∧
  TaskHolds 28 s i ∧
  TaskHolds 29 s i ∧
  TaskHolds 30 s i ∧
  TaskHolds 31 s i ∧
  TaskHolds 32 s i ∧
  TaskHolds 33 s i ∧
  TaskHolds 34 s i ∧
  TaskHolds 35 s i ∧
  TaskHolds 36 s i ∧
  TaskHolds 37 s i ∧
  TaskHolds 38 s i ∧
  TaskHolds 39 s i ∧
  TaskHolds 40 s i ∧
  TaskHolds 41 s i ∧
  TaskHolds 42 s i
theorem register_commit_iff (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) :
    RegisterTasks s i ↔ ArchitecturalRegistersAligned (step s i) := by
  simp only [RegisterTasks, ArchitecturalRegistersAligned, register_task_next_iff_1 s i reset commit, register_task_next_iff_2 s i reset commit, register_task_next_iff_3 s i reset commit, register_task_next_iff_4 s i reset commit, register_task_next_iff_5 s i reset commit, register_task_next_iff_6 s i reset commit, register_task_next_iff_7 s i reset commit, register_task_next_iff_8 s i reset commit, register_task_next_iff_9 s i reset commit, register_task_next_iff_10 s i reset commit, register_task_next_iff_11 s i reset commit, register_task_next_iff_12 s i reset commit, register_task_next_iff_13 s i reset commit, register_task_next_iff_14 s i reset commit, register_task_next_iff_15 s i reset commit, register_task_next_iff_16 s i reset commit, register_task_next_iff_17 s i reset commit, register_task_next_iff_18 s i reset commit, register_task_next_iff_19 s i reset commit, register_task_next_iff_20 s i reset commit, register_task_next_iff_21 s i reset commit, register_task_next_iff_22 s i reset commit, register_task_next_iff_23 s i reset commit, register_task_next_iff_24 s i reset commit, register_task_next_iff_25 s i reset commit, register_task_next_iff_26 s i reset commit, register_task_next_iff_27 s i reset commit, register_task_next_iff_28 s i reset commit, register_task_next_iff_29 s i reset commit, register_task_next_iff_30 s i reset commit, register_task_next_iff_31 s i reset commit]
#print axioms register_commit_iff
end NutShellProofs
