import Proofs.Contract
namespace NutShellProofs
open nNutCore
theorem register_reset_1 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  change v11857 s i = v16711 s i
  simp [v11857, v11456, v11455, v11851, v11850, v16711, v14555, v14554, v14553, v14567, v14566, h]
theorem register_reset_2 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  change v11865 s i = v16955 s i
  simp [v11865, v11456, v11455, v11859, v11858, v16955, v14555, v14554, v14553, v16713, v16712, h]
theorem register_reset_3 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  change v11873 s i = v17199 s i
  simp [v11873, v11456, v11455, v11867, v11866, v17199, v14555, v14554, v14553, v16957, v16956, h]
theorem register_reset_4 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  change v11881 s i = v17443 s i
  simp [v11881, v11456, v11455, v11875, v11874, v17443, v14555, v14554, v14553, v17201, v17200, h]
theorem register_reset_5 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  change v11889 s i = v17687 s i
  simp [v11889, v11456, v11455, v11883, v11882, v17687, v14555, v14554, v14553, v17445, v17444, h]
theorem register_reset_6 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  change v11897 s i = v17931 s i
  simp [v11897, v11456, v11455, v11891, v11890, v17931, v14555, v14554, v14553, v17689, v17688, h]
theorem register_reset_7 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  change v11905 s i = v18175 s i
  simp [v11905, v11456, v11455, v11899, v11898, v18175, v14555, v14554, v14553, v17933, v17932, h]
theorem register_reset_8 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  change v11913 s i = v18419 s i
  simp [v11913, v11456, v11455, v11907, v11906, v18419, v14555, v14554, v14553, v18177, v18176, h]
theorem register_reset_9 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  change v11921 s i = v18663 s i
  simp [v11921, v11456, v11455, v11915, v11914, v18663, v14555, v14554, v14553, v18421, v18420, h]
theorem register_reset_10 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  change v11929 s i = v18907 s i
  simp [v11929, v11456, v11455, v11923, v11922, v18907, v14555, v14554, v14553, v18665, v18664, h]
theorem register_reset_11 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  change v11937 s i = v19151 s i
  simp [v11937, v11456, v11455, v11931, v11930, v19151, v14555, v14554, v14553, v18909, v18908, h]
theorem register_reset_12 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  change v11945 s i = v19395 s i
  simp [v11945, v11456, v11455, v11939, v11938, v19395, v14555, v14554, v14553, v19153, v19152, h]
theorem register_reset_13 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  change v11953 s i = v19639 s i
  simp [v11953, v11456, v11455, v11947, v11946, v19639, v14555, v14554, v14553, v19397, v19396, h]
theorem register_reset_14 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  change v11961 s i = v19883 s i
  simp [v11961, v11456, v11455, v11955, v11954, v19883, v14555, v14554, v14553, v19641, v19640, h]
theorem register_reset_15 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  change v11969 s i = v20127 s i
  simp [v11969, v11456, v11455, v11963, v11962, v20127, v14555, v14554, v14553, v19885, v19884, h]
theorem register_reset_16 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  change v11977 s i = v20313 s i
  simp [v11977, v11456, v11455, v11971, v11970, v20313, v14555, v14554, v14553, v20129, v20128, h]
theorem register_reset_17 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  change v11985 s i = v20499 s i
  simp [v11985, v11456, v11455, v11979, v11978, v20499, v14555, v14554, v14553, v20315, v20314, h]
theorem register_reset_18 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  change v11993 s i = v20685 s i
  simp [v11993, v11456, v11455, v11987, v11986, v20685, v14555, v14554, v14553, v20501, v20500, h]
theorem register_reset_19 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  change v12001 s i = v20871 s i
  simp [v12001, v11456, v11455, v11995, v11994, v20871, v14555, v14554, v14553, v20687, v20686, h]
theorem register_reset_20 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  change v12009 s i = v21057 s i
  simp [v12009, v11456, v11455, v12003, v12002, v21057, v14555, v14554, v14553, v20873, v20872, h]
theorem register_reset_21 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  change v12017 s i = v21243 s i
  simp [v12017, v11456, v11455, v12011, v12010, v21243, v14555, v14554, v14553, v21059, v21058, h]
theorem register_reset_22 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  change v12025 s i = v21429 s i
  simp [v12025, v11456, v11455, v12019, v12018, v21429, v14555, v14554, v14553, v21245, v21244, h]
theorem register_reset_23 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  change v12033 s i = v21615 s i
  simp [v12033, v11456, v11455, v12027, v12026, v21615, v14555, v14554, v14553, v21431, v21430, h]
theorem register_reset_24 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  change v12041 s i = v21801 s i
  simp [v12041, v11456, v11455, v12035, v12034, v21801, v14555, v14554, v14553, v21617, v21616, h]
theorem register_reset_25 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  change v12049 s i = v21987 s i
  simp [v12049, v11456, v11455, v12043, v12042, v21987, v14555, v14554, v14553, v21803, v21802, h]
theorem register_reset_26 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  change v12057 s i = v22173 s i
  simp [v12057, v11456, v11455, v12051, v12050, v22173, v14555, v14554, v14553, v21989, v21988, h]
theorem register_reset_27 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  change v12065 s i = v22359 s i
  simp [v12065, v11456, v11455, v12059, v12058, v22359, v14555, v14554, v14553, v22175, v22174, h]
theorem register_reset_28 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  change v12073 s i = v22545 s i
  simp [v12073, v11456, v11455, v12067, v12066, v22545, v14555, v14554, v14553, v22361, v22360, h]
theorem register_reset_29 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  change v12081 s i = v22731 s i
  simp [v12081, v11456, v11455, v12075, v12074, v22731, v14555, v14554, v14553, v22547, v22546, h]
theorem register_reset_30 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  change v12089 s i = v22917 s i
  simp [v12089, v11456, v11455, v12083, v12082, v22917, v14555, v14554, v14553, v22733, v22732, h]
theorem register_reset_31 (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  change v12097 s i = v23103 s i
  simp [v12097, v11456, v11455, v12091, v12090, v23103, v14555, v14554, v14553, v22919, v22918, h]
def ArchitecturalRegistersAligned (s : State) : Prop :=
  s.g40.r1287_nbackend_5Fisu_5Frf_5F1 = s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 ∧
  s.g40.r1288_nbackend_5Fisu_5Frf_5F2 = s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 ∧
  s.g40.r1289_nbackend_5Fisu_5Frf_5F3 = s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 ∧
  s.g40.r1290_nbackend_5Fisu_5Frf_5F4 = s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 ∧
  s.g40.r1291_nbackend_5Fisu_5Frf_5F5 = s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 ∧
  s.g40.r1292_nbackend_5Fisu_5Frf_5F6 = s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 ∧
  s.g40.r1293_nbackend_5Fisu_5Frf_5F7 = s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 ∧
  s.g40.r1294_nbackend_5Fisu_5Frf_5F8 = s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 ∧
  s.g40.r1295_nbackend_5Fisu_5Frf_5F9 = s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 ∧
  s.g40.r1296_nbackend_5Fisu_5Frf_5F10 = s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 ∧
  s.g40.r1297_nbackend_5Fisu_5Frf_5F11 = s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 ∧
  s.g40.r1298_nbackend_5Fisu_5Frf_5F12 = s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 ∧
  s.g40.r1299_nbackend_5Fisu_5Frf_5F13 = s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 ∧
  s.g40.r1300_nbackend_5Fisu_5Frf_5F14 = s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 ∧
  s.g40.r1301_nbackend_5Fisu_5Frf_5F15 = s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 ∧
  s.g40.r1302_nbackend_5Fisu_5Frf_5F16 = s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 ∧
  s.g40.r1303_nbackend_5Fisu_5Frf_5F17 = s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 ∧
  s.g40.r1304_nbackend_5Fisu_5Frf_5F18 = s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 ∧
  s.g40.r1305_nbackend_5Fisu_5Frf_5F19 = s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 ∧
  s.g40.r1306_nbackend_5Fisu_5Frf_5F20 = s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 ∧
  s.g40.r1307_nbackend_5Fisu_5Frf_5F21 = s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 ∧
  s.g40.r1308_nbackend_5Fisu_5Frf_5F22 = s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 ∧
  s.g40.r1309_nbackend_5Fisu_5Frf_5F23 = s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 ∧
  s.g40.r1310_nbackend_5Fisu_5Frf_5F24 = s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 ∧
  s.g40.r1311_nbackend_5Fisu_5Frf_5F25 = s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 ∧
  s.g41.r1312_nbackend_5Fisu_5Frf_5F26 = s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 ∧
  s.g41.r1313_nbackend_5Fisu_5Frf_5F27 = s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 ∧
  s.g41.r1314_nbackend_5Fisu_5Frf_5F28 = s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 ∧
  s.g41.r1315_nbackend_5Fisu_5Frf_5F29 = s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 ∧
  s.g41.r1316_nbackend_5Fisu_5Frf_5F30 = s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 ∧
  s.g41.r1317_nbackend_5Fisu_5Frf_5F31 = s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31
theorem registers_aligned_after_reset (s : State) (i : Inputs) (h : i.g0.nreset = 1) :
    ArchitecturalRegistersAligned (step s i) := by
  exact ⟨register_reset_1 s i h, register_reset_2 s i h, register_reset_3 s i h, register_reset_4 s i h, register_reset_5 s i h, register_reset_6 s i h, register_reset_7 s i h, register_reset_8 s i h, register_reset_9 s i h, register_reset_10 s i h, register_reset_11 s i h, register_reset_12 s i h, register_reset_13 s i h, register_reset_14 s i h, register_reset_15 s i h, register_reset_16 s i h, register_reset_17 s i h, register_reset_18 s i h, register_reset_19 s i h, register_reset_20 s i h, register_reset_21 s i h, register_reset_22 s i h, register_reset_23 s i h, register_reset_24 s i h, register_reset_25 s i h, register_reset_26 s i h, register_reset_27 s i h, register_reset_28 s i h, register_reset_29 s i h, register_reset_30 s i h, register_reset_31 s i h⟩
#print axioms registers_aligned_after_reset
end NutShellProofs
