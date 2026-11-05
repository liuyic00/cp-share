import Proofs.RegisterReset
namespace NutShellProofs
open nNutCore
theorem dut_register_hold_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = s.g40.r1287_nbackend_5Fisu_5Frf_5F1 := by
  change v11857 s i = s.g40.r1287_nbackend_5Fisu_5Frf_5F1
  simp [v11857, v11456, v11455, v11856, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  change v16711 s i = s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1
  simp [v16711, v14555, v14554, v14553, v11455, v16710, v16709, v14560, v14559, v14558, v15359, reset, idle]
theorem dut_register_hold_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = s.g40.r1288_nbackend_5Fisu_5Frf_5F2 := by
  change v11865 s i = s.g40.r1288_nbackend_5Fisu_5Frf_5F2
  simp [v11865, v11456, v11455, v11864, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  change v16955 s i = s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2
  simp [v16955, v14555, v14554, v14553, v11455, v16954, v16953, v14560, v14559, v14558, v15356, reset, idle]
theorem dut_register_hold_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = s.g40.r1289_nbackend_5Fisu_5Frf_5F3 := by
  change v11873 s i = s.g40.r1289_nbackend_5Fisu_5Frf_5F3
  simp [v11873, v11456, v11455, v11872, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  change v17199 s i = s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3
  simp [v17199, v14555, v14554, v14553, v11455, v17198, v17197, v14560, v14559, v14558, v15353, reset, idle]
theorem dut_register_hold_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = s.g40.r1290_nbackend_5Fisu_5Frf_5F4 := by
  change v11881 s i = s.g40.r1290_nbackend_5Fisu_5Frf_5F4
  simp [v11881, v11456, v11455, v11880, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  change v17443 s i = s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4
  simp [v17443, v14555, v14554, v14553, v11455, v17442, v17441, v14560, v14559, v14558, v15350, reset, idle]
theorem dut_register_hold_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = s.g40.r1291_nbackend_5Fisu_5Frf_5F5 := by
  change v11889 s i = s.g40.r1291_nbackend_5Fisu_5Frf_5F5
  simp [v11889, v11456, v11455, v11888, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  change v17687 s i = s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5
  simp [v17687, v14555, v14554, v14553, v11455, v17686, v17685, v14560, v14559, v14558, v15347, reset, idle]
theorem dut_register_hold_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = s.g40.r1292_nbackend_5Fisu_5Frf_5F6 := by
  change v11897 s i = s.g40.r1292_nbackend_5Fisu_5Frf_5F6
  simp [v11897, v11456, v11455, v11896, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  change v17931 s i = s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6
  simp [v17931, v14555, v14554, v14553, v11455, v17930, v17929, v14560, v14559, v14558, v15344, reset, idle]
theorem dut_register_hold_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = s.g40.r1293_nbackend_5Fisu_5Frf_5F7 := by
  change v11905 s i = s.g40.r1293_nbackend_5Fisu_5Frf_5F7
  simp [v11905, v11456, v11455, v11904, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  change v18175 s i = s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7
  simp [v18175, v14555, v14554, v14553, v11455, v18174, v18173, v14560, v14559, v14558, v15341, reset, idle]
theorem dut_register_hold_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = s.g40.r1294_nbackend_5Fisu_5Frf_5F8 := by
  change v11913 s i = s.g40.r1294_nbackend_5Fisu_5Frf_5F8
  simp [v11913, v11456, v11455, v11912, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  change v18419 s i = s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8
  simp [v18419, v14555, v14554, v14553, v11455, v18418, v18417, v14560, v14559, v14558, v15338, reset, idle]
theorem dut_register_hold_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = s.g40.r1295_nbackend_5Fisu_5Frf_5F9 := by
  change v11921 s i = s.g40.r1295_nbackend_5Fisu_5Frf_5F9
  simp [v11921, v11456, v11455, v11920, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  change v18663 s i = s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9
  simp [v18663, v14555, v14554, v14553, v11455, v18662, v18661, v14560, v14559, v14558, v15335, reset, idle]
theorem dut_register_hold_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = s.g40.r1296_nbackend_5Fisu_5Frf_5F10 := by
  change v11929 s i = s.g40.r1296_nbackend_5Fisu_5Frf_5F10
  simp [v11929, v11456, v11455, v11928, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  change v18907 s i = s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10
  simp [v18907, v14555, v14554, v14553, v11455, v18906, v18905, v14560, v14559, v14558, v15332, reset, idle]
theorem dut_register_hold_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = s.g40.r1297_nbackend_5Fisu_5Frf_5F11 := by
  change v11937 s i = s.g40.r1297_nbackend_5Fisu_5Frf_5F11
  simp [v11937, v11456, v11455, v11936, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  change v19151 s i = s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11
  simp [v19151, v14555, v14554, v14553, v11455, v19150, v19149, v14560, v14559, v14558, v15329, reset, idle]
theorem dut_register_hold_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = s.g40.r1298_nbackend_5Fisu_5Frf_5F12 := by
  change v11945 s i = s.g40.r1298_nbackend_5Fisu_5Frf_5F12
  simp [v11945, v11456, v11455, v11944, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  change v19395 s i = s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12
  simp [v19395, v14555, v14554, v14553, v11455, v19394, v19393, v14560, v14559, v14558, v15326, reset, idle]
theorem dut_register_hold_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = s.g40.r1299_nbackend_5Fisu_5Frf_5F13 := by
  change v11953 s i = s.g40.r1299_nbackend_5Fisu_5Frf_5F13
  simp [v11953, v11456, v11455, v11952, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  change v19639 s i = s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13
  simp [v19639, v14555, v14554, v14553, v11455, v19638, v19637, v14560, v14559, v14558, v15323, reset, idle]
theorem dut_register_hold_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = s.g40.r1300_nbackend_5Fisu_5Frf_5F14 := by
  change v11961 s i = s.g40.r1300_nbackend_5Fisu_5Frf_5F14
  simp [v11961, v11456, v11455, v11960, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  change v19883 s i = s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14
  simp [v19883, v14555, v14554, v14553, v11455, v19882, v19881, v14560, v14559, v14558, v15320, reset, idle]
theorem dut_register_hold_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = s.g40.r1301_nbackend_5Fisu_5Frf_5F15 := by
  change v11969 s i = s.g40.r1301_nbackend_5Fisu_5Frf_5F15
  simp [v11969, v11456, v11455, v11968, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  change v20127 s i = s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15
  simp [v20127, v14555, v14554, v14553, v11455, v20126, v20125, v14560, v14559, v14558, v15317, reset, idle]
theorem dut_register_hold_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = s.g40.r1302_nbackend_5Fisu_5Frf_5F16 := by
  change v11977 s i = s.g40.r1302_nbackend_5Fisu_5Frf_5F16
  simp [v11977, v11456, v11455, v11976, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  change v20313 s i = s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16
  simp [v20313, v14555, v14554, v14553, v11455, v20312, v20311, v14560, v14559, v14558, v15314, reset, idle]
theorem dut_register_hold_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = s.g40.r1303_nbackend_5Fisu_5Frf_5F17 := by
  change v11985 s i = s.g40.r1303_nbackend_5Fisu_5Frf_5F17
  simp [v11985, v11456, v11455, v11984, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  change v20499 s i = s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17
  simp [v20499, v14555, v14554, v14553, v11455, v20498, v20497, v14560, v14559, v14558, v15312, reset, idle]
theorem dut_register_hold_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = s.g40.r1304_nbackend_5Fisu_5Frf_5F18 := by
  change v11993 s i = s.g40.r1304_nbackend_5Fisu_5Frf_5F18
  simp [v11993, v11456, v11455, v11992, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  change v20685 s i = s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18
  simp [v20685, v14555, v14554, v14553, v11455, v20684, v20683, v14560, v14559, v14558, v15310, reset, idle]
theorem dut_register_hold_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = s.g40.r1305_nbackend_5Fisu_5Frf_5F19 := by
  change v12001 s i = s.g40.r1305_nbackend_5Fisu_5Frf_5F19
  simp [v12001, v11456, v11455, v12000, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  change v20871 s i = s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19
  simp [v20871, v14555, v14554, v14553, v11455, v20870, v20869, v14560, v14559, v14558, v15308, reset, idle]
theorem dut_register_hold_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = s.g40.r1306_nbackend_5Fisu_5Frf_5F20 := by
  change v12009 s i = s.g40.r1306_nbackend_5Fisu_5Frf_5F20
  simp [v12009, v11456, v11455, v12008, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  change v21057 s i = s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20
  simp [v21057, v14555, v14554, v14553, v11455, v21056, v21055, v14560, v14559, v14558, v15306, reset, idle]
theorem dut_register_hold_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = s.g40.r1307_nbackend_5Fisu_5Frf_5F21 := by
  change v12017 s i = s.g40.r1307_nbackend_5Fisu_5Frf_5F21
  simp [v12017, v11456, v11455, v12016, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  change v21243 s i = s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21
  simp [v21243, v14555, v14554, v14553, v11455, v21242, v21241, v14560, v14559, v14558, v15304, reset, idle]
theorem dut_register_hold_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = s.g40.r1308_nbackend_5Fisu_5Frf_5F22 := by
  change v12025 s i = s.g40.r1308_nbackend_5Fisu_5Frf_5F22
  simp [v12025, v11456, v11455, v12024, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  change v21429 s i = s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22
  simp [v21429, v14555, v14554, v14553, v11455, v21428, v21427, v14560, v14559, v14558, v15302, reset, idle]
theorem dut_register_hold_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = s.g40.r1309_nbackend_5Fisu_5Frf_5F23 := by
  change v12033 s i = s.g40.r1309_nbackend_5Fisu_5Frf_5F23
  simp [v12033, v11456, v11455, v12032, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  change v21615 s i = s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23
  simp [v21615, v14555, v14554, v14553, v11455, v21614, v21613, v14560, v14559, v14558, v15300, reset, idle]
theorem dut_register_hold_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = s.g40.r1310_nbackend_5Fisu_5Frf_5F24 := by
  change v12041 s i = s.g40.r1310_nbackend_5Fisu_5Frf_5F24
  simp [v12041, v11456, v11455, v12040, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  change v21801 s i = s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24
  simp [v21801, v14555, v14554, v14553, v11455, v21800, v21799, v14560, v14559, v14558, v15298, reset, idle]
theorem dut_register_hold_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = s.g40.r1311_nbackend_5Fisu_5Frf_5F25 := by
  change v12049 s i = s.g40.r1311_nbackend_5Fisu_5Frf_5F25
  simp [v12049, v11456, v11455, v12048, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  change v21987 s i = s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25
  simp [v21987, v14555, v14554, v14553, v11455, v21986, v21985, v14560, v14559, v14558, v15296, reset, idle]
theorem dut_register_hold_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = s.g41.r1312_nbackend_5Fisu_5Frf_5F26 := by
  change v12057 s i = s.g41.r1312_nbackend_5Fisu_5Frf_5F26
  simp [v12057, v11456, v11455, v12056, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  change v22173 s i = s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26
  simp [v22173, v14555, v14554, v14553, v11455, v22172, v22171, v14560, v14559, v14558, v15294, reset, idle]
theorem dut_register_hold_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = s.g41.r1313_nbackend_5Fisu_5Frf_5F27 := by
  change v12065 s i = s.g41.r1313_nbackend_5Fisu_5Frf_5F27
  simp [v12065, v11456, v11455, v12064, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  change v22359 s i = s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27
  simp [v22359, v14555, v14554, v14553, v11455, v22358, v22357, v14560, v14559, v14558, v15292, reset, idle]
theorem dut_register_hold_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = s.g41.r1314_nbackend_5Fisu_5Frf_5F28 := by
  change v12073 s i = s.g41.r1314_nbackend_5Fisu_5Frf_5F28
  simp [v12073, v11456, v11455, v12072, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  change v22545 s i = s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28
  simp [v22545, v14555, v14554, v14553, v11455, v22544, v22543, v14560, v14559, v14558, v15290, reset, idle]
theorem dut_register_hold_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = s.g41.r1315_nbackend_5Fisu_5Frf_5F29 := by
  change v12081 s i = s.g41.r1315_nbackend_5Fisu_5Frf_5F29
  simp [v12081, v11456, v11455, v12080, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  change v22731 s i = s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29
  simp [v22731, v14555, v14554, v14553, v11455, v22730, v22729, v14560, v14559, v14558, v15288, reset, idle]
theorem dut_register_hold_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = s.g41.r1316_nbackend_5Fisu_5Frf_5F30 := by
  change v12089 s i = s.g41.r1316_nbackend_5Fisu_5Frf_5F30
  simp [v12089, v11456, v11455, v12088, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  change v22917 s i = s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30
  simp [v22917, v14555, v14554, v14553, v11455, v22916, v22915, v14560, v14559, v14558, v15286, reset, idle]
theorem dut_register_hold_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = s.g41.r1317_nbackend_5Fisu_5Frf_5F31 := by
  change v12097 s i = s.g41.r1317_nbackend_5Fisu_5Frf_5F31
  simp [v12097, v11456, v11455, v12096, v11462, v11461, v11460, reset, idle]
theorem spec_register_hold_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0) :
    (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  change v23103 s i = s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31
  simp [v23103, v14555, v14554, v14553, v11455, v23102, v23101, v14560, v14559, v14558, v15284, reset, idle]
theorem registers_aligned_hold (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (idle : v9 s i = 0)
    (aligned : ArchitecturalRegistersAligned s) :
    ArchitecturalRegistersAligned (step s i) := by
  simpa only [ArchitecturalRegistersAligned, dut_register_hold_1 s i reset idle, spec_register_hold_1 s i reset idle, dut_register_hold_2 s i reset idle, spec_register_hold_2 s i reset idle, dut_register_hold_3 s i reset idle, spec_register_hold_3 s i reset idle, dut_register_hold_4 s i reset idle, spec_register_hold_4 s i reset idle, dut_register_hold_5 s i reset idle, spec_register_hold_5 s i reset idle, dut_register_hold_6 s i reset idle, spec_register_hold_6 s i reset idle, dut_register_hold_7 s i reset idle, spec_register_hold_7 s i reset idle, dut_register_hold_8 s i reset idle, spec_register_hold_8 s i reset idle, dut_register_hold_9 s i reset idle, spec_register_hold_9 s i reset idle, dut_register_hold_10 s i reset idle, spec_register_hold_10 s i reset idle, dut_register_hold_11 s i reset idle, spec_register_hold_11 s i reset idle, dut_register_hold_12 s i reset idle, spec_register_hold_12 s i reset idle, dut_register_hold_13 s i reset idle, spec_register_hold_13 s i reset idle, dut_register_hold_14 s i reset idle, spec_register_hold_14 s i reset idle, dut_register_hold_15 s i reset idle, spec_register_hold_15 s i reset idle, dut_register_hold_16 s i reset idle, spec_register_hold_16 s i reset idle, dut_register_hold_17 s i reset idle, spec_register_hold_17 s i reset idle, dut_register_hold_18 s i reset idle, spec_register_hold_18 s i reset idle, dut_register_hold_19 s i reset idle, spec_register_hold_19 s i reset idle, dut_register_hold_20 s i reset idle, spec_register_hold_20 s i reset idle, dut_register_hold_21 s i reset idle, spec_register_hold_21 s i reset idle, dut_register_hold_22 s i reset idle, spec_register_hold_22 s i reset idle, dut_register_hold_23 s i reset idle, spec_register_hold_23 s i reset idle, dut_register_hold_24 s i reset idle, spec_register_hold_24 s i reset idle, dut_register_hold_25 s i reset idle, spec_register_hold_25 s i reset idle, dut_register_hold_26 s i reset idle, spec_register_hold_26 s i reset idle, dut_register_hold_27 s i reset idle, spec_register_hold_27 s i reset idle, dut_register_hold_28 s i reset idle, spec_register_hold_28 s i reset idle, dut_register_hold_29 s i reset idle, spec_register_hold_29 s i reset idle, dut_register_hold_30 s i reset idle, spec_register_hold_30 s i reset idle, dut_register_hold_31 s i reset idle, spec_register_hold_31 s i reset idle] using aligned
#print axioms registers_aligned_hold
end NutShellProofs
