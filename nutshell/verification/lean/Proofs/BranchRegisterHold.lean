import Proofs.BranchWriteback
import Proofs.RegisterReset
namespace NutShellProofs
open nNutCore
theorem dut_register_disabled_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = s.g40.r1287_nbackend_5Fisu_5Frf_5F1 := by
  change v11857 s i = s.g40.r1287_nbackend_5Fisu_5Frf_5F1
  simp [v11857, v11456, v11455, v11856, reset, disabled]

theorem dut_register_disabled_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = s.g40.r1288_nbackend_5Fisu_5Frf_5F2 := by
  change v11865 s i = s.g40.r1288_nbackend_5Fisu_5Frf_5F2
  simp [v11865, v11456, v11455, v11864, reset, disabled]

theorem dut_register_disabled_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = s.g40.r1289_nbackend_5Fisu_5Frf_5F3 := by
  change v11873 s i = s.g40.r1289_nbackend_5Fisu_5Frf_5F3
  simp [v11873, v11456, v11455, v11872, reset, disabled]

theorem dut_register_disabled_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = s.g40.r1290_nbackend_5Fisu_5Frf_5F4 := by
  change v11881 s i = s.g40.r1290_nbackend_5Fisu_5Frf_5F4
  simp [v11881, v11456, v11455, v11880, reset, disabled]

theorem dut_register_disabled_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = s.g40.r1291_nbackend_5Fisu_5Frf_5F5 := by
  change v11889 s i = s.g40.r1291_nbackend_5Fisu_5Frf_5F5
  simp [v11889, v11456, v11455, v11888, reset, disabled]

theorem dut_register_disabled_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = s.g40.r1292_nbackend_5Fisu_5Frf_5F6 := by
  change v11897 s i = s.g40.r1292_nbackend_5Fisu_5Frf_5F6
  simp [v11897, v11456, v11455, v11896, reset, disabled]

theorem dut_register_disabled_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = s.g40.r1293_nbackend_5Fisu_5Frf_5F7 := by
  change v11905 s i = s.g40.r1293_nbackend_5Fisu_5Frf_5F7
  simp [v11905, v11456, v11455, v11904, reset, disabled]

theorem dut_register_disabled_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = s.g40.r1294_nbackend_5Fisu_5Frf_5F8 := by
  change v11913 s i = s.g40.r1294_nbackend_5Fisu_5Frf_5F8
  simp [v11913, v11456, v11455, v11912, reset, disabled]

theorem dut_register_disabled_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = s.g40.r1295_nbackend_5Fisu_5Frf_5F9 := by
  change v11921 s i = s.g40.r1295_nbackend_5Fisu_5Frf_5F9
  simp [v11921, v11456, v11455, v11920, reset, disabled]

theorem dut_register_disabled_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = s.g40.r1296_nbackend_5Fisu_5Frf_5F10 := by
  change v11929 s i = s.g40.r1296_nbackend_5Fisu_5Frf_5F10
  simp [v11929, v11456, v11455, v11928, reset, disabled]

theorem dut_register_disabled_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = s.g40.r1297_nbackend_5Fisu_5Frf_5F11 := by
  change v11937 s i = s.g40.r1297_nbackend_5Fisu_5Frf_5F11
  simp [v11937, v11456, v11455, v11936, reset, disabled]

theorem dut_register_disabled_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = s.g40.r1298_nbackend_5Fisu_5Frf_5F12 := by
  change v11945 s i = s.g40.r1298_nbackend_5Fisu_5Frf_5F12
  simp [v11945, v11456, v11455, v11944, reset, disabled]

theorem dut_register_disabled_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = s.g40.r1299_nbackend_5Fisu_5Frf_5F13 := by
  change v11953 s i = s.g40.r1299_nbackend_5Fisu_5Frf_5F13
  simp [v11953, v11456, v11455, v11952, reset, disabled]

theorem dut_register_disabled_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = s.g40.r1300_nbackend_5Fisu_5Frf_5F14 := by
  change v11961 s i = s.g40.r1300_nbackend_5Fisu_5Frf_5F14
  simp [v11961, v11456, v11455, v11960, reset, disabled]

theorem dut_register_disabled_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = s.g40.r1301_nbackend_5Fisu_5Frf_5F15 := by
  change v11969 s i = s.g40.r1301_nbackend_5Fisu_5Frf_5F15
  simp [v11969, v11456, v11455, v11968, reset, disabled]

theorem dut_register_disabled_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = s.g40.r1302_nbackend_5Fisu_5Frf_5F16 := by
  change v11977 s i = s.g40.r1302_nbackend_5Fisu_5Frf_5F16
  simp [v11977, v11456, v11455, v11976, reset, disabled]

theorem dut_register_disabled_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = s.g40.r1303_nbackend_5Fisu_5Frf_5F17 := by
  change v11985 s i = s.g40.r1303_nbackend_5Fisu_5Frf_5F17
  simp [v11985, v11456, v11455, v11984, reset, disabled]

theorem dut_register_disabled_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = s.g40.r1304_nbackend_5Fisu_5Frf_5F18 := by
  change v11993 s i = s.g40.r1304_nbackend_5Fisu_5Frf_5F18
  simp [v11993, v11456, v11455, v11992, reset, disabled]

theorem dut_register_disabled_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = s.g40.r1305_nbackend_5Fisu_5Frf_5F19 := by
  change v12001 s i = s.g40.r1305_nbackend_5Fisu_5Frf_5F19
  simp [v12001, v11456, v11455, v12000, reset, disabled]

theorem dut_register_disabled_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = s.g40.r1306_nbackend_5Fisu_5Frf_5F20 := by
  change v12009 s i = s.g40.r1306_nbackend_5Fisu_5Frf_5F20
  simp [v12009, v11456, v11455, v12008, reset, disabled]

theorem dut_register_disabled_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = s.g40.r1307_nbackend_5Fisu_5Frf_5F21 := by
  change v12017 s i = s.g40.r1307_nbackend_5Fisu_5Frf_5F21
  simp [v12017, v11456, v11455, v12016, reset, disabled]

theorem dut_register_disabled_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = s.g40.r1308_nbackend_5Fisu_5Frf_5F22 := by
  change v12025 s i = s.g40.r1308_nbackend_5Fisu_5Frf_5F22
  simp [v12025, v11456, v11455, v12024, reset, disabled]

theorem dut_register_disabled_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = s.g40.r1309_nbackend_5Fisu_5Frf_5F23 := by
  change v12033 s i = s.g40.r1309_nbackend_5Fisu_5Frf_5F23
  simp [v12033, v11456, v11455, v12032, reset, disabled]

theorem dut_register_disabled_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = s.g40.r1310_nbackend_5Fisu_5Frf_5F24 := by
  change v12041 s i = s.g40.r1310_nbackend_5Fisu_5Frf_5F24
  simp [v12041, v11456, v11455, v12040, reset, disabled]

theorem dut_register_disabled_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = s.g40.r1311_nbackend_5Fisu_5Frf_5F25 := by
  change v12049 s i = s.g40.r1311_nbackend_5Fisu_5Frf_5F25
  simp [v12049, v11456, v11455, v12048, reset, disabled]

theorem dut_register_disabled_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = s.g41.r1312_nbackend_5Fisu_5Frf_5F26 := by
  change v12057 s i = s.g41.r1312_nbackend_5Fisu_5Frf_5F26
  simp [v12057, v11456, v11455, v12056, reset, disabled]

theorem dut_register_disabled_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = s.g41.r1313_nbackend_5Fisu_5Frf_5F27 := by
  change v12065 s i = s.g41.r1313_nbackend_5Fisu_5Frf_5F27
  simp [v12065, v11456, v11455, v12064, reset, disabled]

theorem dut_register_disabled_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = s.g41.r1314_nbackend_5Fisu_5Frf_5F28 := by
  change v12073 s i = s.g41.r1314_nbackend_5Fisu_5Frf_5F28
  simp [v12073, v11456, v11455, v12072, reset, disabled]

theorem dut_register_disabled_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = s.g41.r1315_nbackend_5Fisu_5Frf_5F29 := by
  change v12081 s i = s.g41.r1315_nbackend_5Fisu_5Frf_5F29
  simp [v12081, v11456, v11455, v12080, reset, disabled]

theorem dut_register_disabled_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = s.g41.r1316_nbackend_5Fisu_5Frf_5F30 := by
  change v12089 s i = s.g41.r1316_nbackend_5Fisu_5Frf_5F30
  simp [v12089, v11456, v11455, v12088, reset, disabled]

theorem dut_register_disabled_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (disabled : v11462 s i = 0) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = s.g41.r1317_nbackend_5Fisu_5Frf_5F31 := by
  change v12097 s i = s.g41.r1317_nbackend_5Fisu_5Frf_5F31
  simp [v12097, v11456, v11455, v12096, reset, disabled]

theorem branch_dut_register_hold_1 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1287_nbackend_5Fisu_5Frf_5F1 = (run initial inputs (t + 2)).g40.r1287_nbackend_5Fisu_5Frf_5F1 := by
  exact dut_register_disabled_1 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_1

theorem branch_dut_register_hold_2 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1288_nbackend_5Fisu_5Frf_5F2 = (run initial inputs (t + 2)).g40.r1288_nbackend_5Fisu_5Frf_5F2 := by
  exact dut_register_disabled_2 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_2

theorem branch_dut_register_hold_3 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1289_nbackend_5Fisu_5Frf_5F3 = (run initial inputs (t + 2)).g40.r1289_nbackend_5Fisu_5Frf_5F3 := by
  exact dut_register_disabled_3 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_3

theorem branch_dut_register_hold_4 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1290_nbackend_5Fisu_5Frf_5F4 = (run initial inputs (t + 2)).g40.r1290_nbackend_5Fisu_5Frf_5F4 := by
  exact dut_register_disabled_4 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_4

theorem branch_dut_register_hold_5 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1291_nbackend_5Fisu_5Frf_5F5 = (run initial inputs (t + 2)).g40.r1291_nbackend_5Fisu_5Frf_5F5 := by
  exact dut_register_disabled_5 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_5

theorem branch_dut_register_hold_6 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1292_nbackend_5Fisu_5Frf_5F6 = (run initial inputs (t + 2)).g40.r1292_nbackend_5Fisu_5Frf_5F6 := by
  exact dut_register_disabled_6 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_6

theorem branch_dut_register_hold_7 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1293_nbackend_5Fisu_5Frf_5F7 = (run initial inputs (t + 2)).g40.r1293_nbackend_5Fisu_5Frf_5F7 := by
  exact dut_register_disabled_7 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_7

theorem branch_dut_register_hold_8 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1294_nbackend_5Fisu_5Frf_5F8 = (run initial inputs (t + 2)).g40.r1294_nbackend_5Fisu_5Frf_5F8 := by
  exact dut_register_disabled_8 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_8

theorem branch_dut_register_hold_9 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1295_nbackend_5Fisu_5Frf_5F9 = (run initial inputs (t + 2)).g40.r1295_nbackend_5Fisu_5Frf_5F9 := by
  exact dut_register_disabled_9 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_9

theorem branch_dut_register_hold_10 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1296_nbackend_5Fisu_5Frf_5F10 = (run initial inputs (t + 2)).g40.r1296_nbackend_5Fisu_5Frf_5F10 := by
  exact dut_register_disabled_10 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_10

theorem branch_dut_register_hold_11 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1297_nbackend_5Fisu_5Frf_5F11 = (run initial inputs (t + 2)).g40.r1297_nbackend_5Fisu_5Frf_5F11 := by
  exact dut_register_disabled_11 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_11

theorem branch_dut_register_hold_12 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1298_nbackend_5Fisu_5Frf_5F12 = (run initial inputs (t + 2)).g40.r1298_nbackend_5Fisu_5Frf_5F12 := by
  exact dut_register_disabled_12 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_12

theorem branch_dut_register_hold_13 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1299_nbackend_5Fisu_5Frf_5F13 = (run initial inputs (t + 2)).g40.r1299_nbackend_5Fisu_5Frf_5F13 := by
  exact dut_register_disabled_13 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_13

theorem branch_dut_register_hold_14 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1300_nbackend_5Fisu_5Frf_5F14 = (run initial inputs (t + 2)).g40.r1300_nbackend_5Fisu_5Frf_5F14 := by
  exact dut_register_disabled_14 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_14

theorem branch_dut_register_hold_15 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1301_nbackend_5Fisu_5Frf_5F15 = (run initial inputs (t + 2)).g40.r1301_nbackend_5Fisu_5Frf_5F15 := by
  exact dut_register_disabled_15 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_15

theorem branch_dut_register_hold_16 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1302_nbackend_5Fisu_5Frf_5F16 = (run initial inputs (t + 2)).g40.r1302_nbackend_5Fisu_5Frf_5F16 := by
  exact dut_register_disabled_16 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_16

theorem branch_dut_register_hold_17 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1303_nbackend_5Fisu_5Frf_5F17 = (run initial inputs (t + 2)).g40.r1303_nbackend_5Fisu_5Frf_5F17 := by
  exact dut_register_disabled_17 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_17

theorem branch_dut_register_hold_18 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1304_nbackend_5Fisu_5Frf_5F18 = (run initial inputs (t + 2)).g40.r1304_nbackend_5Fisu_5Frf_5F18 := by
  exact dut_register_disabled_18 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_18

theorem branch_dut_register_hold_19 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1305_nbackend_5Fisu_5Frf_5F19 = (run initial inputs (t + 2)).g40.r1305_nbackend_5Fisu_5Frf_5F19 := by
  exact dut_register_disabled_19 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_19

theorem branch_dut_register_hold_20 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1306_nbackend_5Fisu_5Frf_5F20 = (run initial inputs (t + 2)).g40.r1306_nbackend_5Fisu_5Frf_5F20 := by
  exact dut_register_disabled_20 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_20

theorem branch_dut_register_hold_21 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1307_nbackend_5Fisu_5Frf_5F21 = (run initial inputs (t + 2)).g40.r1307_nbackend_5Fisu_5Frf_5F21 := by
  exact dut_register_disabled_21 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_21

theorem branch_dut_register_hold_22 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1308_nbackend_5Fisu_5Frf_5F22 = (run initial inputs (t + 2)).g40.r1308_nbackend_5Fisu_5Frf_5F22 := by
  exact dut_register_disabled_22 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_22

theorem branch_dut_register_hold_23 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1309_nbackend_5Fisu_5Frf_5F23 = (run initial inputs (t + 2)).g40.r1309_nbackend_5Fisu_5Frf_5F23 := by
  exact dut_register_disabled_23 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_23

theorem branch_dut_register_hold_24 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1310_nbackend_5Fisu_5Frf_5F24 = (run initial inputs (t + 2)).g40.r1310_nbackend_5Fisu_5Frf_5F24 := by
  exact dut_register_disabled_24 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_24

theorem branch_dut_register_hold_25 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g40.r1311_nbackend_5Fisu_5Frf_5F25 = (run initial inputs (t + 2)).g40.r1311_nbackend_5Fisu_5Frf_5F25 := by
  exact dut_register_disabled_25 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_25

theorem branch_dut_register_hold_26 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1312_nbackend_5Fisu_5Frf_5F26 = (run initial inputs (t + 2)).g41.r1312_nbackend_5Fisu_5Frf_5F26 := by
  exact dut_register_disabled_26 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_26

theorem branch_dut_register_hold_27 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1313_nbackend_5Fisu_5Frf_5F27 = (run initial inputs (t + 2)).g41.r1313_nbackend_5Fisu_5Frf_5F27 := by
  exact dut_register_disabled_27 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_27

theorem branch_dut_register_hold_28 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1314_nbackend_5Fisu_5Frf_5F28 = (run initial inputs (t + 2)).g41.r1314_nbackend_5Fisu_5Frf_5F28 := by
  exact dut_register_disabled_28 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_28

theorem branch_dut_register_hold_29 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1315_nbackend_5Fisu_5Frf_5F29 = (run initial inputs (t + 2)).g41.r1315_nbackend_5Fisu_5Frf_5F29 := by
  exact dut_register_disabled_29 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_29

theorem branch_dut_register_hold_30 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1316_nbackend_5Fisu_5Frf_5F30 = (run initial inputs (t + 2)).g41.r1316_nbackend_5Fisu_5Frf_5F30 := by
  exact dut_register_disabled_30 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_30

theorem branch_dut_register_hold_31 (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g41.r1317_nbackend_5Fisu_5Frf_5F31 = (run initial inputs (t + 2)).g41.r1317_nbackend_5Fisu_5Frf_5F31 := by
  exact dut_register_disabled_31 _ _ currentReset
    (branch_writeback_disabled_run initial inputs reset t operation unit matched)
#print axioms branch_dut_register_hold_31

end NutShellProofs
