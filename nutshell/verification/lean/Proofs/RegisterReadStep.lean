import Proofs.RegisterReads
import Proofs.RegisterFrame
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 8192
theorem dut_register_no_write_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = s.g40.r1287_nbackend_5Fisu_5Frf_5F1 := by
  change v11857 s i = s.g40.r1287_nbackend_5Fisu_5Frf_5F1
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11850, v11851, v11852, v11853, v11854, v11855, v11856, v11857, reset, zero]
theorem dut_register_no_write_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = s.g40.r1288_nbackend_5Fisu_5Frf_5F2 := by
  change v11865 s i = s.g40.r1288_nbackend_5Fisu_5Frf_5F2
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11858, v11859, v11860, v11861, v11862, v11863, v11864, v11865, reset, zero]
theorem dut_register_no_write_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = s.g40.r1289_nbackend_5Fisu_5Frf_5F3 := by
  change v11873 s i = s.g40.r1289_nbackend_5Fisu_5Frf_5F3
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11866, v11867, v11868, v11869, v11870, v11871, v11872, v11873, reset, zero]
theorem dut_register_no_write_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = s.g40.r1290_nbackend_5Fisu_5Frf_5F4 := by
  change v11881 s i = s.g40.r1290_nbackend_5Fisu_5Frf_5F4
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11874, v11875, v11876, v11877, v11878, v11879, v11880, v11881, reset, zero]
theorem dut_register_no_write_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = s.g40.r1291_nbackend_5Fisu_5Frf_5F5 := by
  change v11889 s i = s.g40.r1291_nbackend_5Fisu_5Frf_5F5
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11882, v11883, v11884, v11885, v11886, v11887, v11888, v11889, reset, zero]
theorem dut_register_no_write_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = s.g40.r1292_nbackend_5Fisu_5Frf_5F6 := by
  change v11897 s i = s.g40.r1292_nbackend_5Fisu_5Frf_5F6
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11890, v11891, v11892, v11893, v11894, v11895, v11896, v11897, reset, zero]
theorem dut_register_no_write_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = s.g40.r1293_nbackend_5Fisu_5Frf_5F7 := by
  change v11905 s i = s.g40.r1293_nbackend_5Fisu_5Frf_5F7
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11898, v11899, v11900, v11901, v11902, v11903, v11904, v11905, reset, zero]
theorem dut_register_no_write_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = s.g40.r1294_nbackend_5Fisu_5Frf_5F8 := by
  change v11913 s i = s.g40.r1294_nbackend_5Fisu_5Frf_5F8
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11906, v11907, v11908, v11909, v11910, v11911, v11912, v11913, reset, zero]
theorem dut_register_no_write_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = s.g40.r1295_nbackend_5Fisu_5Frf_5F9 := by
  change v11921 s i = s.g40.r1295_nbackend_5Fisu_5Frf_5F9
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11914, v11915, v11916, v11917, v11918, v11919, v11920, v11921, reset, zero]
theorem dut_register_no_write_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = s.g40.r1296_nbackend_5Fisu_5Frf_5F10 := by
  change v11929 s i = s.g40.r1296_nbackend_5Fisu_5Frf_5F10
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11922, v11923, v11924, v11925, v11926, v11927, v11928, v11929, reset, zero]
theorem dut_register_no_write_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = s.g40.r1297_nbackend_5Fisu_5Frf_5F11 := by
  change v11937 s i = s.g40.r1297_nbackend_5Fisu_5Frf_5F11
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11930, v11931, v11932, v11933, v11934, v11935, v11936, v11937, reset, zero]
theorem dut_register_no_write_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = s.g40.r1298_nbackend_5Fisu_5Frf_5F12 := by
  change v11945 s i = s.g40.r1298_nbackend_5Fisu_5Frf_5F12
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11938, v11939, v11940, v11941, v11942, v11943, v11944, v11945, reset, zero]
theorem dut_register_no_write_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = s.g40.r1299_nbackend_5Fisu_5Frf_5F13 := by
  change v11953 s i = s.g40.r1299_nbackend_5Fisu_5Frf_5F13
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11946, v11947, v11948, v11949, v11950, v11951, v11952, v11953, reset, zero]
theorem dut_register_no_write_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = s.g40.r1300_nbackend_5Fisu_5Frf_5F14 := by
  change v11961 s i = s.g40.r1300_nbackend_5Fisu_5Frf_5F14
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11954, v11955, v11956, v11957, v11958, v11959, v11960, v11961, reset, zero]
theorem dut_register_no_write_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = s.g40.r1301_nbackend_5Fisu_5Frf_5F15 := by
  change v11969 s i = s.g40.r1301_nbackend_5Fisu_5Frf_5F15
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11962, v11963, v11964, v11965, v11966, v11967, v11968, v11969, reset, zero]
theorem dut_register_no_write_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = s.g40.r1302_nbackend_5Fisu_5Frf_5F16 := by
  change v11977 s i = s.g40.r1302_nbackend_5Fisu_5Frf_5F16
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11970, v11971, v11972, v11973, v11974, v11975, v11976, v11977, reset, zero]
theorem dut_register_no_write_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = s.g40.r1303_nbackend_5Fisu_5Frf_5F17 := by
  change v11985 s i = s.g40.r1303_nbackend_5Fisu_5Frf_5F17
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11978, v11979, v11980, v11981, v11982, v11983, v11984, v11985, reset, zero]
theorem dut_register_no_write_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = s.g40.r1304_nbackend_5Fisu_5Frf_5F18 := by
  change v11993 s i = s.g40.r1304_nbackend_5Fisu_5Frf_5F18
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11986, v11987, v11988, v11989, v11990, v11991, v11992, v11993, reset, zero]
theorem dut_register_no_write_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = s.g40.r1305_nbackend_5Fisu_5Frf_5F19 := by
  change v12001 s i = s.g40.r1305_nbackend_5Fisu_5Frf_5F19
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v11994, v11995, v11996, v11997, v11998, v11999, v12000, v12001, reset, zero]
theorem dut_register_no_write_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = s.g40.r1306_nbackend_5Fisu_5Frf_5F20 := by
  change v12009 s i = s.g40.r1306_nbackend_5Fisu_5Frf_5F20
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12002, v12003, v12004, v12005, v12006, v12007, v12008, v12009, reset, zero]
theorem dut_register_no_write_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = s.g40.r1307_nbackend_5Fisu_5Frf_5F21 := by
  change v12017 s i = s.g40.r1307_nbackend_5Fisu_5Frf_5F21
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12010, v12011, v12012, v12013, v12014, v12015, v12016, v12017, reset, zero]
theorem dut_register_no_write_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = s.g40.r1308_nbackend_5Fisu_5Frf_5F22 := by
  change v12025 s i = s.g40.r1308_nbackend_5Fisu_5Frf_5F22
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12018, v12019, v12020, v12021, v12022, v12023, v12024, v12025, reset, zero]
theorem dut_register_no_write_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = s.g40.r1309_nbackend_5Fisu_5Frf_5F23 := by
  change v12033 s i = s.g40.r1309_nbackend_5Fisu_5Frf_5F23
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12026, v12027, v12028, v12029, v12030, v12031, v12032, v12033, reset, zero]
theorem dut_register_no_write_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = s.g40.r1310_nbackend_5Fisu_5Frf_5F24 := by
  change v12041 s i = s.g40.r1310_nbackend_5Fisu_5Frf_5F24
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12034, v12035, v12036, v12037, v12038, v12039, v12040, v12041, reset, zero]
theorem dut_register_no_write_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = s.g40.r1311_nbackend_5Fisu_5Frf_5F25 := by
  change v12049 s i = s.g40.r1311_nbackend_5Fisu_5Frf_5F25
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12042, v12043, v12044, v12045, v12046, v12047, v12048, v12049, reset, zero]
theorem dut_register_no_write_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = s.g41.r1312_nbackend_5Fisu_5Frf_5F26 := by
  change v12057 s i = s.g41.r1312_nbackend_5Fisu_5Frf_5F26
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12050, v12051, v12052, v12053, v12054, v12055, v12056, v12057, reset, zero]
theorem dut_register_no_write_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = s.g41.r1313_nbackend_5Fisu_5Frf_5F27 := by
  change v12065 s i = s.g41.r1313_nbackend_5Fisu_5Frf_5F27
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12058, v12059, v12060, v12061, v12062, v12063, v12064, v12065, reset, zero]
theorem dut_register_no_write_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = s.g41.r1314_nbackend_5Fisu_5Frf_5F28 := by
  change v12073 s i = s.g41.r1314_nbackend_5Fisu_5Frf_5F28
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12066, v12067, v12068, v12069, v12070, v12071, v12072, v12073, reset, zero]
theorem dut_register_no_write_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = s.g41.r1315_nbackend_5Fisu_5Frf_5F29 := by
  change v12081 s i = s.g41.r1315_nbackend_5Fisu_5Frf_5F29
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12074, v12075, v12076, v12077, v12078, v12079, v12080, v12081, reset, zero]
theorem dut_register_no_write_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = s.g41.r1316_nbackend_5Fisu_5Frf_5F30 := by
  change v12089 s i = s.g41.r1316_nbackend_5Fisu_5Frf_5F30
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12082, v12083, v12084, v12085, v12086, v12087, v12088, v12089, reset, zero]
theorem dut_register_no_write_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (write : v11462 s i ≠ 1) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = s.g41.r1317_nbackend_5Fisu_5Frf_5F31 := by
  change v12097 s i = s.g41.r1317_nbackend_5Fisu_5Frf_5F31
  have zero : v11462 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right write
  simp [v11455, v11456, v11816, v11817, v12090, v12091, v12092, v12093, v12094, v12095, v12096, v12097, reset, zero]
theorem dut_read_step (s : State) (i next : Inputs) (addr : BitVec 5)
    (reset : i.g0.nreset = 0) :
    dutRead.v25201 (step s i) next addr =
      if addr = 0 then 0 else
      if v11465 s i = addr ∧ v11462 s i = 1 then v11842 s i
      else dutRead.v25201 s i addr := by
  have bound := addr.isLt
  have cases : addr.toNat = 0 ∨ addr.toNat = 1 ∨ addr.toNat = 2 ∨ addr.toNat = 3 ∨ addr.toNat = 4 ∨ addr.toNat = 5 ∨ addr.toNat = 6 ∨ addr.toNat = 7 ∨ addr.toNat = 8 ∨ addr.toNat = 9 ∨ addr.toNat = 10 ∨ addr.toNat = 11 ∨ addr.toNat = 12 ∨ addr.toNat = 13 ∨ addr.toNat = 14 ∨ addr.toNat = 15 ∨ addr.toNat = 16 ∨ addr.toNat = 17 ∨ addr.toNat = 18 ∨ addr.toNat = 19 ∨ addr.toNat = 20 ∨ addr.toNat = 21 ∨ addr.toNat = 22 ∨ addr.toNat = 23 ∨ addr.toNat = 24 ∨ addr.toNat = 25 ∨ addr.toNat = 26 ∨ addr.toNat = 27 ∨ addr.toNat = 28 ∨ addr.toNat = 29 ∨ addr.toNat = 30 ∨ addr.toNat = 31 := by omega
  rcases cases with c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13 | c14 | c15 | c16 | c17 | c18 | c19 | c20 | c21 | c22 | c23 | c24 | c25 | c26 | c27 | c28 | c29 | c30 | c31
  · have eq : addr = (0 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c0)
    subst addr
    rw [dutRead.read_0, if_pos rfl]
  · have eq : addr = (1 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c1)
    subst addr
    rw [dutRead.read_1, dutRead.read_1]
    by_cases dest : v11465 s i = (1 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (1 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_1 s i reset dest write
      · rw [if_neg (by decide : (1 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_1 s i reset write
    · rw [if_neg (by decide : (1 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_1 s i reset dest
  · have eq : addr = (2 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c2)
    subst addr
    rw [dutRead.read_2, dutRead.read_2]
    by_cases dest : v11465 s i = (2 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (2 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_2 s i reset dest write
      · rw [if_neg (by decide : (2 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_2 s i reset write
    · rw [if_neg (by decide : (2 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_2 s i reset dest
  · have eq : addr = (3 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c3)
    subst addr
    rw [dutRead.read_3, dutRead.read_3]
    by_cases dest : v11465 s i = (3 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (3 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_3 s i reset dest write
      · rw [if_neg (by decide : (3 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_3 s i reset write
    · rw [if_neg (by decide : (3 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_3 s i reset dest
  · have eq : addr = (4 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c4)
    subst addr
    rw [dutRead.read_4, dutRead.read_4]
    by_cases dest : v11465 s i = (4 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (4 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_4 s i reset dest write
      · rw [if_neg (by decide : (4 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_4 s i reset write
    · rw [if_neg (by decide : (4 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_4 s i reset dest
  · have eq : addr = (5 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c5)
    subst addr
    rw [dutRead.read_5, dutRead.read_5]
    by_cases dest : v11465 s i = (5 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (5 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_5 s i reset dest write
      · rw [if_neg (by decide : (5 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_5 s i reset write
    · rw [if_neg (by decide : (5 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_5 s i reset dest
  · have eq : addr = (6 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c6)
    subst addr
    rw [dutRead.read_6, dutRead.read_6]
    by_cases dest : v11465 s i = (6 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (6 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_6 s i reset dest write
      · rw [if_neg (by decide : (6 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_6 s i reset write
    · rw [if_neg (by decide : (6 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_6 s i reset dest
  · have eq : addr = (7 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c7)
    subst addr
    rw [dutRead.read_7, dutRead.read_7]
    by_cases dest : v11465 s i = (7 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (7 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_7 s i reset dest write
      · rw [if_neg (by decide : (7 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_7 s i reset write
    · rw [if_neg (by decide : (7 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_7 s i reset dest
  · have eq : addr = (8 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c8)
    subst addr
    rw [dutRead.read_8, dutRead.read_8]
    by_cases dest : v11465 s i = (8 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (8 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_8 s i reset dest write
      · rw [if_neg (by decide : (8 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_8 s i reset write
    · rw [if_neg (by decide : (8 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_8 s i reset dest
  · have eq : addr = (9 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c9)
    subst addr
    rw [dutRead.read_9, dutRead.read_9]
    by_cases dest : v11465 s i = (9 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (9 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_9 s i reset dest write
      · rw [if_neg (by decide : (9 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_9 s i reset write
    · rw [if_neg (by decide : (9 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_9 s i reset dest
  · have eq : addr = (10 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c10)
    subst addr
    rw [dutRead.read_10, dutRead.read_10]
    by_cases dest : v11465 s i = (10 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (10 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_10 s i reset dest write
      · rw [if_neg (by decide : (10 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_10 s i reset write
    · rw [if_neg (by decide : (10 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_10 s i reset dest
  · have eq : addr = (11 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c11)
    subst addr
    rw [dutRead.read_11, dutRead.read_11]
    by_cases dest : v11465 s i = (11 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (11 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_11 s i reset dest write
      · rw [if_neg (by decide : (11 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_11 s i reset write
    · rw [if_neg (by decide : (11 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_11 s i reset dest
  · have eq : addr = (12 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c12)
    subst addr
    rw [dutRead.read_12, dutRead.read_12]
    by_cases dest : v11465 s i = (12 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (12 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_12 s i reset dest write
      · rw [if_neg (by decide : (12 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_12 s i reset write
    · rw [if_neg (by decide : (12 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_12 s i reset dest
  · have eq : addr = (13 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c13)
    subst addr
    rw [dutRead.read_13, dutRead.read_13]
    by_cases dest : v11465 s i = (13 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (13 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_13 s i reset dest write
      · rw [if_neg (by decide : (13 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_13 s i reset write
    · rw [if_neg (by decide : (13 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_13 s i reset dest
  · have eq : addr = (14 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c14)
    subst addr
    rw [dutRead.read_14, dutRead.read_14]
    by_cases dest : v11465 s i = (14 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (14 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_14 s i reset dest write
      · rw [if_neg (by decide : (14 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_14 s i reset write
    · rw [if_neg (by decide : (14 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_14 s i reset dest
  · have eq : addr = (15 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c15)
    subst addr
    rw [dutRead.read_15, dutRead.read_15]
    by_cases dest : v11465 s i = (15 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (15 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_15 s i reset dest write
      · rw [if_neg (by decide : (15 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_15 s i reset write
    · rw [if_neg (by decide : (15 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_15 s i reset dest
  · have eq : addr = (16 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c16)
    subst addr
    rw [dutRead.read_16, dutRead.read_16]
    by_cases dest : v11465 s i = (16 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (16 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_16 s i reset dest write
      · rw [if_neg (by decide : (16 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_16 s i reset write
    · rw [if_neg (by decide : (16 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_16 s i reset dest
  · have eq : addr = (17 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c17)
    subst addr
    rw [dutRead.read_17, dutRead.read_17]
    by_cases dest : v11465 s i = (17 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (17 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_17 s i reset dest write
      · rw [if_neg (by decide : (17 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_17 s i reset write
    · rw [if_neg (by decide : (17 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_17 s i reset dest
  · have eq : addr = (18 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c18)
    subst addr
    rw [dutRead.read_18, dutRead.read_18]
    by_cases dest : v11465 s i = (18 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (18 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_18 s i reset dest write
      · rw [if_neg (by decide : (18 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_18 s i reset write
    · rw [if_neg (by decide : (18 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_18 s i reset dest
  · have eq : addr = (19 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c19)
    subst addr
    rw [dutRead.read_19, dutRead.read_19]
    by_cases dest : v11465 s i = (19 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (19 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_19 s i reset dest write
      · rw [if_neg (by decide : (19 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_19 s i reset write
    · rw [if_neg (by decide : (19 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_19 s i reset dest
  · have eq : addr = (20 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c20)
    subst addr
    rw [dutRead.read_20, dutRead.read_20]
    by_cases dest : v11465 s i = (20 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (20 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_20 s i reset dest write
      · rw [if_neg (by decide : (20 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_20 s i reset write
    · rw [if_neg (by decide : (20 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_20 s i reset dest
  · have eq : addr = (21 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c21)
    subst addr
    rw [dutRead.read_21, dutRead.read_21]
    by_cases dest : v11465 s i = (21 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (21 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_21 s i reset dest write
      · rw [if_neg (by decide : (21 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_21 s i reset write
    · rw [if_neg (by decide : (21 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_21 s i reset dest
  · have eq : addr = (22 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c22)
    subst addr
    rw [dutRead.read_22, dutRead.read_22]
    by_cases dest : v11465 s i = (22 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (22 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_22 s i reset dest write
      · rw [if_neg (by decide : (22 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_22 s i reset write
    · rw [if_neg (by decide : (22 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_22 s i reset dest
  · have eq : addr = (23 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c23)
    subst addr
    rw [dutRead.read_23, dutRead.read_23]
    by_cases dest : v11465 s i = (23 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (23 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_23 s i reset dest write
      · rw [if_neg (by decide : (23 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_23 s i reset write
    · rw [if_neg (by decide : (23 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_23 s i reset dest
  · have eq : addr = (24 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c24)
    subst addr
    rw [dutRead.read_24, dutRead.read_24]
    by_cases dest : v11465 s i = (24 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (24 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_24 s i reset dest write
      · rw [if_neg (by decide : (24 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_24 s i reset write
    · rw [if_neg (by decide : (24 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_24 s i reset dest
  · have eq : addr = (25 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c25)
    subst addr
    rw [dutRead.read_25, dutRead.read_25]
    by_cases dest : v11465 s i = (25 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (25 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_25 s i reset dest write
      · rw [if_neg (by decide : (25 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_25 s i reset write
    · rw [if_neg (by decide : (25 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_25 s i reset dest
  · have eq : addr = (26 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c26)
    subst addr
    rw [dutRead.read_26, dutRead.read_26]
    by_cases dest : v11465 s i = (26 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (26 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_26 s i reset dest write
      · rw [if_neg (by decide : (26 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_26 s i reset write
    · rw [if_neg (by decide : (26 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_26 s i reset dest
  · have eq : addr = (27 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c27)
    subst addr
    rw [dutRead.read_27, dutRead.read_27]
    by_cases dest : v11465 s i = (27 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (27 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_27 s i reset dest write
      · rw [if_neg (by decide : (27 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_27 s i reset write
    · rw [if_neg (by decide : (27 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_27 s i reset dest
  · have eq : addr = (28 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c28)
    subst addr
    rw [dutRead.read_28, dutRead.read_28]
    by_cases dest : v11465 s i = (28 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (28 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_28 s i reset dest write
      · rw [if_neg (by decide : (28 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_28 s i reset write
    · rw [if_neg (by decide : (28 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_28 s i reset dest
  · have eq : addr = (29 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c29)
    subst addr
    rw [dutRead.read_29, dutRead.read_29]
    by_cases dest : v11465 s i = (29 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (29 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_29 s i reset dest write
      · rw [if_neg (by decide : (29 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_29 s i reset write
    · rw [if_neg (by decide : (29 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_29 s i reset dest
  · have eq : addr = (30 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c30)
    subst addr
    rw [dutRead.read_30, dutRead.read_30]
    by_cases dest : v11465 s i = (30 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (30 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_30 s i reset dest write
      · rw [if_neg (by decide : (30 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_30 s i reset write
    · rw [if_neg (by decide : (30 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_30 s i reset dest
  · have eq : addr = (31 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c31)
    subst addr
    rw [dutRead.read_31, dutRead.read_31]
    by_cases dest : v11465 s i = (31 : BitVec 5)
    · by_cases write : v11462 s i = 1
      · rw [if_neg (by decide : (31 : BitVec 5) ≠ 0), if_pos ⟨dest, write⟩]
        exact dut_register_write_31 s i reset dest write
      · rw [if_neg (by decide : (31 : BitVec 5) ≠ 0), if_neg (fun h => write h.2)]
        exact dut_register_no_write_31 s i reset write
    · rw [if_neg (by decide : (31 : BitVec 5) ≠ 0), if_neg (fun h => dest h.1)]
      exact dut_register_frame_31 s i reset dest
#print axioms dut_read_step
end NutShellProofs
