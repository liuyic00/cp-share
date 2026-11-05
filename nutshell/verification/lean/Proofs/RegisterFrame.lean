import Proofs.RegisterBridge
namespace NutShellProofs
open nNutCore
theorem dut_register_frame_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 1) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = s.g40.r1287_nbackend_5Fisu_5Frf_5F1 := by
  change v11857 s i = s.g40.r1287_nbackend_5Fisu_5Frf_5F1
  simp [v11455, v11456, v11850, v11851, v11816, v11817, v11852, v11853, v11854, v11855, v11856, v11857, reset, Ne.symm other]
theorem dut_register_write_1 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 1)
    (write : v11462 s i = 1) :
    (step s i).g40.r1287_nbackend_5Fisu_5Frf_5F1 = v11842 s i := by
  change v11857 s i = v11842 s i
  simp [v11455, v11456, v11850, v11851, v11816, v11817, v11852, v11853, v11854, v11855, v11856, v11857, reset, dest, write]
theorem dut_register_frame_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 2) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = s.g40.r1288_nbackend_5Fisu_5Frf_5F2 := by
  change v11865 s i = s.g40.r1288_nbackend_5Fisu_5Frf_5F2
  simp [v11455, v11456, v11858, v11859, v11816, v11817, v11860, v11861, v11862, v11863, v11864, v11865, reset, Ne.symm other]
theorem dut_register_write_2 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 2)
    (write : v11462 s i = 1) :
    (step s i).g40.r1288_nbackend_5Fisu_5Frf_5F2 = v11842 s i := by
  change v11865 s i = v11842 s i
  simp [v11455, v11456, v11858, v11859, v11816, v11817, v11860, v11861, v11862, v11863, v11864, v11865, reset, dest, write]
theorem dut_register_frame_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 3) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = s.g40.r1289_nbackend_5Fisu_5Frf_5F3 := by
  change v11873 s i = s.g40.r1289_nbackend_5Fisu_5Frf_5F3
  simp [v11455, v11456, v11866, v11867, v11816, v11817, v11868, v11869, v11870, v11871, v11872, v11873, reset, Ne.symm other]
theorem dut_register_write_3 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 3)
    (write : v11462 s i = 1) :
    (step s i).g40.r1289_nbackend_5Fisu_5Frf_5F3 = v11842 s i := by
  change v11873 s i = v11842 s i
  simp [v11455, v11456, v11866, v11867, v11816, v11817, v11868, v11869, v11870, v11871, v11872, v11873, reset, dest, write]
theorem dut_register_frame_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 4) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = s.g40.r1290_nbackend_5Fisu_5Frf_5F4 := by
  change v11881 s i = s.g40.r1290_nbackend_5Fisu_5Frf_5F4
  simp [v11455, v11456, v11874, v11875, v11816, v11817, v11876, v11877, v11878, v11879, v11880, v11881, reset, Ne.symm other]
theorem dut_register_write_4 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 4)
    (write : v11462 s i = 1) :
    (step s i).g40.r1290_nbackend_5Fisu_5Frf_5F4 = v11842 s i := by
  change v11881 s i = v11842 s i
  simp [v11455, v11456, v11874, v11875, v11816, v11817, v11876, v11877, v11878, v11879, v11880, v11881, reset, dest, write]
theorem dut_register_frame_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 5) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = s.g40.r1291_nbackend_5Fisu_5Frf_5F5 := by
  change v11889 s i = s.g40.r1291_nbackend_5Fisu_5Frf_5F5
  simp [v11455, v11456, v11882, v11883, v11816, v11817, v11884, v11885, v11886, v11887, v11888, v11889, reset, Ne.symm other]
theorem dut_register_write_5 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 5)
    (write : v11462 s i = 1) :
    (step s i).g40.r1291_nbackend_5Fisu_5Frf_5F5 = v11842 s i := by
  change v11889 s i = v11842 s i
  simp [v11455, v11456, v11882, v11883, v11816, v11817, v11884, v11885, v11886, v11887, v11888, v11889, reset, dest, write]
theorem dut_register_frame_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 6) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = s.g40.r1292_nbackend_5Fisu_5Frf_5F6 := by
  change v11897 s i = s.g40.r1292_nbackend_5Fisu_5Frf_5F6
  simp [v11455, v11456, v11890, v11891, v11816, v11817, v11892, v11893, v11894, v11895, v11896, v11897, reset, Ne.symm other]
theorem dut_register_write_6 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 6)
    (write : v11462 s i = 1) :
    (step s i).g40.r1292_nbackend_5Fisu_5Frf_5F6 = v11842 s i := by
  change v11897 s i = v11842 s i
  simp [v11455, v11456, v11890, v11891, v11816, v11817, v11892, v11893, v11894, v11895, v11896, v11897, reset, dest, write]
theorem dut_register_frame_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 7) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = s.g40.r1293_nbackend_5Fisu_5Frf_5F7 := by
  change v11905 s i = s.g40.r1293_nbackend_5Fisu_5Frf_5F7
  simp [v11455, v11456, v11898, v11899, v11816, v11817, v11900, v11901, v11902, v11903, v11904, v11905, reset, Ne.symm other]
theorem dut_register_write_7 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 7)
    (write : v11462 s i = 1) :
    (step s i).g40.r1293_nbackend_5Fisu_5Frf_5F7 = v11842 s i := by
  change v11905 s i = v11842 s i
  simp [v11455, v11456, v11898, v11899, v11816, v11817, v11900, v11901, v11902, v11903, v11904, v11905, reset, dest, write]
theorem dut_register_frame_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 8) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = s.g40.r1294_nbackend_5Fisu_5Frf_5F8 := by
  change v11913 s i = s.g40.r1294_nbackend_5Fisu_5Frf_5F8
  simp [v11455, v11456, v11906, v11907, v11816, v11817, v11908, v11909, v11910, v11911, v11912, v11913, reset, Ne.symm other]
theorem dut_register_write_8 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 8)
    (write : v11462 s i = 1) :
    (step s i).g40.r1294_nbackend_5Fisu_5Frf_5F8 = v11842 s i := by
  change v11913 s i = v11842 s i
  simp [v11455, v11456, v11906, v11907, v11816, v11817, v11908, v11909, v11910, v11911, v11912, v11913, reset, dest, write]
theorem dut_register_frame_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 9) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = s.g40.r1295_nbackend_5Fisu_5Frf_5F9 := by
  change v11921 s i = s.g40.r1295_nbackend_5Fisu_5Frf_5F9
  simp [v11455, v11456, v11914, v11915, v11816, v11817, v11916, v11917, v11918, v11919, v11920, v11921, reset, Ne.symm other]
theorem dut_register_write_9 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 9)
    (write : v11462 s i = 1) :
    (step s i).g40.r1295_nbackend_5Fisu_5Frf_5F9 = v11842 s i := by
  change v11921 s i = v11842 s i
  simp [v11455, v11456, v11914, v11915, v11816, v11817, v11916, v11917, v11918, v11919, v11920, v11921, reset, dest, write]
theorem dut_register_frame_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 10) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = s.g40.r1296_nbackend_5Fisu_5Frf_5F10 := by
  change v11929 s i = s.g40.r1296_nbackend_5Fisu_5Frf_5F10
  simp [v11455, v11456, v11922, v11923, v11816, v11817, v11924, v11925, v11926, v11927, v11928, v11929, reset, Ne.symm other]
theorem dut_register_write_10 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 10)
    (write : v11462 s i = 1) :
    (step s i).g40.r1296_nbackend_5Fisu_5Frf_5F10 = v11842 s i := by
  change v11929 s i = v11842 s i
  simp [v11455, v11456, v11922, v11923, v11816, v11817, v11924, v11925, v11926, v11927, v11928, v11929, reset, dest, write]
theorem dut_register_frame_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 11) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = s.g40.r1297_nbackend_5Fisu_5Frf_5F11 := by
  change v11937 s i = s.g40.r1297_nbackend_5Fisu_5Frf_5F11
  simp [v11455, v11456, v11930, v11931, v11816, v11817, v11932, v11933, v11934, v11935, v11936, v11937, reset, Ne.symm other]
theorem dut_register_write_11 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 11)
    (write : v11462 s i = 1) :
    (step s i).g40.r1297_nbackend_5Fisu_5Frf_5F11 = v11842 s i := by
  change v11937 s i = v11842 s i
  simp [v11455, v11456, v11930, v11931, v11816, v11817, v11932, v11933, v11934, v11935, v11936, v11937, reset, dest, write]
theorem dut_register_frame_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 12) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = s.g40.r1298_nbackend_5Fisu_5Frf_5F12 := by
  change v11945 s i = s.g40.r1298_nbackend_5Fisu_5Frf_5F12
  simp [v11455, v11456, v11938, v11939, v11816, v11817, v11940, v11941, v11942, v11943, v11944, v11945, reset, Ne.symm other]
theorem dut_register_write_12 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 12)
    (write : v11462 s i = 1) :
    (step s i).g40.r1298_nbackend_5Fisu_5Frf_5F12 = v11842 s i := by
  change v11945 s i = v11842 s i
  simp [v11455, v11456, v11938, v11939, v11816, v11817, v11940, v11941, v11942, v11943, v11944, v11945, reset, dest, write]
theorem dut_register_frame_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 13) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = s.g40.r1299_nbackend_5Fisu_5Frf_5F13 := by
  change v11953 s i = s.g40.r1299_nbackend_5Fisu_5Frf_5F13
  simp [v11455, v11456, v11946, v11947, v11816, v11817, v11948, v11949, v11950, v11951, v11952, v11953, reset, Ne.symm other]
theorem dut_register_write_13 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 13)
    (write : v11462 s i = 1) :
    (step s i).g40.r1299_nbackend_5Fisu_5Frf_5F13 = v11842 s i := by
  change v11953 s i = v11842 s i
  simp [v11455, v11456, v11946, v11947, v11816, v11817, v11948, v11949, v11950, v11951, v11952, v11953, reset, dest, write]
theorem dut_register_frame_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 14) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = s.g40.r1300_nbackend_5Fisu_5Frf_5F14 := by
  change v11961 s i = s.g40.r1300_nbackend_5Fisu_5Frf_5F14
  simp [v11455, v11456, v11954, v11955, v11816, v11817, v11956, v11957, v11958, v11959, v11960, v11961, reset, Ne.symm other]
theorem dut_register_write_14 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 14)
    (write : v11462 s i = 1) :
    (step s i).g40.r1300_nbackend_5Fisu_5Frf_5F14 = v11842 s i := by
  change v11961 s i = v11842 s i
  simp [v11455, v11456, v11954, v11955, v11816, v11817, v11956, v11957, v11958, v11959, v11960, v11961, reset, dest, write]
theorem dut_register_frame_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 15) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = s.g40.r1301_nbackend_5Fisu_5Frf_5F15 := by
  change v11969 s i = s.g40.r1301_nbackend_5Fisu_5Frf_5F15
  simp [v11455, v11456, v11962, v11963, v11816, v11817, v11964, v11965, v11966, v11967, v11968, v11969, reset, Ne.symm other]
theorem dut_register_write_15 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 15)
    (write : v11462 s i = 1) :
    (step s i).g40.r1301_nbackend_5Fisu_5Frf_5F15 = v11842 s i := by
  change v11969 s i = v11842 s i
  simp [v11455, v11456, v11962, v11963, v11816, v11817, v11964, v11965, v11966, v11967, v11968, v11969, reset, dest, write]
theorem dut_register_frame_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 16) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = s.g40.r1302_nbackend_5Fisu_5Frf_5F16 := by
  change v11977 s i = s.g40.r1302_nbackend_5Fisu_5Frf_5F16
  simp [v11455, v11456, v11970, v11971, v11816, v11817, v11972, v11973, v11974, v11975, v11976, v11977, reset, Ne.symm other]
theorem dut_register_write_16 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 16)
    (write : v11462 s i = 1) :
    (step s i).g40.r1302_nbackend_5Fisu_5Frf_5F16 = v11842 s i := by
  change v11977 s i = v11842 s i
  simp [v11455, v11456, v11970, v11971, v11816, v11817, v11972, v11973, v11974, v11975, v11976, v11977, reset, dest, write]
theorem dut_register_frame_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 17) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = s.g40.r1303_nbackend_5Fisu_5Frf_5F17 := by
  change v11985 s i = s.g40.r1303_nbackend_5Fisu_5Frf_5F17
  simp [v11455, v11456, v11978, v11979, v11816, v11817, v11980, v11981, v11982, v11983, v11984, v11985, reset, Ne.symm other]
theorem dut_register_write_17 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 17)
    (write : v11462 s i = 1) :
    (step s i).g40.r1303_nbackend_5Fisu_5Frf_5F17 = v11842 s i := by
  change v11985 s i = v11842 s i
  simp [v11455, v11456, v11978, v11979, v11816, v11817, v11980, v11981, v11982, v11983, v11984, v11985, reset, dest, write]
theorem dut_register_frame_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 18) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = s.g40.r1304_nbackend_5Fisu_5Frf_5F18 := by
  change v11993 s i = s.g40.r1304_nbackend_5Fisu_5Frf_5F18
  simp [v11455, v11456, v11986, v11987, v11816, v11817, v11988, v11989, v11990, v11991, v11992, v11993, reset, Ne.symm other]
theorem dut_register_write_18 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 18)
    (write : v11462 s i = 1) :
    (step s i).g40.r1304_nbackend_5Fisu_5Frf_5F18 = v11842 s i := by
  change v11993 s i = v11842 s i
  simp [v11455, v11456, v11986, v11987, v11816, v11817, v11988, v11989, v11990, v11991, v11992, v11993, reset, dest, write]
theorem dut_register_frame_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 19) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = s.g40.r1305_nbackend_5Fisu_5Frf_5F19 := by
  change v12001 s i = s.g40.r1305_nbackend_5Fisu_5Frf_5F19
  simp [v11455, v11456, v11994, v11995, v11816, v11817, v11996, v11997, v11998, v11999, v12000, v12001, reset, Ne.symm other]
theorem dut_register_write_19 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 19)
    (write : v11462 s i = 1) :
    (step s i).g40.r1305_nbackend_5Fisu_5Frf_5F19 = v11842 s i := by
  change v12001 s i = v11842 s i
  simp [v11455, v11456, v11994, v11995, v11816, v11817, v11996, v11997, v11998, v11999, v12000, v12001, reset, dest, write]
theorem dut_register_frame_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 20) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = s.g40.r1306_nbackend_5Fisu_5Frf_5F20 := by
  change v12009 s i = s.g40.r1306_nbackend_5Fisu_5Frf_5F20
  simp [v11455, v11456, v12002, v12003, v11816, v11817, v12004, v12005, v12006, v12007, v12008, v12009, reset, Ne.symm other]
theorem dut_register_write_20 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 20)
    (write : v11462 s i = 1) :
    (step s i).g40.r1306_nbackend_5Fisu_5Frf_5F20 = v11842 s i := by
  change v12009 s i = v11842 s i
  simp [v11455, v11456, v12002, v12003, v11816, v11817, v12004, v12005, v12006, v12007, v12008, v12009, reset, dest, write]
theorem dut_register_frame_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 21) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = s.g40.r1307_nbackend_5Fisu_5Frf_5F21 := by
  change v12017 s i = s.g40.r1307_nbackend_5Fisu_5Frf_5F21
  simp [v11455, v11456, v12010, v12011, v11816, v11817, v12012, v12013, v12014, v12015, v12016, v12017, reset, Ne.symm other]
theorem dut_register_write_21 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 21)
    (write : v11462 s i = 1) :
    (step s i).g40.r1307_nbackend_5Fisu_5Frf_5F21 = v11842 s i := by
  change v12017 s i = v11842 s i
  simp [v11455, v11456, v12010, v12011, v11816, v11817, v12012, v12013, v12014, v12015, v12016, v12017, reset, dest, write]
theorem dut_register_frame_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 22) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = s.g40.r1308_nbackend_5Fisu_5Frf_5F22 := by
  change v12025 s i = s.g40.r1308_nbackend_5Fisu_5Frf_5F22
  simp [v11455, v11456, v12018, v12019, v11816, v11817, v12020, v12021, v12022, v12023, v12024, v12025, reset, Ne.symm other]
theorem dut_register_write_22 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 22)
    (write : v11462 s i = 1) :
    (step s i).g40.r1308_nbackend_5Fisu_5Frf_5F22 = v11842 s i := by
  change v12025 s i = v11842 s i
  simp [v11455, v11456, v12018, v12019, v11816, v11817, v12020, v12021, v12022, v12023, v12024, v12025, reset, dest, write]
theorem dut_register_frame_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 23) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = s.g40.r1309_nbackend_5Fisu_5Frf_5F23 := by
  change v12033 s i = s.g40.r1309_nbackend_5Fisu_5Frf_5F23
  simp [v11455, v11456, v12026, v12027, v11816, v11817, v12028, v12029, v12030, v12031, v12032, v12033, reset, Ne.symm other]
theorem dut_register_write_23 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 23)
    (write : v11462 s i = 1) :
    (step s i).g40.r1309_nbackend_5Fisu_5Frf_5F23 = v11842 s i := by
  change v12033 s i = v11842 s i
  simp [v11455, v11456, v12026, v12027, v11816, v11817, v12028, v12029, v12030, v12031, v12032, v12033, reset, dest, write]
theorem dut_register_frame_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 24) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = s.g40.r1310_nbackend_5Fisu_5Frf_5F24 := by
  change v12041 s i = s.g40.r1310_nbackend_5Fisu_5Frf_5F24
  simp [v11455, v11456, v12034, v12035, v11816, v11817, v12036, v12037, v12038, v12039, v12040, v12041, reset, Ne.symm other]
theorem dut_register_write_24 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 24)
    (write : v11462 s i = 1) :
    (step s i).g40.r1310_nbackend_5Fisu_5Frf_5F24 = v11842 s i := by
  change v12041 s i = v11842 s i
  simp [v11455, v11456, v12034, v12035, v11816, v11817, v12036, v12037, v12038, v12039, v12040, v12041, reset, dest, write]
theorem dut_register_frame_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 25) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = s.g40.r1311_nbackend_5Fisu_5Frf_5F25 := by
  change v12049 s i = s.g40.r1311_nbackend_5Fisu_5Frf_5F25
  simp [v11455, v11456, v12042, v12043, v11816, v11817, v12044, v12045, v12046, v12047, v12048, v12049, reset, Ne.symm other]
theorem dut_register_write_25 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 25)
    (write : v11462 s i = 1) :
    (step s i).g40.r1311_nbackend_5Fisu_5Frf_5F25 = v11842 s i := by
  change v12049 s i = v11842 s i
  simp [v11455, v11456, v12042, v12043, v11816, v11817, v12044, v12045, v12046, v12047, v12048, v12049, reset, dest, write]
theorem dut_register_frame_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 26) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = s.g41.r1312_nbackend_5Fisu_5Frf_5F26 := by
  change v12057 s i = s.g41.r1312_nbackend_5Fisu_5Frf_5F26
  simp [v11455, v11456, v12050, v12051, v11816, v11817, v12052, v12053, v12054, v12055, v12056, v12057, reset, Ne.symm other]
theorem dut_register_write_26 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 26)
    (write : v11462 s i = 1) :
    (step s i).g41.r1312_nbackend_5Fisu_5Frf_5F26 = v11842 s i := by
  change v12057 s i = v11842 s i
  simp [v11455, v11456, v12050, v12051, v11816, v11817, v12052, v12053, v12054, v12055, v12056, v12057, reset, dest, write]
theorem dut_register_frame_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 27) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = s.g41.r1313_nbackend_5Fisu_5Frf_5F27 := by
  change v12065 s i = s.g41.r1313_nbackend_5Fisu_5Frf_5F27
  simp [v11455, v11456, v12058, v12059, v11816, v11817, v12060, v12061, v12062, v12063, v12064, v12065, reset, Ne.symm other]
theorem dut_register_write_27 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 27)
    (write : v11462 s i = 1) :
    (step s i).g41.r1313_nbackend_5Fisu_5Frf_5F27 = v11842 s i := by
  change v12065 s i = v11842 s i
  simp [v11455, v11456, v12058, v12059, v11816, v11817, v12060, v12061, v12062, v12063, v12064, v12065, reset, dest, write]
theorem dut_register_frame_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 28) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = s.g41.r1314_nbackend_5Fisu_5Frf_5F28 := by
  change v12073 s i = s.g41.r1314_nbackend_5Fisu_5Frf_5F28
  simp [v11455, v11456, v12066, v12067, v11816, v11817, v12068, v12069, v12070, v12071, v12072, v12073, reset, Ne.symm other]
theorem dut_register_write_28 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 28)
    (write : v11462 s i = 1) :
    (step s i).g41.r1314_nbackend_5Fisu_5Frf_5F28 = v11842 s i := by
  change v12073 s i = v11842 s i
  simp [v11455, v11456, v12066, v12067, v11816, v11817, v12068, v12069, v12070, v12071, v12072, v12073, reset, dest, write]
theorem dut_register_frame_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 29) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = s.g41.r1315_nbackend_5Fisu_5Frf_5F29 := by
  change v12081 s i = s.g41.r1315_nbackend_5Fisu_5Frf_5F29
  simp [v11455, v11456, v12074, v12075, v11816, v11817, v12076, v12077, v12078, v12079, v12080, v12081, reset, Ne.symm other]
theorem dut_register_write_29 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 29)
    (write : v11462 s i = 1) :
    (step s i).g41.r1315_nbackend_5Fisu_5Frf_5F29 = v11842 s i := by
  change v12081 s i = v11842 s i
  simp [v11455, v11456, v12074, v12075, v11816, v11817, v12076, v12077, v12078, v12079, v12080, v12081, reset, dest, write]
theorem dut_register_frame_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 30) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = s.g41.r1316_nbackend_5Fisu_5Frf_5F30 := by
  change v12089 s i = s.g41.r1316_nbackend_5Fisu_5Frf_5F30
  simp [v11455, v11456, v12082, v12083, v11816, v11817, v12084, v12085, v12086, v12087, v12088, v12089, reset, Ne.symm other]
theorem dut_register_write_30 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 30)
    (write : v11462 s i = 1) :
    (step s i).g41.r1316_nbackend_5Fisu_5Frf_5F30 = v11842 s i := by
  change v12089 s i = v11842 s i
  simp [v11455, v11456, v12082, v12083, v11816, v11817, v12084, v12085, v12086, v12087, v12088, v12089, reset, dest, write]
theorem dut_register_frame_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (other : v11465 s i ≠ BitVec.ofNat 5 31) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = s.g41.r1317_nbackend_5Fisu_5Frf_5F31 := by
  change v12097 s i = s.g41.r1317_nbackend_5Fisu_5Frf_5F31
  simp [v11455, v11456, v12090, v12091, v11816, v11817, v12092, v12093, v12094, v12095, v12096, v12097, reset, Ne.symm other]
theorem dut_register_write_31 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (dest : v11465 s i = BitVec.ofNat 5 31)
    (write : v11462 s i = 1) :
    (step s i).g41.r1317_nbackend_5Fisu_5Frf_5F31 = v11842 s i := by
  change v12097 s i = v11842 s i
  simp [v11455, v11456, v12090, v12091, v11816, v11817, v12092, v12093, v12094, v12095, v12096, v12097, reset, dest, write]
#print axioms dut_register_frame_31
#print axioms dut_register_write_31
end NutShellProofs
