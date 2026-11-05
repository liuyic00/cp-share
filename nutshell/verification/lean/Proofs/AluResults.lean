import Proofs.AluComparisons
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem alu_result_slt (s : State) (i : Inputs) (op : v28 s i = 2) :
    v25095 s i = (if (v12148 s i).toInt < (v12150 s i).toInt then 1 else 0) := by
  have cmp := alu_signed_compare_bit s i (by rw [op]; decide)
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, cmp, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_slt (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 2) :
    v11842 (step s i) next = (if (v12148 s i).toInt < (v12150 s i).toInt then 1 else 0) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_slt s i op
#print axioms writeback_alu_slt

theorem alu_result_sltu (s : State) (i : Inputs) (op : v28 s i = 3) :
    v25095 s i = (if (v12148 s i).toNat < (v12150 s i).toNat then 1 else 0) := by
  have cmp := alu_unsigned_compare_bit s i (by rw [op]; decide)
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, cmp, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_sltu (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 3) :
    v11842 (step s i) next = (if (v12148 s i).toNat < (v12150 s i).toNat then 1 else 0) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sltu s i op
#print axioms writeback_alu_sltu

theorem alu_result_add (s : State) (i : Inputs) (op : v28 s i = 64) :
    v25095 s i = (v12148 s i + v12150 s i) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_add (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 64) :
    v11842 (step s i) next = (v12148 s i + v12150 s i) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_add s i op
#print axioms writeback_alu_add

theorem alu_result_sub (s : State) (i : Inputs) (op : v28 s i = 8) :
    v25095 s i = (v12148 s i - v12150 s i) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_sub (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 8) :
    v11842 (step s i) next = (v12148 s i - v12150 s i) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sub s i op
#print axioms writeback_alu_sub

theorem alu_result_xor (s : State) (i : Inputs) (op : v28 s i = 4) :
    v25095 s i = (v12148 s i ^^^ v12150 s i) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_xor (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 4) :
    v11842 (step s i) next = (v12148 s i ^^^ v12150 s i) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_xor s i op
#print axioms writeback_alu_xor

theorem alu_result_or (s : State) (i : Inputs) (op : v28 s i = 6) :
    v25095 s i = (v12148 s i ||| v12150 s i) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_or (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 6) :
    v11842 (step s i) next = (v12148 s i ||| v12150 s i) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_or s i op
#print axioms writeback_alu_or

theorem alu_result_and (s : State) (i : Inputs) (op : v28 s i = 7) :
    v25095 s i = (v12148 s i &&& v12150 s i) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_and (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 7) :
    v11842 (step s i) next = (v12148 s i &&& v12150 s i) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_and s i op
#print axioms writeback_alu_and

theorem alu_result_sll (s : State) (i : Inputs) (op : v28 s i = 1) :
    v25095 s i = (BitVec.shiftLeft (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_sll (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 1) :
    v11842 (step s i) next = (BitVec.shiftLeft (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sll s i op
#print axioms writeback_alu_sll

theorem alu_result_srl (s : State) (i : Inputs) (op : v28 s i = 5) :
    v25095 s i = (BitVec.ushiftRight (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_srl (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 5) :
    v11842 (step s i) next = (BitVec.ushiftRight (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_srl s i op
#print axioms writeback_alu_srl

theorem alu_result_sra (s : State) (i : Inputs) (op : v28 s i = 13) :
    v25095 s i = (BitVec.sshiftRight (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  simp (disch := omega) [v25095, v25094, v25093, v12142, v12141, v25024, v24, v25023, v25008, v12193, v12192, v12191, v2750, v25015, v25014, v25012, v25011, v25010, v25009, v13804, v13805, v25013, v25022, v25021, v25019, v25018, v25017, v25016, v25020, v25092, v25025, v25091, v25090, v25089, v25088, v25087, v25086, v25027, v8300, v25026, v25047, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try simp (disch := omega) [BitVec.toNat_append, low_shiftLeft]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try (split <;> rfl)
  all_goals rw [BitVec.toNat_append]
  all_goals simp

theorem writeback_alu_sra (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 13) :
    v11842 (step s i) next = (BitVec.sshiftRight (v12148 s i) (BitVec.extractLsb' 0 6 (v12150 s i)).toNat) := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sra s i op
#print axioms writeback_alu_sra
end NutShellProofs
