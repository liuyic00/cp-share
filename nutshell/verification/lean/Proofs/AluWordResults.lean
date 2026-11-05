import Proofs.AluWordOutput
namespace NutShellProofs
open nNutCore
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem alu_word_core_addw (s : State) (i : Inputs) (op : v28 s i = 96) :
    BitVec.extractLsb' 0 64 (v25086 s i) = v12148 s i + v12150 s i := by
  simp (disch := omega) [v25086, v25027, v8300, v25026, v12141, v25047, v24, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try rw [sign_extend_word]
  all_goals try simp (disch := omega) [low_shiftLeft]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals repeat' rw [BitVec.toNat_append]
  all_goals try simp
  all_goals try rw [sign_extend_word]
  all_goals exact congrArg (fun x : BitVec 64 => x.sshiftRight ((v12150 s i).toNat % 32)) (sign_extend_word (BitVec.extractLsb' 0 32 (v12148 s i)))

theorem alu_result_addw (s : State) (i : Inputs) (op : v28 s i = 96) :
    v25095 s i = (BitVec.extractLsb' 0 32 (v12148 s i + v12150 s i)).signExtend 64 := by
  rw [alu_word_output s i (by rw [op]; decide) (by rw [op]; decide)]
  have low := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 32 x) (alu_word_core_addw s i op)
  dsimp only at low
  rw [low_low (n := 32) (m := 64) _ (by decide)] at low
  rw [low]

theorem writeback_alu_addw (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 96) :
    v11842 (step s i) next = (BitVec.extractLsb' 0 32 (v12148 s i + v12150 s i)).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_addw s i op
#print axioms writeback_alu_addw

theorem alu_word_core_subw (s : State) (i : Inputs) (op : v28 s i = 40) :
    BitVec.extractLsb' 0 64 (v25086 s i) = v12148 s i - v12150 s i := by
  simp (disch := omega) [v25086, v25027, v8300, v25026, v12141, v25047, v24, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try rw [sign_extend_word]
  all_goals try simp (disch := omega) [low_shiftLeft]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals repeat' rw [BitVec.toNat_append]
  all_goals try simp
  all_goals try rw [sign_extend_word]
  all_goals exact congrArg (fun x : BitVec 64 => x.sshiftRight ((v12150 s i).toNat % 32)) (sign_extend_word (BitVec.extractLsb' 0 32 (v12148 s i)))

theorem alu_result_subw (s : State) (i : Inputs) (op : v28 s i = 40) :
    v25095 s i = (BitVec.extractLsb' 0 32 (v12148 s i - v12150 s i)).signExtend 64 := by
  rw [alu_word_output s i (by rw [op]; decide) (by rw [op]; decide)]
  have low := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 32 x) (alu_word_core_subw s i op)
  dsimp only at low
  rw [low_low (n := 32) (m := 64) _ (by decide)] at low
  rw [low]

theorem writeback_alu_subw (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 40) :
    v11842 (step s i) next = (BitVec.extractLsb' 0 32 (v12148 s i - v12150 s i)).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_subw s i op
#print axioms writeback_alu_subw

theorem alu_word_core_sllw (s : State) (i : Inputs) (op : v28 s i = 33) :
    BitVec.extractLsb' 0 64 (v25086 s i) = BitVec.shiftLeft (v12148 s i) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat := by
  simp (disch := omega) [v25086, v25027, v8300, v25026, v12141, v25047, v24, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try rw [sign_extend_word]
  all_goals try simp (disch := omega) [low_shiftLeft]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals repeat' rw [BitVec.toNat_append]
  all_goals try simp
  all_goals try rw [sign_extend_word]
  all_goals exact congrArg (fun x : BitVec 64 => x.sshiftRight ((v12150 s i).toNat % 32)) (sign_extend_word (BitVec.extractLsb' 0 32 (v12148 s i)))

theorem alu_result_sllw (s : State) (i : Inputs) (op : v28 s i = 33) :
    v25095 s i = (BitVec.extractLsb' 0 32 (BitVec.shiftLeft (v12148 s i) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [alu_word_output s i (by rw [op]; decide) (by rw [op]; decide)]
  have low := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 32 x) (alu_word_core_sllw s i op)
  dsimp only at low
  rw [low_low (n := 32) (m := 64) _ (by decide)] at low
  rw [low]

theorem writeback_alu_sllw (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 33) :
    v11842 (step s i) next = (BitVec.extractLsb' 0 32 (BitVec.shiftLeft (v12148 s i) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sllw s i op
#print axioms writeback_alu_sllw

theorem alu_word_core_srlw (s : State) (i : Inputs) (op : v28 s i = 37) :
    BitVec.extractLsb' 0 64 (v25086 s i) = BitVec.ushiftRight ((0 : BitVec 32) ++ BitVec.extractLsb' 0 32 (v12148 s i)) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat := by
  simp (disch := omega) [v25086, v25027, v8300, v25026, v12141, v25047, v24, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try rw [sign_extend_word]
  all_goals try simp (disch := omega) [low_shiftLeft]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals repeat' rw [BitVec.toNat_append]
  all_goals try simp
  all_goals try rw [sign_extend_word]
  all_goals exact congrArg (fun x : BitVec 64 => x.sshiftRight ((v12150 s i).toNat % 32)) (sign_extend_word (BitVec.extractLsb' 0 32 (v12148 s i)))

theorem alu_result_srlw (s : State) (i : Inputs) (op : v28 s i = 37) :
    v25095 s i = (BitVec.extractLsb' 0 32 (BitVec.ushiftRight ((0 : BitVec 32) ++ BitVec.extractLsb' 0 32 (v12148 s i)) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [alu_word_output s i (by rw [op]; decide) (by rw [op]; decide)]
  have low := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 32 x) (alu_word_core_srlw s i op)
  dsimp only at low
  rw [low_low (n := 32) (m := 64) _ (by decide)] at low
  rw [low]

theorem writeback_alu_srlw (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 37) :
    v11842 (step s i) next = (BitVec.extractLsb' 0 32 (BitVec.ushiftRight ((0 : BitVec 32) ++ BitVec.extractLsb' 0 32 (v12148 s i)) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_srlw s i op
#print axioms writeback_alu_srlw

theorem alu_word_core_sraw (s : State) (i : Inputs) (op : v28 s i = 45) :
    BitVec.extractLsb' 0 64 (v25086 s i) = BitVec.sshiftRight ((BitVec.extractLsb' 0 32 (v12148 s i)).signExtend 64) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat := by
  simp (disch := omega) [v25086, v25027, v8300, v25026, v12141, v25047, v24, v25046, v25039, v25029, v25028, v25033, v25032, v25031, v25030, v11488, v11103, v25038, v25035, v25034, v25037, v25036, v25045, v11483, v25044, v25040, v25042, v25041, v25043, v25085, v25049, v25048, v25051, v25050, v25084, v25053, v25052, v25055, v25054, v25083, v25057, v25056, v25060, v25059, v25058, v25082, v25062, v25061, v25063, v12151, v25081, v25065, v25064, v25067, v25066, v12724, v25080, v25069, v25068, v25071, v25070, v25079, v25073, v25072, v25078, v25077, v25076, v25074, v25075, v16276, v12169, v12168, v12165, v12164, v12157, v12163, v12162, v12161, v12159, v12158, v12160, v4051, v12167, v12166, op, low_low, low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals try rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals simp (disch := omega) [low_add, BitVec.extractLsb'_append_eq_of_add_le]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals try exact twos_complement_sub _ _
  all_goals try rw [sign_extend_word]
  all_goals try simp (disch := omega) [low_shiftLeft]
  all_goals repeat' rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  all_goals try simp
  all_goals repeat' rw [BitVec.toNat_append]
  all_goals try simp
  all_goals try rw [sign_extend_word]
  all_goals exact congrArg (fun x : BitVec 64 => x.sshiftRight ((v12150 s i).toNat % 32)) (sign_extend_word (BitVec.extractLsb' 0 32 (v12148 s i)))

theorem alu_result_sraw (s : State) (i : Inputs) (op : v28 s i = 45) :
    v25095 s i = (BitVec.extractLsb' 0 32 (BitVec.sshiftRight ((BitVec.extractLsb' 0 32 (v12148 s i)).signExtend 64) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [alu_word_output s i (by rw [op]; decide) (by rw [op]; decide)]
  have low := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 32 x) (alu_word_core_sraw s i op)
  dsimp only at low
  rw [low_low (n := 32) (m := 64) _ (by decide)] at low
  rw [low]

theorem writeback_alu_sraw (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (op : v28 s i = 45) :
    v11842 (step s i) next = (BitVec.extractLsb' 0 32 (BitVec.sshiftRight ((BitVec.extractLsb' 0 32 (v12148 s i)).signExtend 64) (BitVec.extractLsb' 0 5 (v12150 s i)).toNat)).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sraw s i op
#print axioms writeback_alu_sraw
end NutShellProofs
