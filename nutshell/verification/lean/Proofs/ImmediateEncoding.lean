import Proofs.SignExtension
namespace NutShellProofs
open nNutCore

def immediateI (instr : BitVec 64) : BitVec 64 :=
  (BitVec.extractLsb' 20 12 instr).signExtend 64

def immediateS (instr : BitVec 64) : BitVec 64 :=
  ((BitVec.extractLsb' 25 7 instr) ++ (BitVec.extractLsb' 7 5 instr)).signExtend 64

def immediateB (instr : BitVec 64) : BitVec 64 :=
  ((((BitVec.extractLsb' 31 1 instr ++ BitVec.extractLsb' 7 1 instr) ++
    BitVec.extractLsb' 25 6 instr) ++ (BitVec.extractLsb' 8 4 instr ++ (0 : BitVec 1))) : BitVec 13).signExtend 64

def immediateU (instr : BitVec 64) : BitVec 64 :=
  (BitVec.extractLsb' 12 20 instr ++ (0 : BitVec 12)).signExtend 64

def immediateJ (instr : BitVec 64) : BitVec 64 :=
  ((((BitVec.extractLsb' 31 1 instr ++ BitVec.extractLsb' 12 8 instr) ++
    BitVec.extractLsb' 20 1 instr) ++ (BitVec.extractLsb' 21 10 instr ++ (0 : BitVec 1))) : BitVec 21).signExtend 64


theorem idu_immediate_0_i (s : State) (i : Inputs) (format : v26897 s i = 4) :
    v29154 s i = immediateI (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateI (v26210 s i)
  unfold immediateI
  exact sign_extend_replication _ 52
#print axioms idu_immediate_0_i

theorem idu_immediate_0_s (s : State) (i : Inputs) (format : v26897 s i = 2) :
    v29154 s i = immediateS (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateS (v26210 s i)
  unfold immediateS
  exact sign_extend_replication _ 52
#print axioms idu_immediate_0_s

theorem idu_immediate_0_s_alt (s : State) (i : Inputs) (format : v26897 s i = 15) :
    v29154 s i = immediateS (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateS (v26210 s i)
  unfold immediateS
  exact sign_extend_replication _ 52
#print axioms idu_immediate_0_s_alt

theorem idu_immediate_0_b (s : State) (i : Inputs) (format : v26897 s i = 1) :
    v29154 s i = immediateB (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateB (v26210 s i)
  unfold immediateB
  exact sign_extend_replication _ 51
#print axioms idu_immediate_0_b

theorem idu_immediate_0_u (s : State) (i : Inputs) (format : v26897 s i = 6) :
    v29154 s i = immediateU (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateU (v26210 s i)
  unfold immediateU
  exact sign_extend_replication _ 32
#print axioms idu_immediate_0_u

theorem idu_immediate_0_j (s : State) (i : Inputs) (format : v26897 s i = 7) :
    v29154 s i = immediateJ (v26210 s i) := by
  simp [v29154, v29153, v29152, v29151, v29135, v29125, v29109, v29099, v29088, v29082, v29081, v29086, v29085, v29084, v29083, v15835, v9860, v29087, v29098, v29090, v29089, v29096, v29095, v29094, v29093, v29091, v29092, v29097, v29108, v29100, v15, v29106, v29105, v29104, v29103, v29101, v29102, v29107, v29124, v29111, v29110, v29122, v29121, v29120, v29119, v29116, v29114, v29112, v29113, v29115, v29118, v29117, v24, v16018, v16019, v29123, v29134, v29127, v29126, v29132, v29131, v29130, v29129, v29128, v10038, v11488, v11103, v29133, v29150, v29137, v29136, v29148, v29147, v29146, v29145, v29142, v29140, v29138, v29139, v29141, v29144, v29143, v16075, v16076, v29149, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateJ (v26210 s i)
  unfold immediateJ
  exact sign_extend_replication _ 43
#print axioms idu_immediate_0_j

theorem idu_immediate_1_i (s : State) (i : Inputs) (format : v27424 s i = 4) :
    v29230 s i = immediateI (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateI (v26223 s i)
  unfold immediateI
  exact sign_extend_replication _ 52
#print axioms idu_immediate_1_i

theorem idu_immediate_1_s (s : State) (i : Inputs) (format : v27424 s i = 2) :
    v29230 s i = immediateS (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateS (v26223 s i)
  unfold immediateS
  exact sign_extend_replication _ 52
#print axioms idu_immediate_1_s

theorem idu_immediate_1_s_alt (s : State) (i : Inputs) (format : v27424 s i = 15) :
    v29230 s i = immediateS (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateS (v26223 s i)
  unfold immediateS
  exact sign_extend_replication _ 52
#print axioms idu_immediate_1_s_alt

theorem idu_immediate_1_b (s : State) (i : Inputs) (format : v27424 s i = 1) :
    v29230 s i = immediateB (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateB (v26223 s i)
  unfold immediateB
  exact sign_extend_replication _ 51
#print axioms idu_immediate_1_b

theorem idu_immediate_1_u (s : State) (i : Inputs) (format : v27424 s i = 6) :
    v29230 s i = immediateU (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateU (v26223 s i)
  unfold immediateU
  exact sign_extend_replication _ 32
#print axioms idu_immediate_1_u

theorem idu_immediate_1_j (s : State) (i : Inputs) (format : v27424 s i = 7) :
    v29230 s i = immediateJ (v26223 s i) := by
  simp [v29230, v29229, v29228, v29227, v29211, v29201, v29185, v29175, v29164, v29158, v29157, v29162, v29161, v29160, v29159, v15835, v9860, v29163, v29174, v29166, v29165, v29172, v29171, v29170, v29169, v29167, v29168, v29173, v29184, v29176, v15, v29182, v29181, v29180, v29179, v29177, v29178, v29183, v29200, v29187, v29186, v29198, v29197, v29196, v29195, v29192, v29190, v29188, v29189, v29191, v29194, v29193, v24, v16018, v16019, v29199, v29210, v29203, v29202, v29208, v29207, v29206, v29205, v29204, v10038, v11488, v11103, v29209, v29226, v29213, v29212, v29224, v29223, v29222, v29221, v29218, v29216, v29214, v29215, v29217, v29220, v29219, v16075, v16076, v29225, format]
  try simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  try simp only [BitVec.or_zero, BitVec.zero_or]
  change _ = immediateJ (v26223 s i)
  unfold immediateJ
  exact sign_extend_replication _ 43
#print axioms idu_immediate_1_j
end NutShellProofs
