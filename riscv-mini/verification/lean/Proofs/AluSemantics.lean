import Proofs.AluCone
import Proofs.ShiftFacts
import Proofs.ReverseNetwork
set_option linter.unusedSimpArgs false
namespace RiscvMiniProofs
-- Unfolding the extracted cone keeps the original generated semantics.
private theorem zero_append_nat {n w : Nat} (x : BitVec w) : ((0#n) ++ x).toNat = x.toNat := by
  simp only [BitVec.toNat_append]
  simp

theorem circuit_alu_add (a b : BitVec 32) : circuitAlu 0 a b = a + b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg]
  all_goals omega
#print axioms circuit_alu_add

theorem circuit_alu_sub (a b : BitVec 32) : circuitAlu 1 a b = a - b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg]
  all_goals omega
#print axioms circuit_alu_sub

theorem circuit_alu_and (a b : BitVec 32) : circuitAlu 2 a b = a &&& b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
#print axioms circuit_alu_and

theorem circuit_alu_or (a b : BitVec 32) : circuitAlu 3 a b = a ||| b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
#print axioms circuit_alu_or

theorem circuit_alu_xor (a b : BitVec 32) : circuitAlu 4 a b = a ^^^ b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
#print axioms circuit_alu_xor

theorem circuit_alu_copy_a (a b : BitVec 32) : circuitAlu 10 a b = a := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
#print axioms circuit_alu_copy_a

theorem circuit_alu_copy_b (a b : BitVec 32) : circuitAlu 11 a b = b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
#print axioms circuit_alu_copy_b

theorem circuit_alu_slt (a b : BitVec 32) : circuitAlu 5 a b = (if a.toInt < b.toInt then 1 else 0) := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_eq, zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond]
  simp only [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), apply_ite, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.reducePow, Nat.zero_shiftRight, Nat.zero_or, Nat.reduceAdd]
  repeat' split
  all_goals try simp only [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.shiftRight_zero]
  all_goals omega
#print axioms circuit_alu_slt

theorem circuit_alu_sltu (a b : BitVec 32) : circuitAlu 7 a b = (if a.toNat < b.toNat then 1 else 0) := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_eq, zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond]
  simp only [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), apply_ite, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.reducePow, Nat.zero_shiftRight, Nat.zero_or, Nat.reduceAdd]
  repeat' split
  all_goals try simp only [zero_append_nat (n := 1) (w := 32), zero_append_nat (n := 31) (w := 1), BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_neg, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.shiftRight_zero]
  all_goals omega
#print axioms circuit_alu_sltu

theorem circuit_alu_srl (a b : BitVec 32) : circuitAlu 8 a b = a.ushiftRight (BitVec.extractLsb' 0 5 b).toNat := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  simp only [zero_append_nat (n := 28) (w := 5)]
  skip
  exact zero_extend_shift_extract a _
#print axioms circuit_alu_srl

theorem circuit_alu_sra (a b : BitVec 32) : circuitAlu 9 a b = a.sshiftRight (BitVec.extractLsb' 0 5 b).toNat := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
  simp only [zero_append_nat (n := 28) (w := 5)]
  have bit : (1#1 &&& BitVec.extractLsb' 31 1 a) = BitVec.extractLsb' 31 1 a := one_and_bit _
  rw [bit]
  exact sign_extend_shift_extract a _
#print axioms circuit_alu_sra

theorem circuit_alu_sll (a b : BitVec 32) : circuitAlu 6 a b = a.shiftLeft (BitVec.extractLsb' 0 5 b).toNat := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164, input_reverse_network, output_reverse_network]
  simp only [zero_append_nat (n := 28) (w := 5)]
  rw [zero_extend_shift_extract]
  exact reverse_right_reverse a _
#print axioms circuit_alu_sll

theorem circuit_alu_default_12 (a b : BitVec 32) : circuitAlu 12 a b = b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
theorem circuit_alu_default_13 (a b : BitVec 32) : circuitAlu 13 a b = b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
theorem circuit_alu_default_14 (a b : BitVec 32) : circuitAlu 14 a b = b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]
theorem circuit_alu_default_15 (a b : BitVec 32) : circuitAlu 15 a b = b := by
  simp [circuitAlu, alu_v725, alu_v7841, alu_v7793, alu_v7842, alu_v7843, alu_v4, alu_v7890, alu_v7891, alu_v7892, alu_v8035, alu_v8036, alu_v8037, alu_v8038, alu_v8039, alu_v8040, alu_v8041, alu_v7785, alu_v8042, alu_v7786, alu_v8043, alu_v8044, alu_v2274, alu_v8045, alu_v8046, alu_v8047, alu_v8048, alu_v8049, alu_v8050, alu_v8051, alu_v8052, alu_v8053, alu_v8054, alu_v7792, alu_v8055, alu_v7791, alu_v8056, alu_v8057, alu_v8058, alu_v8059, alu_v32, alu_v2012, alu_v2100, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, alu_v8105, alu_v8106, alu_v8107, alu_v8108, alu_v608, alu_v8109, alu_v8110, alu_v8111, alu_v8112, alu_v7790, alu_v8113, alu_v8114, alu_v8115, alu_v8116, alu_v8117, alu_v8118, alu_v8119, alu_v8120, alu_v8121, alu_v8122, alu_v8123, alu_v8124, alu_v8125, alu_v8126, alu_v8127, alu_v8128, alu_v8129, alu_v8130, alu_v8131, alu_v8132, alu_v8133, alu_v8134, alu_v8135, alu_v8136, alu_v8137, alu_v8138, alu_v8139, alu_v8140, alu_v8141, alu_v8142, alu_v8143, alu_v8144, alu_v8145, alu_v8146, alu_v8147, alu_v8148, alu_v7789, alu_v8149, alu_v8150, alu_v7788, alu_v8151, alu_v8152, alu_v7787, alu_v8153, alu_v8154, alu_v7795, alu_v8155, alu_v8156, alu_v8157, alu_v8158, alu_v8159, alu_v8160, alu_v8161, alu_v8162, alu_v8163, alu_v8164]

-- Mathematical specification for every 4-bit ALU operation code.
def aluSpec (op : BitVec 4) (a b : BitVec 32) : BitVec 32 :=
  match op.toNat with
  | 0 => a + b
  | 1 => a - b
  | 2 => a &&& b
  | 3 => a ||| b
  | 4 => a ^^^ b
  | 5 => if a.toInt < b.toInt then 1 else 0
  | 6 => a.shiftLeft (BitVec.extractLsb' 0 5 b).toNat
  | 7 => if a.toNat < b.toNat then 1 else 0
  | 8 => a.ushiftRight (BitVec.extractLsb' 0 5 b).toNat
  | 9 => a.sshiftRight (BitVec.extractLsb' 0 5 b).toNat
  | 10 => a
  | _ => b

theorem circuit_alu_correct (op : BitVec 4) (a b : BitVec 32) :
    circuitAlu op a b = aluSpec op a b := by
  have bound := op.isLt
  have cases : op.toNat = 0 ∨ op.toNat = 1 ∨ op.toNat = 2 ∨ op.toNat = 3 ∨ op.toNat = 4 ∨ op.toNat = 5 ∨ op.toNat = 6 ∨ op.toNat = 7 ∨ op.toNat = 8 ∨ op.toNat = 9 ∨ op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12 ∨ op.toNat = 13 ∨ op.toNat = 14 ∨ op.toNat = 15 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have eq : op = 0 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_add a b
  · have eq : op = 1 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_sub a b
  · have eq : op = 2 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_and a b
  · have eq : op = 3 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_or a b
  · have eq : op = 4 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_xor a b
  · have eq : op = 5 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_slt a b
  · have eq : op = 6 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_sll a b
  · have eq : op = 7 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_sltu a b
  · have eq : op = 8 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_srl a b
  · have eq : op = 9 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_sra a b
  · have eq : op = 10 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_copy_a a b
  · have eq : op = 11 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_copy_b a b
  · have eq : op = 12 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_default_12 a b
  · have eq : op = 13 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_default_13 a b
  · have eq : op = 14 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_default_14 a b
  · have eq : op = 15 := BitVec.eq_of_toNat_eq h
    subst op
    exact circuit_alu_default_15 a b
#print axioms circuit_alu_correct
end RiscvMiniProofs
