import Proofs.RegisterCommitReduction
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
private theorem destination_v1280 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1280 s i = v701 s i := by
  simp only [v1277, v1278, v1279, v1280, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1281 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1281 s i = 0 ∨ v1281 s i = v701 s i := by
  simp only [v1281]
  split
  · exact Or.inr (destination_v1280 s i commit)
  · exact Or.inl rfl
private theorem destination_v1272 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1272 s i = v701 s i := by
  simp only [v1269, v1270, v1271, v1272, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1282 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1282 s i = 0 ∨ v1282 s i = v701 s i := by
  simp only [v1282]
  split
  · exact Or.inr (destination_v1272 s i commit)
  · exact destination_v1281 s i commit
private theorem destination_v1264 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1264 s i = v701 s i := by
  simp only [v1261, v1262, v1263, v1264, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1283 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1283 s i = 0 ∨ v1283 s i = v701 s i := by
  simp only [v1283]
  split
  · exact Or.inr (destination_v1264 s i commit)
  · exact destination_v1282 s i commit
private theorem destination_v1256 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1256 s i = v701 s i := by
  simp only [v1253, v1254, v1255, v1256, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1284 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1284 s i = 0 ∨ v1284 s i = v701 s i := by
  simp only [v1284]
  split
  · exact Or.inr (destination_v1256 s i commit)
  · exact destination_v1283 s i commit
private theorem destination_v1248 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1248 s i = v701 s i := by
  simp only [v1245, v1246, v1247, v1248, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1285 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1285 s i = 0 ∨ v1285 s i = v701 s i := by
  simp only [v1285]
  split
  · exact Or.inr (destination_v1248 s i commit)
  · exact destination_v1284 s i commit
private theorem destination_v1240 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1240 s i = v701 s i := by
  simp only [v1237, v1238, v1239, v1240, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1286 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1286 s i = 0 ∨ v1286 s i = v701 s i := by
  simp only [v1286]
  split
  · exact Or.inr (destination_v1240 s i commit)
  · exact destination_v1285 s i commit
private theorem destination_v1232 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1232 s i = v701 s i := by
  simp only [v1229, v1230, v1231, v1232, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1287 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1287 s i = 0 ∨ v1287 s i = v701 s i := by
  simp only [v1287]
  split
  · exact Or.inr (destination_v1232 s i commit)
  · exact destination_v1286 s i commit
private theorem destination_v1225 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1225 s i = v701 s i := by
  simp only [v1222, v1223, v1224, v1225, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1288 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1288 s i = 0 ∨ v1288 s i = v701 s i := by
  simp only [v1288]
  split
  · exact Or.inr (destination_v1225 s i commit)
  · exact destination_v1287 s i commit
private theorem destination_v1218 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1218 s i = v701 s i := by
  simp only [v1215, v1216, v1217, v1218, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1289 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1289 s i = 0 ∨ v1289 s i = v701 s i := by
  simp only [v1289]
  split
  · exact Or.inr (destination_v1218 s i commit)
  · exact destination_v1288 s i commit
private theorem destination_v1211 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1211 s i = v701 s i := by
  simp only [v1210, v1211, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1290 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1290 s i = 0 ∨ v1290 s i = v701 s i := by
  simp only [v1290]
  split
  · exact Or.inr (destination_v1211 s i commit)
  · exact destination_v1289 s i commit
private theorem destination_v1205 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1205 s i = v701 s i := by
  simp only [v1204, v1205, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1291 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1291 s i = 0 ∨ v1291 s i = v701 s i := by
  simp only [v1291]
  split
  · exact Or.inr (destination_v1205 s i commit)
  · exact destination_v1290 s i commit
private theorem destination_v1199 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1199 s i = v701 s i := by
  simp only [v1195, v1196, v1197, v1198, v1199, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1292 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1292 s i = 0 ∨ v1292 s i = v701 s i := by
  simp only [v1292]
  split
  · exact Or.inr (destination_v1199 s i commit)
  · exact destination_v1291 s i commit
private theorem destination_v1191 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1191 s i = v701 s i := by
  simp only [v1187, v1188, v1189, v1190, v1191, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1293 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1293 s i = 0 ∨ v1293 s i = v701 s i := by
  simp only [v1293]
  split
  · exact Or.inr (destination_v1191 s i commit)
  · exact destination_v1292 s i commit
private theorem destination_v1183 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1183 s i = v701 s i := by
  simp only [v1179, v1180, v1181, v1182, v1183, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1294 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1294 s i = 0 ∨ v1294 s i = v701 s i := by
  simp only [v1294]
  split
  · exact Or.inr (destination_v1183 s i commit)
  · exact destination_v1293 s i commit
private theorem destination_v1175 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1175 s i = v701 s i := by
  simp only [v1171, v1172, v1173, v1174, v1175, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1295 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1295 s i = 0 ∨ v1295 s i = v701 s i := by
  simp only [v1295]
  split
  · exact Or.inr (destination_v1175 s i commit)
  · exact destination_v1294 s i commit
private theorem destination_v1167 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1167 s i = v701 s i := by
  simp only [v1163, v1164, v1165, v1166, v1167, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1296 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1296 s i = 0 ∨ v1296 s i = v701 s i := by
  simp only [v1296]
  split
  · exact Or.inr (destination_v1167 s i commit)
  · exact destination_v1295 s i commit
private theorem destination_v1159 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1159 s i = v701 s i := by
  simp only [v1155, v1156, v1157, v1158, v1159, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1297 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1297 s i = 0 ∨ v1297 s i = v701 s i := by
  simp only [v1297]
  split
  · exact Or.inr (destination_v1159 s i commit)
  · exact destination_v1296 s i commit
private theorem destination_v1151 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1151 s i = v701 s i := by
  simp only [v1147, v1148, v1149, v1150, v1151, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1298 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1298 s i = 0 ∨ v1298 s i = v701 s i := by
  simp only [v1298]
  split
  · exact Or.inr (destination_v1151 s i commit)
  · exact destination_v1297 s i commit
private theorem destination_v1143 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1143 s i = v701 s i := by
  simp only [v1139, v1140, v1141, v1142, v1143, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1299 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1299 s i = 0 ∨ v1299 s i = v701 s i := by
  simp only [v1299]
  split
  · exact Or.inr (destination_v1143 s i commit)
  · exact destination_v1298 s i commit
private theorem destination_v1135 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1135 s i = v701 s i := by
  simp only [v1131, v1132, v1133, v1134, v1135, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1300 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1300 s i = 0 ∨ v1300 s i = v701 s i := by
  simp only [v1300]
  split
  · exact Or.inr (destination_v1135 s i commit)
  · exact destination_v1299 s i commit
private theorem destination_v1127 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1127 s i = v701 s i := by
  simp only [v1123, v1124, v1125, v1126, v1127, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1301 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1301 s i = 0 ∨ v1301 s i = v701 s i := by
  simp only [v1301]
  split
  · exact Or.inr (destination_v1127 s i commit)
  · exact destination_v1300 s i commit
private theorem destination_v1119 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1119 s i = v701 s i := by
  simp only [v1115, v1116, v1117, v1118, v1119, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1302 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1302 s i = 0 ∨ v1302 s i = v701 s i := by
  simp only [v1302]
  split
  · exact Or.inr (destination_v1119 s i commit)
  · exact destination_v1301 s i commit
private theorem destination_v1110 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1110 s i = v701 s i := by
  simp only [v1107, v1108, v1109, v1110, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1303 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1303 s i = 0 ∨ v1303 s i = v701 s i := by
  simp only [v1303]
  split
  · exact Or.inr (destination_v1110 s i commit)
  · exact destination_v1302 s i commit
private theorem destination_v1102 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1102 s i = v701 s i := by
  simp only [v1099, v1100, v1101, v1102, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1304 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1304 s i = 0 ∨ v1304 s i = v701 s i := by
  simp only [v1304]
  split
  · exact Or.inr (destination_v1102 s i commit)
  · exact destination_v1303 s i commit
private theorem destination_v1094 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1094 s i = v701 s i := by
  simp only [v1091, v1092, v1093, v1094, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1305 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1305 s i = 0 ∨ v1305 s i = v701 s i := by
  simp only [v1305]
  split
  · exact Or.inr (destination_v1094 s i commit)
  · exact destination_v1304 s i commit
private theorem destination_v1086 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1086 s i = v701 s i := by
  simp only [v1083, v1084, v1085, v1086, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1306 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1306 s i = 0 ∨ v1306 s i = v701 s i := by
  simp only [v1306]
  split
  · exact Or.inr (destination_v1086 s i commit)
  · exact destination_v1305 s i commit
private theorem destination_v1078 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1078 s i = v701 s i := by
  simp only [v1075, v1076, v1077, v1078, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1307 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1307 s i = 0 ∨ v1307 s i = v701 s i := by
  simp only [v1307]
  split
  · exact Or.inr (destination_v1078 s i commit)
  · exact destination_v1306 s i commit
private theorem destination_v1070 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1070 s i = v701 s i := by
  simp only [v1067, v1068, v1069, v1070, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1308 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1308 s i = 0 ∨ v1308 s i = v701 s i := by
  simp only [v1308]
  split
  · exact Or.inr (destination_v1070 s i commit)
  · exact destination_v1307 s i commit
private theorem destination_v1062 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1062 s i = v701 s i := by
  simp only [v1059, v1060, v1061, v1062, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1309 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1309 s i = 0 ∨ v1309 s i = v701 s i := by
  simp only [v1309]
  split
  · exact Or.inr (destination_v1062 s i commit)
  · exact destination_v1308 s i commit
private theorem destination_v1056 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1056 s i = v701 s i := by
  simp only [v1053, v1054, v1055, v1056, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1310 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1310 s i = 0 ∨ v1310 s i = v701 s i := by
  simp only [v1310]
  split
  · exact Or.inr (destination_v1056 s i commit)
  · exact destination_v1309 s i commit
private theorem destination_v1050 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1050 s i = v701 s i := by
  simp only [v1047, v1048, v1049, v1050, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1311 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1311 s i = 0 ∨ v1311 s i = v701 s i := by
  simp only [v1311]
  split
  · exact Or.inr (destination_v1050 s i commit)
  · exact destination_v1310 s i commit
private theorem destination_v1042 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1042 s i = v701 s i := by
  simp only [v1038, v1039, v1040, v1041, v1042, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1312 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1312 s i = 0 ∨ v1312 s i = v701 s i := by
  simp only [v1312]
  split
  · exact Or.inr (destination_v1042 s i commit)
  · exact destination_v1311 s i commit
private theorem destination_v1034 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1034 s i = v701 s i := by
  simp only [v1030, v1031, v1032, v1033, v1034, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1313 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1313 s i = 0 ∨ v1313 s i = v701 s i := by
  simp only [v1313]
  split
  · exact Or.inr (destination_v1034 s i commit)
  · exact destination_v1312 s i commit
private theorem destination_v1026 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1026 s i = v701 s i := by
  simp only [v1022, v1023, v1024, v1025, v1026, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1314 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1314 s i = 0 ∨ v1314 s i = v701 s i := by
  simp only [v1314]
  split
  · exact Or.inr (destination_v1026 s i commit)
  · exact destination_v1313 s i commit
private theorem destination_v1018 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1018 s i = v701 s i := by
  simp only [v1014, v1015, v1016, v1017, v1018, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1315 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1315 s i = 0 ∨ v1315 s i = v701 s i := by
  simp only [v1315]
  split
  · exact Or.inr (destination_v1018 s i commit)
  · exact destination_v1314 s i commit
private theorem destination_v1010 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1010 s i = v701 s i := by
  simp only [v1006, v1007, v1008, v1009, v1010, v973, v974, v975, v976, v977, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1316 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1316 s i = 0 ∨ v1316 s i = v701 s i := by
  simp only [v1316]
  split
  · exact Or.inr (destination_v1010 s i commit)
  · exact destination_v1315 s i commit
private theorem destination_v1002 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1002 s i = v701 s i := by
  simp only [v1000, v1001, v1002, v973, v974, v975, v976, v977, v998, v999, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1317 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1317 s i = 0 ∨ v1317 s i = v701 s i := by
  simp only [v1317]
  split
  · exact Or.inr (destination_v1002 s i commit)
  · exact destination_v1316 s i commit
private theorem destination_v994 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v994 s i = v701 s i := by
  simp only [v973, v974, v975, v976, v977, v990, v991, v992, v993, v994, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1318 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1318 s i = 0 ∨ v1318 s i = v701 s i := by
  simp only [v1318]
  split
  · exact Or.inr (destination_v994 s i commit)
  · exact destination_v1317 s i commit
private theorem destination_v986 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v986 s i = v701 s i := by
  simp only [v973, v974, v975, v976, v977, v982, v983, v984, v985, v986, v701, commit, if_true]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega,
    show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 31 by omega, show 7+j < 25 by omega]
private theorem destination_v1319 (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v1319 s i = 0 ∨ v1319 s i = v701 s i := by
  simp only [v1319]
  split
  · exact Or.inr (destination_v986 s i commit)
  · exact destination_v1318 s i commit
theorem reference_destination_alignment (s : State) (i : Inputs)
    (commit : v964 s i = 1) : v1320 s i = 0 ∨ v1320 s i = v701 s i := by
  simpa only [v1320, commit, if_true] using destination_v1319 s i commit

theorem register_tasks_of_written_value (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0)
    (commit : v964 s i = 1)
    (written : dutRead (step s i) (v701 s i) =
      referenceRead (step s i) (v701 s i)) : RegisterTasks s i :=
  register_tasks_of_destination s i agree reset commit
    (reference_destination_alignment s i commit) written
theorem register_tasks_iff_written_value (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0) (commit : v964 s i = 1) :
    RegisterTasks s i ↔ dutRead (step s i) (v701 s i) =
      referenceRead (step s i) (v701 s i) := by
  constructor
  · intro tasks
    exact register_reads_agree _ ((register_tasks_iff_next s i reset commit).mp tasks) _
  · exact register_tasks_of_written_value s i agree reset commit

theorem register_tasks_rd_zero (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0) (commit : v964 s i = 1)
    (destination_zero : v701 s i = 0) : RegisterTasks s i := by
  apply register_tasks_of_written_value s i agree reset commit
  simp [destination_zero, dutRead, referenceRead]

#print axioms register_tasks_rd_zero
#print axioms register_tasks_iff_written_value
#print axioms reference_destination_alignment
#print axioms register_tasks_of_written_value
end RiscvMiniProofs
