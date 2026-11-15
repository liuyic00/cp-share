From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Stable GlobalStable FrontCheck Booth8.
Local Open Scope N_scope.
Definition top_global_leaves (v:global_leaves) : Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_0 v
| 0, 1 => global_word_1 v
| 0, 2 => global_word_2 v
| 0, 3 => global_word_53 v
| 0, 4 => global_word_56 v
| 0, 5 => global_word_61 v
| 0, 201 => global_word_3 v
| 0, 203 => global_word_4 v
| 0, 205 => global_word_5 v
| 0, 207 => global_word_6 v
| 0, 209 => global_word_7 v
| 0, 211 => global_word_8 v
| 0, 213 => global_word_9 v
| 0, 215 => global_word_10 v
| 0, 217 => global_word_11 v
| 0, 219 => global_word_12 v
| 0, 221 => global_word_13 v
| 0, 223 => global_word_14 v
| 0, 225 => global_word_15 v
| 0, 227 => global_word_16 v
| 0, 229 => global_word_17 v
| 0, 231 => global_word_18 v
| 0, 233 => global_word_19 v
| 0, 235 => global_word_20 v
| 0, 237 => global_word_21 v
| 0, 239 => global_word_22 v
| 0, 241 => global_word_23 v
| 0, 243 => global_word_24 v
| 0, 245 => global_word_25 v
| 0, 247 => global_word_26 v
| 0, 249 => global_word_27 v
| 0, 251 => global_word_28 v
| 0, 253 => global_word_29 v
| 0, 255 => global_word_30 v
| 0, 257 => global_word_31 v
| 0, 259 => global_word_32 v
| 0, 261 => global_word_33 v
| 0, 263 => global_word_34 v
| 0, 265 => global_word_35 v
| 0, 267 => global_word_36 v
| 0, 269 => global_word_37 v
| 0, 271 => global_word_38 v
| 0, 273 => global_word_39 v
| 0, 275 => global_word_40 v
| 0, 277 => global_word_41 v
| 0, 279 => global_word_42 v
| 0, 281 => global_word_43 v
| 0, 283 => global_word_44 v
| 0, 285 => global_word_45 v
| 0, 287 => global_word_46 v
| 0, 289 => global_word_47 v
| 0, 291 => global_word_48 v
| 0, 293 => global_word_49 v
| 0, 295 => global_word_50 v
| 0, 297 => global_word_51 v
| 0, 299 => global_word_52 v
| 0, 301 => global_word_54 v
| 0, 303 => global_word_55 v
| 0, 408 => global_word_57 v
| 0, 410 => global_word_58 v
| 0, 416 => global_word_59 v
| 0, 419 => global_word_60 v
| 7, 4 => global_word_290 v
| 7, 5 => global_word_294 v
| 8, 4 => global_word_308 v
| 8, 5 => global_word_312 v
| 9, 5 => global_word_332 v
| 9, 6 => global_word_336 v
| 10, 5 => global_word_356 v
| 10, 6 => global_word_360 v
| 11, 7 => global_word_415 v
| 11, 8 => global_word_422 v
| 11, 9 => global_word_429 v
| 12, 7 => global_word_484 v
| 12, 8 => global_word_491 v
| 12, 9 => global_word_498 v
| 13, 7 => global_word_553 v
| 13, 8 => global_word_560 v
| 13, 9 => global_word_567 v
| 14, 7 => global_word_622 v
| 14, 8 => global_word_629 v
| 14, 9 => global_word_636 v
| 15, 7 => global_word_691 v
| 15, 8 => global_word_698 v
| 15, 9 => global_word_705 v
| 16, 7 => global_word_760 v
| 16, 8 => global_word_767 v
| 16, 9 => global_word_774 v
| 17, 7 => global_word_829 v
| 17, 8 => global_word_836 v
| 17, 9 => global_word_843 v
| 18, 7 => global_word_898 v
| 18, 8 => global_word_905 v
| 18, 9 => global_word_912 v
| 19, 5 => global_word_932 v
| 19, 6 => global_word_936 v
| 20, 4 => global_word_950 v
| 20, 5 => global_word_954 v
| 21, 4 => global_word_968 v
| 21, 5 => global_word_972 v
| 22, 4 => global_word_986 v
| 22, 5 => global_word_990 v
| 23, 4 => global_word_1004 v
| 23, 5 => global_word_1008 v
| 24, 4 => global_word_1022 v
| 24, 5 => global_word_1026 v
| 25, 4 => global_word_1040 v
| 25, 5 => global_word_1044 v
| 26, 4 => global_word_1058 v
| 26, 5 => global_word_1062 v
| 27, 5 => global_word_1082 v
| 27, 6 => global_word_1086 v
| 28, 5 => global_word_1106 v
| 28, 6 => global_word_1110 v
| 29, 4 => global_word_1124 v
| 29, 5 => global_word_1128 v
| 30, 4 => global_word_1142 v
| 30, 5 => global_word_1146 v
| 31, 4 => global_word_1160 v
| 31, 5 => global_word_1164 v
| 32, 4 => global_word_1178 v
| 32, 5 => global_word_1182 v
| 33, 5 => global_word_1202 v
| 33, 6 => global_word_1206 v
| 34, 4 => global_word_1220 v
| 34, 5 => global_word_1224 v
| 35, 4 => global_word_1238 v
| 35, 5 => global_word_1242 v
| 36, 4 => global_word_1256 v
| 36, 5 => global_word_1260 v
| _,_ => [::] end.
Transparent Stable.word_0 global_word_0. Lemma top_word_0 v : Stable.word_0 (top_global_leaves v) = global_word_0 v.
Proof. unfold Stable.word_0, top_global_leaves. reflexivity. Qed. Opaque Stable.word_0 global_word_0.
Transparent Stable.word_1 global_word_1. Lemma top_word_1 v : Stable.word_1 (top_global_leaves v) = global_word_1 v.
Proof. unfold Stable.word_1, top_global_leaves. reflexivity. Qed. Opaque Stable.word_1 global_word_1.
Transparent Stable.word_2 global_word_2. Lemma top_word_2 v : Stable.word_2 (top_global_leaves v) = global_word_2 v.
Proof. unfold Stable.word_2, top_global_leaves. reflexivity. Qed. Opaque Stable.word_2 global_word_2.
Transparent Stable.word_3 global_word_53. Lemma top_word_3 v : Stable.word_3 (top_global_leaves v) = global_word_53 v.
Proof. unfold Stable.word_3, top_global_leaves. reflexivity. Qed. Opaque Stable.word_3 global_word_53.
Transparent Stable.word_4 global_word_56. Lemma top_word_4 v : Stable.word_4 (top_global_leaves v) = global_word_56 v.
Proof. unfold Stable.word_4, top_global_leaves. reflexivity. Qed. Opaque Stable.word_4 global_word_56.
Transparent Stable.word_5 global_word_61. Lemma top_word_5 v : Stable.word_5 (top_global_leaves v) = global_word_61 v.
Proof. unfold Stable.word_5, top_global_leaves. reflexivity. Qed. Opaque Stable.word_5 global_word_61.
Transparent Stable.word_201 global_word_3. Lemma top_word_201 v : Stable.word_201 (top_global_leaves v) = global_word_3 v.
Proof. unfold Stable.word_201, top_global_leaves. reflexivity. Qed. Opaque Stable.word_201 global_word_3.
Transparent Stable.word_203 global_word_4. Lemma top_word_203 v : Stable.word_203 (top_global_leaves v) = global_word_4 v.
Proof. unfold Stable.word_203, top_global_leaves. reflexivity. Qed. Opaque Stable.word_203 global_word_4.
Transparent Stable.word_205 global_word_5. Lemma top_word_205 v : Stable.word_205 (top_global_leaves v) = global_word_5 v.
Proof. unfold Stable.word_205, top_global_leaves. reflexivity. Qed. Opaque Stable.word_205 global_word_5.
Transparent Stable.word_207 global_word_6. Lemma top_word_207 v : Stable.word_207 (top_global_leaves v) = global_word_6 v.
Proof. unfold Stable.word_207, top_global_leaves. reflexivity. Qed. Opaque Stable.word_207 global_word_6.
Transparent Stable.word_209 global_word_7. Lemma top_word_209 v : Stable.word_209 (top_global_leaves v) = global_word_7 v.
Proof. unfold Stable.word_209, top_global_leaves. reflexivity. Qed. Opaque Stable.word_209 global_word_7.
Transparent Stable.word_211 global_word_8. Lemma top_word_211 v : Stable.word_211 (top_global_leaves v) = global_word_8 v.
Proof. unfold Stable.word_211, top_global_leaves. reflexivity. Qed. Opaque Stable.word_211 global_word_8.
Transparent Stable.word_213 global_word_9. Lemma top_word_213 v : Stable.word_213 (top_global_leaves v) = global_word_9 v.
Proof. unfold Stable.word_213, top_global_leaves. reflexivity. Qed. Opaque Stable.word_213 global_word_9.
Transparent Stable.word_215 global_word_10. Lemma top_word_215 v : Stable.word_215 (top_global_leaves v) = global_word_10 v.
Proof. unfold Stable.word_215, top_global_leaves. reflexivity. Qed. Opaque Stable.word_215 global_word_10.
Transparent Stable.word_217 global_word_11. Lemma top_word_217 v : Stable.word_217 (top_global_leaves v) = global_word_11 v.
Proof. unfold Stable.word_217, top_global_leaves. reflexivity. Qed. Opaque Stable.word_217 global_word_11.
Transparent Stable.word_219 global_word_12. Lemma top_word_219 v : Stable.word_219 (top_global_leaves v) = global_word_12 v.
Proof. unfold Stable.word_219, top_global_leaves. reflexivity. Qed. Opaque Stable.word_219 global_word_12.
Transparent Stable.word_221 global_word_13. Lemma top_word_221 v : Stable.word_221 (top_global_leaves v) = global_word_13 v.
Proof. unfold Stable.word_221, top_global_leaves. reflexivity. Qed. Opaque Stable.word_221 global_word_13.
Transparent Stable.word_223 global_word_14. Lemma top_word_223 v : Stable.word_223 (top_global_leaves v) = global_word_14 v.
Proof. unfold Stable.word_223, top_global_leaves. reflexivity. Qed. Opaque Stable.word_223 global_word_14.
Transparent Stable.word_225 global_word_15. Lemma top_word_225 v : Stable.word_225 (top_global_leaves v) = global_word_15 v.
Proof. unfold Stable.word_225, top_global_leaves. reflexivity. Qed. Opaque Stable.word_225 global_word_15.
Transparent Stable.word_227 global_word_16. Lemma top_word_227 v : Stable.word_227 (top_global_leaves v) = global_word_16 v.
Proof. unfold Stable.word_227, top_global_leaves. reflexivity. Qed. Opaque Stable.word_227 global_word_16.
Transparent Stable.word_229 global_word_17. Lemma top_word_229 v : Stable.word_229 (top_global_leaves v) = global_word_17 v.
Proof. unfold Stable.word_229, top_global_leaves. reflexivity. Qed. Opaque Stable.word_229 global_word_17.
Transparent Stable.word_231 global_word_18. Lemma top_word_231 v : Stable.word_231 (top_global_leaves v) = global_word_18 v.
Proof. unfold Stable.word_231, top_global_leaves. reflexivity. Qed. Opaque Stable.word_231 global_word_18.
Transparent Stable.word_233 global_word_19. Lemma top_word_233 v : Stable.word_233 (top_global_leaves v) = global_word_19 v.
Proof. unfold Stable.word_233, top_global_leaves. reflexivity. Qed. Opaque Stable.word_233 global_word_19.
Transparent Stable.word_235 global_word_20. Lemma top_word_235 v : Stable.word_235 (top_global_leaves v) = global_word_20 v.
Proof. unfold Stable.word_235, top_global_leaves. reflexivity. Qed. Opaque Stable.word_235 global_word_20.
Transparent Stable.word_237 global_word_21. Lemma top_word_237 v : Stable.word_237 (top_global_leaves v) = global_word_21 v.
Proof. unfold Stable.word_237, top_global_leaves. reflexivity. Qed. Opaque Stable.word_237 global_word_21.
Transparent Stable.word_239 global_word_22. Lemma top_word_239 v : Stable.word_239 (top_global_leaves v) = global_word_22 v.
Proof. unfold Stable.word_239, top_global_leaves. reflexivity. Qed. Opaque Stable.word_239 global_word_22.
Transparent Stable.word_241 global_word_23. Lemma top_word_241 v : Stable.word_241 (top_global_leaves v) = global_word_23 v.
Proof. unfold Stable.word_241, top_global_leaves. reflexivity. Qed. Opaque Stable.word_241 global_word_23.
Transparent Stable.word_243 global_word_24. Lemma top_word_243 v : Stable.word_243 (top_global_leaves v) = global_word_24 v.
Proof. unfold Stable.word_243, top_global_leaves. reflexivity. Qed. Opaque Stable.word_243 global_word_24.
Transparent Stable.word_245 global_word_25. Lemma top_word_245 v : Stable.word_245 (top_global_leaves v) = global_word_25 v.
Proof. unfold Stable.word_245, top_global_leaves. reflexivity. Qed. Opaque Stable.word_245 global_word_25.
Transparent Stable.word_247 global_word_26. Lemma top_word_247 v : Stable.word_247 (top_global_leaves v) = global_word_26 v.
Proof. unfold Stable.word_247, top_global_leaves. reflexivity. Qed. Opaque Stable.word_247 global_word_26.
Transparent Stable.word_249 global_word_27. Lemma top_word_249 v : Stable.word_249 (top_global_leaves v) = global_word_27 v.
Proof. unfold Stable.word_249, top_global_leaves. reflexivity. Qed. Opaque Stable.word_249 global_word_27.
Transparent Stable.word_251 global_word_28. Lemma top_word_251 v : Stable.word_251 (top_global_leaves v) = global_word_28 v.
Proof. unfold Stable.word_251, top_global_leaves. reflexivity. Qed. Opaque Stable.word_251 global_word_28.
Transparent Stable.word_253 global_word_29. Lemma top_word_253 v : Stable.word_253 (top_global_leaves v) = global_word_29 v.
Proof. unfold Stable.word_253, top_global_leaves. reflexivity. Qed. Opaque Stable.word_253 global_word_29.
Transparent Stable.word_255 global_word_30. Lemma top_word_255 v : Stable.word_255 (top_global_leaves v) = global_word_30 v.
Proof. unfold Stable.word_255, top_global_leaves. reflexivity. Qed. Opaque Stable.word_255 global_word_30.
Transparent Stable.word_257 global_word_31. Lemma top_word_257 v : Stable.word_257 (top_global_leaves v) = global_word_31 v.
Proof. unfold Stable.word_257, top_global_leaves. reflexivity. Qed. Opaque Stable.word_257 global_word_31.
Transparent Stable.word_259 global_word_32. Lemma top_word_259 v : Stable.word_259 (top_global_leaves v) = global_word_32 v.
Proof. unfold Stable.word_259, top_global_leaves. reflexivity. Qed. Opaque Stable.word_259 global_word_32.
Transparent Stable.word_261 global_word_33. Lemma top_word_261 v : Stable.word_261 (top_global_leaves v) = global_word_33 v.
Proof. unfold Stable.word_261, top_global_leaves. reflexivity. Qed. Opaque Stable.word_261 global_word_33.
Transparent Stable.word_263 global_word_34. Lemma top_word_263 v : Stable.word_263 (top_global_leaves v) = global_word_34 v.
Proof. unfold Stable.word_263, top_global_leaves. reflexivity. Qed. Opaque Stable.word_263 global_word_34.
Transparent Stable.word_265 global_word_35. Lemma top_word_265 v : Stable.word_265 (top_global_leaves v) = global_word_35 v.
Proof. unfold Stable.word_265, top_global_leaves. reflexivity. Qed. Opaque Stable.word_265 global_word_35.
Transparent Stable.word_267 global_word_36. Lemma top_word_267 v : Stable.word_267 (top_global_leaves v) = global_word_36 v.
Proof. unfold Stable.word_267, top_global_leaves. reflexivity. Qed. Opaque Stable.word_267 global_word_36.
Transparent Stable.word_269 global_word_37. Lemma top_word_269 v : Stable.word_269 (top_global_leaves v) = global_word_37 v.
Proof. unfold Stable.word_269, top_global_leaves. reflexivity. Qed. Opaque Stable.word_269 global_word_37.
Transparent Stable.word_271 global_word_38. Lemma top_word_271 v : Stable.word_271 (top_global_leaves v) = global_word_38 v.
Proof. unfold Stable.word_271, top_global_leaves. reflexivity. Qed. Opaque Stable.word_271 global_word_38.
Transparent Stable.word_273 global_word_39. Lemma top_word_273 v : Stable.word_273 (top_global_leaves v) = global_word_39 v.
Proof. unfold Stable.word_273, top_global_leaves. reflexivity. Qed. Opaque Stable.word_273 global_word_39.
Transparent Stable.word_275 global_word_40. Lemma top_word_275 v : Stable.word_275 (top_global_leaves v) = global_word_40 v.
Proof. unfold Stable.word_275, top_global_leaves. reflexivity. Qed. Opaque Stable.word_275 global_word_40.
Transparent Stable.word_277 global_word_41. Lemma top_word_277 v : Stable.word_277 (top_global_leaves v) = global_word_41 v.
Proof. unfold Stable.word_277, top_global_leaves. reflexivity. Qed. Opaque Stable.word_277 global_word_41.
Transparent Stable.word_279 global_word_42. Lemma top_word_279 v : Stable.word_279 (top_global_leaves v) = global_word_42 v.
Proof. unfold Stable.word_279, top_global_leaves. reflexivity. Qed. Opaque Stable.word_279 global_word_42.
Transparent Stable.word_281 global_word_43. Lemma top_word_281 v : Stable.word_281 (top_global_leaves v) = global_word_43 v.
Proof. unfold Stable.word_281, top_global_leaves. reflexivity. Qed. Opaque Stable.word_281 global_word_43.
Transparent Stable.word_283 global_word_44. Lemma top_word_283 v : Stable.word_283 (top_global_leaves v) = global_word_44 v.
Proof. unfold Stable.word_283, top_global_leaves. reflexivity. Qed. Opaque Stable.word_283 global_word_44.
Transparent Stable.word_285 global_word_45. Lemma top_word_285 v : Stable.word_285 (top_global_leaves v) = global_word_45 v.
Proof. unfold Stable.word_285, top_global_leaves. reflexivity. Qed. Opaque Stable.word_285 global_word_45.
Transparent Stable.word_287 global_word_46. Lemma top_word_287 v : Stable.word_287 (top_global_leaves v) = global_word_46 v.
Proof. unfold Stable.word_287, top_global_leaves. reflexivity. Qed. Opaque Stable.word_287 global_word_46.
Transparent Stable.word_289 global_word_47. Lemma top_word_289 v : Stable.word_289 (top_global_leaves v) = global_word_47 v.
Proof. unfold Stable.word_289, top_global_leaves. reflexivity. Qed. Opaque Stable.word_289 global_word_47.
Transparent Stable.word_291 global_word_48. Lemma top_word_291 v : Stable.word_291 (top_global_leaves v) = global_word_48 v.
Proof. unfold Stable.word_291, top_global_leaves. reflexivity. Qed. Opaque Stable.word_291 global_word_48.
Transparent Stable.word_293 global_word_49. Lemma top_word_293 v : Stable.word_293 (top_global_leaves v) = global_word_49 v.
Proof. unfold Stable.word_293, top_global_leaves. reflexivity. Qed. Opaque Stable.word_293 global_word_49.
Transparent Stable.word_295 global_word_50. Lemma top_word_295 v : Stable.word_295 (top_global_leaves v) = global_word_50 v.
Proof. unfold Stable.word_295, top_global_leaves. reflexivity. Qed. Opaque Stable.word_295 global_word_50.
Transparent Stable.word_297 global_word_51. Lemma top_word_297 v : Stable.word_297 (top_global_leaves v) = global_word_51 v.
Proof. unfold Stable.word_297, top_global_leaves. reflexivity. Qed. Opaque Stable.word_297 global_word_51.
Transparent Stable.word_299 global_word_52. Lemma top_word_299 v : Stable.word_299 (top_global_leaves v) = global_word_52 v.
Proof. unfold Stable.word_299, top_global_leaves. reflexivity. Qed. Opaque Stable.word_299 global_word_52.
Transparent Stable.word_301 global_word_54. Lemma top_word_301 v : Stable.word_301 (top_global_leaves v) = global_word_54 v.
Proof. unfold Stable.word_301, top_global_leaves. reflexivity. Qed. Opaque Stable.word_301 global_word_54.
Transparent Stable.word_303 global_word_55. Lemma top_word_303 v : Stable.word_303 (top_global_leaves v) = global_word_55 v.
Proof. unfold Stable.word_303, top_global_leaves. reflexivity. Qed. Opaque Stable.word_303 global_word_55.
Transparent Stable.word_408 global_word_57. Lemma top_word_408 v : Stable.word_408 (top_global_leaves v) = global_word_57 v.
Proof. unfold Stable.word_408, top_global_leaves. reflexivity. Qed. Opaque Stable.word_408 global_word_57.
Transparent Stable.word_410 global_word_58. Lemma top_word_410 v : Stable.word_410 (top_global_leaves v) = global_word_58 v.
Proof. unfold Stable.word_410, top_global_leaves. reflexivity. Qed. Opaque Stable.word_410 global_word_58.
Transparent Stable.word_416 global_word_59. Lemma top_word_416 v : Stable.word_416 (top_global_leaves v) = global_word_59 v.
Proof. unfold Stable.word_416, top_global_leaves. reflexivity. Qed. Opaque Stable.word_416 global_word_59.
Transparent Stable.word_419 global_word_60. Lemma top_word_419 v : Stable.word_419 (top_global_leaves v) = global_word_60 v.
Proof. unfold Stable.word_419, top_global_leaves. reflexivity. Qed. Opaque Stable.word_419 global_word_60.
Transparent Stable.port_7_4 global_word_290. Lemma top_port_7_4 v : Stable.port_7_4 (top_global_leaves v) = global_word_290 v.
Proof. unfold Stable.port_7_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_7_4 global_word_290.
Transparent Stable.port_7_5 global_word_294. Lemma top_port_7_5 v : Stable.port_7_5 (top_global_leaves v) = global_word_294 v.
Proof. unfold Stable.port_7_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_7_5 global_word_294.
Transparent Stable.port_8_4 global_word_308. Lemma top_port_8_4 v : Stable.port_8_4 (top_global_leaves v) = global_word_308 v.
Proof. unfold Stable.port_8_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_8_4 global_word_308.
Transparent Stable.port_8_5 global_word_312. Lemma top_port_8_5 v : Stable.port_8_5 (top_global_leaves v) = global_word_312 v.
Proof. unfold Stable.port_8_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_8_5 global_word_312.
Transparent Stable.port_9_5 global_word_332. Lemma top_port_9_5 v : Stable.port_9_5 (top_global_leaves v) = global_word_332 v.
Proof. unfold Stable.port_9_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_9_5 global_word_332.
Transparent Stable.port_9_6 global_word_336. Lemma top_port_9_6 v : Stable.port_9_6 (top_global_leaves v) = global_word_336 v.
Proof. unfold Stable.port_9_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_9_6 global_word_336.
Transparent Stable.port_10_5 global_word_356. Lemma top_port_10_5 v : Stable.port_10_5 (top_global_leaves v) = global_word_356 v.
Proof. unfold Stable.port_10_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_10_5 global_word_356.
Transparent Stable.port_10_6 global_word_360. Lemma top_port_10_6 v : Stable.port_10_6 (top_global_leaves v) = global_word_360 v.
Proof. unfold Stable.port_10_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_10_6 global_word_360.
Transparent Stable.port_11_7 global_word_415. Lemma top_port_11_7 v : Stable.port_11_7 (top_global_leaves v) = global_word_415 v.
Proof. unfold Stable.port_11_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_11_7 global_word_415.
Transparent Stable.port_11_8 global_word_422. Lemma top_port_11_8 v : Stable.port_11_8 (top_global_leaves v) = global_word_422 v.
Proof. unfold Stable.port_11_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_11_8 global_word_422.
Transparent Stable.port_11_9 global_word_429. Lemma top_port_11_9 v : Stable.port_11_9 (top_global_leaves v) = global_word_429 v.
Proof. unfold Stable.port_11_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_11_9 global_word_429.
Transparent Stable.port_12_7 global_word_484. Lemma top_port_12_7 v : Stable.port_12_7 (top_global_leaves v) = global_word_484 v.
Proof. unfold Stable.port_12_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_12_7 global_word_484.
Transparent Stable.port_12_8 global_word_491. Lemma top_port_12_8 v : Stable.port_12_8 (top_global_leaves v) = global_word_491 v.
Proof. unfold Stable.port_12_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_12_8 global_word_491.
Transparent Stable.port_12_9 global_word_498. Lemma top_port_12_9 v : Stable.port_12_9 (top_global_leaves v) = global_word_498 v.
Proof. unfold Stable.port_12_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_12_9 global_word_498.
Transparent Stable.port_13_7 global_word_553. Lemma top_port_13_7 v : Stable.port_13_7 (top_global_leaves v) = global_word_553 v.
Proof. unfold Stable.port_13_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_13_7 global_word_553.
Transparent Stable.port_13_8 global_word_560. Lemma top_port_13_8 v : Stable.port_13_8 (top_global_leaves v) = global_word_560 v.
Proof. unfold Stable.port_13_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_13_8 global_word_560.
Transparent Stable.port_13_9 global_word_567. Lemma top_port_13_9 v : Stable.port_13_9 (top_global_leaves v) = global_word_567 v.
Proof. unfold Stable.port_13_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_13_9 global_word_567.
Transparent Stable.port_14_7 global_word_622. Lemma top_port_14_7 v : Stable.port_14_7 (top_global_leaves v) = global_word_622 v.
Proof. unfold Stable.port_14_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_14_7 global_word_622.
Transparent Stable.port_14_8 global_word_629. Lemma top_port_14_8 v : Stable.port_14_8 (top_global_leaves v) = global_word_629 v.
Proof. unfold Stable.port_14_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_14_8 global_word_629.
Transparent Stable.port_14_9 global_word_636. Lemma top_port_14_9 v : Stable.port_14_9 (top_global_leaves v) = global_word_636 v.
Proof. unfold Stable.port_14_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_14_9 global_word_636.
Transparent Stable.port_15_7 global_word_691. Lemma top_port_15_7 v : Stable.port_15_7 (top_global_leaves v) = global_word_691 v.
Proof. unfold Stable.port_15_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_15_7 global_word_691.
Transparent Stable.port_15_8 global_word_698. Lemma top_port_15_8 v : Stable.port_15_8 (top_global_leaves v) = global_word_698 v.
Proof. unfold Stable.port_15_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_15_8 global_word_698.
Transparent Stable.port_15_9 global_word_705. Lemma top_port_15_9 v : Stable.port_15_9 (top_global_leaves v) = global_word_705 v.
Proof. unfold Stable.port_15_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_15_9 global_word_705.
Transparent Stable.port_16_7 global_word_760. Lemma top_port_16_7 v : Stable.port_16_7 (top_global_leaves v) = global_word_760 v.
Proof. unfold Stable.port_16_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_16_7 global_word_760.
Transparent Stable.port_16_8 global_word_767. Lemma top_port_16_8 v : Stable.port_16_8 (top_global_leaves v) = global_word_767 v.
Proof. unfold Stable.port_16_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_16_8 global_word_767.
Transparent Stable.port_16_9 global_word_774. Lemma top_port_16_9 v : Stable.port_16_9 (top_global_leaves v) = global_word_774 v.
Proof. unfold Stable.port_16_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_16_9 global_word_774.
Transparent Stable.port_17_7 global_word_829. Lemma top_port_17_7 v : Stable.port_17_7 (top_global_leaves v) = global_word_829 v.
Proof. unfold Stable.port_17_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_17_7 global_word_829.
Transparent Stable.port_17_8 global_word_836. Lemma top_port_17_8 v : Stable.port_17_8 (top_global_leaves v) = global_word_836 v.
Proof. unfold Stable.port_17_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_17_8 global_word_836.
Transparent Stable.port_17_9 global_word_843. Lemma top_port_17_9 v : Stable.port_17_9 (top_global_leaves v) = global_word_843 v.
Proof. unfold Stable.port_17_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_17_9 global_word_843.
Transparent Stable.port_18_7 global_word_898. Lemma top_port_18_7 v : Stable.port_18_7 (top_global_leaves v) = global_word_898 v.
Proof. unfold Stable.port_18_7, top_global_leaves. reflexivity. Qed. Opaque Stable.port_18_7 global_word_898.
Transparent Stable.port_18_8 global_word_905. Lemma top_port_18_8 v : Stable.port_18_8 (top_global_leaves v) = global_word_905 v.
Proof. unfold Stable.port_18_8, top_global_leaves. reflexivity. Qed. Opaque Stable.port_18_8 global_word_905.
Transparent Stable.port_18_9 global_word_912. Lemma top_port_18_9 v : Stable.port_18_9 (top_global_leaves v) = global_word_912 v.
Proof. unfold Stable.port_18_9, top_global_leaves. reflexivity. Qed. Opaque Stable.port_18_9 global_word_912.
Transparent Stable.port_19_5 global_word_932. Lemma top_port_19_5 v : Stable.port_19_5 (top_global_leaves v) = global_word_932 v.
Proof. unfold Stable.port_19_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_19_5 global_word_932.
Transparent Stable.port_19_6 global_word_936. Lemma top_port_19_6 v : Stable.port_19_6 (top_global_leaves v) = global_word_936 v.
Proof. unfold Stable.port_19_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_19_6 global_word_936.
Transparent Stable.port_20_4 global_word_950. Lemma top_port_20_4 v : Stable.port_20_4 (top_global_leaves v) = global_word_950 v.
Proof. unfold Stable.port_20_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_20_4 global_word_950.
Transparent Stable.port_20_5 global_word_954. Lemma top_port_20_5 v : Stable.port_20_5 (top_global_leaves v) = global_word_954 v.
Proof. unfold Stable.port_20_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_20_5 global_word_954.
Transparent Stable.port_21_4 global_word_968. Lemma top_port_21_4 v : Stable.port_21_4 (top_global_leaves v) = global_word_968 v.
Proof. unfold Stable.port_21_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_21_4 global_word_968.
Transparent Stable.port_21_5 global_word_972. Lemma top_port_21_5 v : Stable.port_21_5 (top_global_leaves v) = global_word_972 v.
Proof. unfold Stable.port_21_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_21_5 global_word_972.
Transparent Stable.port_22_4 global_word_986. Lemma top_port_22_4 v : Stable.port_22_4 (top_global_leaves v) = global_word_986 v.
Proof. unfold Stable.port_22_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_22_4 global_word_986.
Transparent Stable.port_22_5 global_word_990. Lemma top_port_22_5 v : Stable.port_22_5 (top_global_leaves v) = global_word_990 v.
Proof. unfold Stable.port_22_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_22_5 global_word_990.
Transparent Stable.port_23_4 global_word_1004. Lemma top_port_23_4 v : Stable.port_23_4 (top_global_leaves v) = global_word_1004 v.
Proof. unfold Stable.port_23_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_23_4 global_word_1004.
Transparent Stable.port_23_5 global_word_1008. Lemma top_port_23_5 v : Stable.port_23_5 (top_global_leaves v) = global_word_1008 v.
Proof. unfold Stable.port_23_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_23_5 global_word_1008.
Transparent Stable.port_24_4 global_word_1022. Lemma top_port_24_4 v : Stable.port_24_4 (top_global_leaves v) = global_word_1022 v.
Proof. unfold Stable.port_24_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_24_4 global_word_1022.
Transparent Stable.port_24_5 global_word_1026. Lemma top_port_24_5 v : Stable.port_24_5 (top_global_leaves v) = global_word_1026 v.
Proof. unfold Stable.port_24_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_24_5 global_word_1026.
Transparent Stable.port_25_4 global_word_1040. Lemma top_port_25_4 v : Stable.port_25_4 (top_global_leaves v) = global_word_1040 v.
Proof. unfold Stable.port_25_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_25_4 global_word_1040.
Transparent Stable.port_25_5 global_word_1044. Lemma top_port_25_5 v : Stable.port_25_5 (top_global_leaves v) = global_word_1044 v.
Proof. unfold Stable.port_25_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_25_5 global_word_1044.
Transparent Stable.port_26_4 global_word_1058. Lemma top_port_26_4 v : Stable.port_26_4 (top_global_leaves v) = global_word_1058 v.
Proof. unfold Stable.port_26_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_26_4 global_word_1058.
Transparent Stable.port_26_5 global_word_1062. Lemma top_port_26_5 v : Stable.port_26_5 (top_global_leaves v) = global_word_1062 v.
Proof. unfold Stable.port_26_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_26_5 global_word_1062.
Transparent Stable.port_27_5 global_word_1082. Lemma top_port_27_5 v : Stable.port_27_5 (top_global_leaves v) = global_word_1082 v.
Proof. unfold Stable.port_27_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_27_5 global_word_1082.
Transparent Stable.port_27_6 global_word_1086. Lemma top_port_27_6 v : Stable.port_27_6 (top_global_leaves v) = global_word_1086 v.
Proof. unfold Stable.port_27_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_27_6 global_word_1086.
Transparent Stable.port_28_5 global_word_1106. Lemma top_port_28_5 v : Stable.port_28_5 (top_global_leaves v) = global_word_1106 v.
Proof. unfold Stable.port_28_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_28_5 global_word_1106.
Transparent Stable.port_28_6 global_word_1110. Lemma top_port_28_6 v : Stable.port_28_6 (top_global_leaves v) = global_word_1110 v.
Proof. unfold Stable.port_28_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_28_6 global_word_1110.
Transparent Stable.port_29_4 global_word_1124. Lemma top_port_29_4 v : Stable.port_29_4 (top_global_leaves v) = global_word_1124 v.
Proof. unfold Stable.port_29_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_29_4 global_word_1124.
Transparent Stable.port_29_5 global_word_1128. Lemma top_port_29_5 v : Stable.port_29_5 (top_global_leaves v) = global_word_1128 v.
Proof. unfold Stable.port_29_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_29_5 global_word_1128.
Transparent Stable.port_30_4 global_word_1142. Lemma top_port_30_4 v : Stable.port_30_4 (top_global_leaves v) = global_word_1142 v.
Proof. unfold Stable.port_30_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_30_4 global_word_1142.
Transparent Stable.port_30_5 global_word_1146. Lemma top_port_30_5 v : Stable.port_30_5 (top_global_leaves v) = global_word_1146 v.
Proof. unfold Stable.port_30_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_30_5 global_word_1146.
Transparent Stable.port_31_4 global_word_1160. Lemma top_port_31_4 v : Stable.port_31_4 (top_global_leaves v) = global_word_1160 v.
Proof. unfold Stable.port_31_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_31_4 global_word_1160.
Transparent Stable.port_31_5 global_word_1164. Lemma top_port_31_5 v : Stable.port_31_5 (top_global_leaves v) = global_word_1164 v.
Proof. unfold Stable.port_31_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_31_5 global_word_1164.
Transparent Stable.port_32_4 global_word_1178. Lemma top_port_32_4 v : Stable.port_32_4 (top_global_leaves v) = global_word_1178 v.
Proof. unfold Stable.port_32_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_32_4 global_word_1178.
Transparent Stable.port_32_5 global_word_1182. Lemma top_port_32_5 v : Stable.port_32_5 (top_global_leaves v) = global_word_1182 v.
Proof. unfold Stable.port_32_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_32_5 global_word_1182.
Transparent Stable.port_33_5 global_word_1202. Lemma top_port_33_5 v : Stable.port_33_5 (top_global_leaves v) = global_word_1202 v.
Proof. unfold Stable.port_33_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_33_5 global_word_1202.
Transparent Stable.port_33_6 global_word_1206. Lemma top_port_33_6 v : Stable.port_33_6 (top_global_leaves v) = global_word_1206 v.
Proof. unfold Stable.port_33_6, top_global_leaves. reflexivity. Qed. Opaque Stable.port_33_6 global_word_1206.
Transparent Stable.port_34_4 global_word_1220. Lemma top_port_34_4 v : Stable.port_34_4 (top_global_leaves v) = global_word_1220 v.
Proof. unfold Stable.port_34_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_34_4 global_word_1220.
Transparent Stable.port_34_5 global_word_1224. Lemma top_port_34_5 v : Stable.port_34_5 (top_global_leaves v) = global_word_1224 v.
Proof. unfold Stable.port_34_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_34_5 global_word_1224.
Transparent Stable.port_35_4 global_word_1238. Lemma top_port_35_4 v : Stable.port_35_4 (top_global_leaves v) = global_word_1238 v.
Proof. unfold Stable.port_35_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_35_4 global_word_1238.
Transparent Stable.port_35_5 global_word_1242. Lemma top_port_35_5 v : Stable.port_35_5 (top_global_leaves v) = global_word_1242 v.
Proof. unfold Stable.port_35_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_35_5 global_word_1242.
Transparent Stable.port_36_4 global_word_1256. Lemma top_port_36_4 v : Stable.port_36_4 (top_global_leaves v) = global_word_1256 v.
Proof. unfold Stable.port_36_4, top_global_leaves. reflexivity. Qed. Opaque Stable.port_36_4 global_word_1256.
Transparent Stable.port_36_5 global_word_1260. Lemma top_port_36_5 v : Stable.port_36_5 (top_global_leaves v) = global_word_1260 v.
Proof. unfold Stable.port_36_5, top_global_leaves. reflexivity. Qed. Opaque Stable.port_36_5 global_word_1260.
Transparent Stable.word_37 global_word_62. Lemma top_word_37 v : Stable.word_37 (top_global_leaves v) = global_word_62 v.
Proof. unfold Stable.word_37, global_word_62, Stable.closed_word_37, global_closed_62, Stable.expr_word_37, global_expr_62.
 rewrite top_word_3.
 reflexivity. Qed. Opaque Stable.word_37 global_word_62.
Transparent Stable.word_38 global_word_63. Lemma top_word_38 v : Stable.word_38 (top_global_leaves v) = global_word_63 v.
Proof. unfold Stable.word_38, global_word_63, Stable.closed_word_38, global_closed_63, Stable.expr_word_38, global_expr_63.
 rewrite top_word_3 top_word_37.
 reflexivity. Qed. Opaque Stable.word_38 global_word_63.
Transparent Stable.word_39 global_word_64. Lemma top_word_39 v : Stable.word_39 (top_global_leaves v) = global_word_64 v.
Proof. unfold Stable.word_39, global_word_64, Stable.closed_word_39, global_closed_64, Stable.expr_word_39, global_expr_64.
 rewrite top_word_38.
 reflexivity. Qed. Opaque Stable.word_39 global_word_64.
Transparent Stable.word_40 global_word_65. Lemma top_word_40 v : Stable.word_40 (top_global_leaves v) = global_word_65 v.
Proof. unfold Stable.word_40, global_word_65, Stable.closed_word_40, global_closed_65, Stable.expr_word_40, global_expr_65.
 rewrite top_word_39.
 reflexivity. Qed. Opaque Stable.word_40 global_word_65.
Transparent Stable.word_41 global_word_66. Lemma top_word_41 v : Stable.word_41 (top_global_leaves v) = global_word_66 v.
Proof. unfold Stable.word_41, global_word_66, Stable.closed_word_41, global_closed_66, Stable.expr_word_41, global_expr_66.
 rewrite top_word_39.
 reflexivity. Qed. Opaque Stable.word_41 global_word_66.
Transparent Stable.word_42 global_word_67. Lemma top_word_42 v : Stable.word_42 (top_global_leaves v) = global_word_67 v.
Proof. unfold Stable.word_42, global_word_67, Stable.closed_word_42, global_closed_67, Stable.expr_word_42, global_expr_67.
 rewrite top_word_41.
 reflexivity. Qed. Opaque Stable.word_42 global_word_67.
Transparent Stable.word_43 global_word_68. Lemma top_word_43 v : Stable.word_43 (top_global_leaves v) = global_word_68 v.
Proof. unfold Stable.word_43, global_word_68, Stable.closed_word_43, global_closed_68, Stable.expr_word_43, global_expr_68.
 rewrite top_word_42.
 reflexivity. Qed. Opaque Stable.word_43 global_word_68.
Transparent Stable.word_44 global_word_69. Lemma top_word_44 v : Stable.word_44 (top_global_leaves v) = global_word_69 v.
Proof. unfold Stable.word_44, global_word_69, Stable.closed_word_44, global_closed_69, Stable.expr_word_44, global_expr_69.
 rewrite top_word_2.
 reflexivity. Qed. Opaque Stable.word_44 global_word_69.
Transparent Stable.word_45 global_word_70. Lemma top_word_45 v : Stable.word_45 (top_global_leaves v) = global_word_70 v.
Proof. unfold Stable.word_45, global_word_70, Stable.closed_word_45, global_closed_70, Stable.expr_word_45, global_expr_70.
 rewrite top_word_44.
 reflexivity. Qed. Opaque Stable.word_45 global_word_70.
Transparent Stable.word_46 global_word_71. Lemma top_word_46 v : Stable.word_46 (top_global_leaves v) = global_word_71 v.
Proof. unfold Stable.word_46, global_word_71, Stable.closed_word_46, global_closed_71, Stable.expr_word_46, global_expr_71.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_46 global_word_71.
Transparent Stable.word_47 global_word_72. Lemma top_word_47 v : Stable.word_47 (top_global_leaves v) = global_word_72 v.
Proof. unfold Stable.word_47, global_word_72, Stable.closed_word_47, global_closed_72, Stable.expr_word_47, global_expr_72.
 rewrite top_word_39 top_word_46.
 reflexivity. Qed. Opaque Stable.word_47 global_word_72.
Transparent Stable.word_48 global_word_73. Lemma top_word_48 v : Stable.word_48 (top_global_leaves v) = global_word_73 v.
Proof. unfold Stable.word_48, global_word_73, Stable.closed_word_48, global_closed_73, Stable.expr_word_48, global_expr_73.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_48 global_word_73.
Transparent Stable.word_49 global_word_74. Lemma top_word_49 v : Stable.word_49 (top_global_leaves v) = global_word_74 v.
Proof. unfold Stable.word_49, global_word_74, Stable.closed_word_49, global_closed_74, Stable.expr_word_49, global_expr_74.
 rewrite top_word_39 top_word_47 top_word_48.
 reflexivity. Qed. Opaque Stable.word_49 global_word_74.
Transparent Stable.word_50 global_word_75. Lemma top_word_50 v : Stable.word_50 (top_global_leaves v) = global_word_75 v.
Proof. unfold Stable.word_50, global_word_75, Stable.closed_word_50, global_closed_75, Stable.expr_word_50, global_expr_75.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_50 global_word_75.
Transparent Stable.word_51 global_word_76. Lemma top_word_51 v : Stable.word_51 (top_global_leaves v) = global_word_76 v.
Proof. unfold Stable.word_51, global_word_76, Stable.closed_word_51, global_closed_76, Stable.expr_word_51, global_expr_76.
 rewrite top_word_40.
 reflexivity. Qed. Opaque Stable.word_51 global_word_76.
Transparent Stable.word_52 global_word_77. Lemma top_word_52 v : Stable.word_52 (top_global_leaves v) = global_word_77 v.
Proof. unfold Stable.word_52, global_word_77, Stable.closed_word_52, global_closed_77, Stable.expr_word_52, global_expr_77.
 rewrite top_word_49 top_word_50 top_word_51.
 reflexivity. Qed. Opaque Stable.word_52 global_word_77.
Transparent Stable.word_53 global_word_78. Lemma top_word_53 v : Stable.word_53 (top_global_leaves v) = global_word_78 v.
Proof. unfold Stable.word_53, global_word_78, Stable.closed_word_53, global_closed_78, Stable.expr_word_53, global_expr_78.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_53 global_word_78.
Transparent Stable.word_54 global_word_79. Lemma top_word_54 v : Stable.word_54 (top_global_leaves v) = global_word_79 v.
Proof. unfold Stable.word_54, global_word_79, Stable.closed_word_54, global_closed_79, Stable.expr_word_54, global_expr_79.
 rewrite top_word_43.
 reflexivity. Qed. Opaque Stable.word_54 global_word_79.
Transparent Stable.word_55 global_word_80. Lemma top_word_55 v : Stable.word_55 (top_global_leaves v) = global_word_80 v.
Proof. unfold Stable.word_55, global_word_80, Stable.closed_word_55, global_closed_80, Stable.expr_word_55, global_expr_80.
 rewrite top_word_52 top_word_53 top_word_54.
 reflexivity. Qed. Opaque Stable.word_55 global_word_80.
Transparent Stable.word_56 global_word_81. Lemma top_word_56 v : Stable.word_56 (top_global_leaves v) = global_word_81 v.
Proof. unfold Stable.word_56, global_word_81, Stable.closed_word_56, global_closed_81, Stable.expr_word_56, global_expr_81.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_56 global_word_81.
Transparent Stable.word_57 global_word_82. Lemma top_word_57 v : Stable.word_57 (top_global_leaves v) = global_word_82 v.
Proof. unfold Stable.word_57, global_word_82, Stable.closed_word_57, global_closed_82, Stable.expr_word_57, global_expr_82.
 rewrite top_word_42 top_word_55 top_word_56.
 reflexivity. Qed. Opaque Stable.word_57 global_word_82.
Transparent Stable.word_58 global_word_83. Lemma top_word_58 v : Stable.word_58 (top_global_leaves v) = global_word_83 v.
Proof. unfold Stable.word_58, global_word_83, Stable.closed_word_58, global_closed_83, Stable.expr_word_58, global_expr_83.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_58 global_word_83.
Transparent Stable.word_59 global_word_84. Lemma top_word_59 v : Stable.word_59 (top_global_leaves v) = global_word_84 v.
Proof. unfold Stable.word_59, global_word_84, Stable.closed_word_59, global_closed_84, Stable.expr_word_59, global_expr_84.
 rewrite top_word_42 top_word_57 top_word_58.
 reflexivity. Qed. Opaque Stable.word_59 global_word_84.
Transparent Stable.word_60 global_word_85. Lemma top_word_60 v : Stable.word_60 (top_global_leaves v) = global_word_85 v.
Proof. unfold Stable.word_60, global_word_85, Stable.closed_word_60, global_closed_85, Stable.expr_word_60, global_expr_85.
 rewrite top_word_59.
 reflexivity. Qed. Opaque Stable.word_60 global_word_85.
Transparent Stable.word_61 global_word_86. Lemma top_word_61 v : Stable.word_61 (top_global_leaves v) = global_word_86 v.
Proof. unfold Stable.word_61, global_word_86, Stable.closed_word_61, global_closed_86, Stable.expr_word_61, global_expr_86.
 reflexivity. Qed. Opaque Stable.word_61 global_word_86.
Transparent Stable.word_62 global_word_87. Lemma top_word_62 v : Stable.word_62 (top_global_leaves v) = global_word_87 v.
Proof. unfold Stable.word_62, global_word_87, Stable.closed_word_62, global_closed_87, Stable.expr_word_62, global_expr_87.
 rewrite top_word_61.
 reflexivity. Qed. Opaque Stable.word_62 global_word_87.
Transparent Stable.word_63 global_word_88. Lemma top_word_63 v : Stable.word_63 (top_global_leaves v) = global_word_88 v.
Proof. unfold Stable.word_63, global_word_88, Stable.closed_word_63, global_closed_88, Stable.expr_word_63, global_expr_88.
 rewrite top_word_62.
 reflexivity. Qed. Opaque Stable.word_63 global_word_88.
Transparent Stable.word_64 global_word_89. Lemma top_word_64 v : Stable.word_64 (top_global_leaves v) = global_word_89 v.
Proof. unfold Stable.word_64, global_word_89, Stable.closed_word_64, global_closed_89, Stable.expr_word_64, global_expr_89.
 rewrite top_word_61.
 reflexivity. Qed. Opaque Stable.word_64 global_word_89.
Transparent Stable.word_65 global_word_90. Lemma top_word_65 v : Stable.word_65 (top_global_leaves v) = global_word_90 v.
Proof. unfold Stable.word_65, global_word_90, Stable.closed_word_65, global_closed_90, Stable.expr_word_65, global_expr_90.
 rewrite top_word_63 top_word_64.
 reflexivity. Qed. Opaque Stable.word_65 global_word_90.
Transparent Stable.word_66 global_word_91. Lemma top_word_66 v : Stable.word_66 (top_global_leaves v) = global_word_91 v.
Proof. unfold Stable.word_66, global_word_91, Stable.closed_word_66, global_closed_91, Stable.expr_word_66, global_expr_91.
 rewrite top_word_61.
 reflexivity. Qed. Opaque Stable.word_66 global_word_91.
Transparent Stable.word_67 global_word_92. Lemma top_word_67 v : Stable.word_67 (top_global_leaves v) = global_word_92 v.
Proof. unfold Stable.word_67, global_word_92, Stable.closed_word_67, global_closed_92, Stable.expr_word_67, global_expr_92.
 rewrite top_word_65 top_word_66.
 reflexivity. Qed. Opaque Stable.word_67 global_word_92.
Transparent Stable.word_68 global_word_93. Lemma top_word_68 v : Stable.word_68 (top_global_leaves v) = global_word_93 v.
Proof. unfold Stable.word_68, global_word_93, Stable.closed_word_68, global_closed_93, Stable.expr_word_68, global_expr_93.
 rewrite top_word_60.
 reflexivity. Qed. Opaque Stable.word_68 global_word_93.
Transparent Stable.word_69 global_word_94. Lemma top_word_69 v : Stable.word_69 (top_global_leaves v) = global_word_94 v.
Proof. unfold Stable.word_69, global_word_94, Stable.closed_word_69, global_closed_94, Stable.expr_word_69, global_expr_94.
 rewrite top_word_59 top_word_60.
 reflexivity. Qed. Opaque Stable.word_69 global_word_94.
Transparent Stable.word_70 global_word_95. Lemma top_word_70 v : Stable.word_70 (top_global_leaves v) = global_word_95 v.
Proof. unfold Stable.word_70, global_word_95, Stable.closed_word_70, global_closed_95, Stable.expr_word_70, global_expr_95.
 rewrite top_word_60 top_word_68.
 reflexivity. Qed. Opaque Stable.word_70 global_word_95.
Transparent Stable.word_71 global_word_96. Lemma top_word_71 v : Stable.word_71 (top_global_leaves v) = global_word_96 v.
Proof. unfold Stable.word_71, global_word_96, Stable.closed_word_71, global_closed_96, Stable.expr_word_71, global_expr_96.
 rewrite top_word_69 top_word_70.
 reflexivity. Qed. Opaque Stable.word_71 global_word_96.
Transparent Stable.word_72 global_word_97. Lemma top_word_72 v : Stable.word_72 (top_global_leaves v) = global_word_97 v.
Proof. unfold Stable.word_72, global_word_97, Stable.closed_word_72, global_closed_97, Stable.expr_word_72, global_expr_97.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_72 global_word_97.
Transparent Stable.word_73 global_word_98. Lemma top_word_73 v : Stable.word_73 (top_global_leaves v) = global_word_98 v.
Proof. unfold Stable.word_73, global_word_98, Stable.closed_word_73, global_closed_98, Stable.expr_word_73, global_expr_98.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_73 global_word_98.
Transparent Stable.word_74 global_word_99. Lemma top_word_74 v : Stable.word_74 (top_global_leaves v) = global_word_99 v.
Proof. unfold Stable.word_74, global_word_99, Stable.closed_word_74, global_closed_99, Stable.expr_word_74, global_expr_99.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_74 global_word_99.
Transparent Stable.word_75 global_word_100. Lemma top_word_75 v : Stable.word_75 (top_global_leaves v) = global_word_100 v.
Proof. unfold Stable.word_75, global_word_100, Stable.closed_word_75, global_closed_100, Stable.expr_word_75, global_expr_100.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_75 global_word_100.
Transparent Stable.word_76 global_word_101. Lemma top_word_76 v : Stable.word_76 (top_global_leaves v) = global_word_101 v.
Proof. unfold Stable.word_76, global_word_101, Stable.closed_word_76, global_closed_101, Stable.expr_word_76, global_expr_101.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_76 global_word_101.
Transparent Stable.word_77 global_word_102. Lemma top_word_77 v : Stable.word_77 (top_global_leaves v) = global_word_102 v.
Proof. unfold Stable.word_77, global_word_102, Stable.closed_word_77, global_closed_102, Stable.expr_word_77, global_expr_102.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_77 global_word_102.
Transparent Stable.word_78 global_word_103. Lemma top_word_78 v : Stable.word_78 (top_global_leaves v) = global_word_103 v.
Proof. unfold Stable.word_78, global_word_103, Stable.closed_word_78, global_closed_103, Stable.expr_word_78, global_expr_103.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_78 global_word_103.
Transparent Stable.word_79 global_word_104. Lemma top_word_79 v : Stable.word_79 (top_global_leaves v) = global_word_104 v.
Proof. unfold Stable.word_79, global_word_104, Stable.closed_word_79, global_closed_104, Stable.expr_word_79, global_expr_104.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_79 global_word_104.
Transparent Stable.word_80 global_word_105. Lemma top_word_80 v : Stable.word_80 (top_global_leaves v) = global_word_105 v.
Proof. unfold Stable.word_80, global_word_105, Stable.closed_word_80, global_closed_105, Stable.expr_word_80, global_expr_105.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_80 global_word_105.
Transparent Stable.word_81 global_word_106. Lemma top_word_81 v : Stable.word_81 (top_global_leaves v) = global_word_106 v.
Proof. unfold Stable.word_81, global_word_106, Stable.closed_word_81, global_closed_106, Stable.expr_word_81, global_expr_106.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_81 global_word_106.
Transparent Stable.word_82 global_word_107. Lemma top_word_82 v : Stable.word_82 (top_global_leaves v) = global_word_107 v.
Proof. unfold Stable.word_82, global_word_107, Stable.closed_word_82, global_closed_107, Stable.expr_word_82, global_expr_107.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_82 global_word_107.
Transparent Stable.word_83 global_word_108. Lemma top_word_83 v : Stable.word_83 (top_global_leaves v) = global_word_108 v.
Proof. unfold Stable.word_83, global_word_108, Stable.closed_word_83, global_closed_108, Stable.expr_word_83, global_expr_108.
 rewrite top_word_71.
 reflexivity. Qed. Opaque Stable.word_83 global_word_108.
Transparent Stable.word_84 global_word_109. Lemma top_word_84 v : Stable.word_84 (top_global_leaves v) = global_word_109 v.
Proof. unfold Stable.word_84, global_word_109, Stable.closed_word_84, global_closed_109, Stable.expr_word_84, global_expr_109.
 rewrite top_word_2.
 reflexivity. Qed. Opaque Stable.word_84 global_word_109.
Transparent Stable.word_85 global_word_110. Lemma top_word_85 v : Stable.word_85 (top_global_leaves v) = global_word_110 v.
Proof. unfold Stable.word_85, global_word_110, Stable.closed_word_85, global_closed_110, Stable.expr_word_85, global_expr_110.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_85 global_word_110.
Transparent Stable.word_86 global_word_111. Lemma top_word_86 v : Stable.word_86 (top_global_leaves v) = global_word_111 v.
Proof. unfold Stable.word_86, global_word_111, Stable.closed_word_86, global_closed_111, Stable.expr_word_86, global_expr_111.
 rewrite top_word_39 top_word_85.
 reflexivity. Qed. Opaque Stable.word_86 global_word_111.
Transparent Stable.word_87 global_word_112. Lemma top_word_87 v : Stable.word_87 (top_global_leaves v) = global_word_112 v.
Proof. unfold Stable.word_87, global_word_112, Stable.closed_word_87, global_closed_112, Stable.expr_word_87, global_expr_112.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_87 global_word_112.
Transparent Stable.word_88 global_word_113. Lemma top_word_88 v : Stable.word_88 (top_global_leaves v) = global_word_113 v.
Proof. unfold Stable.word_88, global_word_113, Stable.closed_word_88, global_closed_113, Stable.expr_word_88, global_expr_113.
 rewrite top_word_39 top_word_86 top_word_87.
 reflexivity. Qed. Opaque Stable.word_88 global_word_113.
Transparent Stable.word_89 global_word_114. Lemma top_word_89 v : Stable.word_89 (top_global_leaves v) = global_word_114 v.
Proof. unfold Stable.word_89, global_word_114, Stable.closed_word_89, global_closed_114, Stable.expr_word_89, global_expr_114.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_89 global_word_114.
Transparent Stable.word_90 global_word_115. Lemma top_word_90 v : Stable.word_90 (top_global_leaves v) = global_word_115 v.
Proof. unfold Stable.word_90, global_word_115, Stable.closed_word_90, global_closed_115, Stable.expr_word_90, global_expr_115.
 rewrite top_word_51 top_word_88 top_word_89.
 reflexivity. Qed. Opaque Stable.word_90 global_word_115.
Transparent Stable.word_91 global_word_116. Lemma top_word_91 v : Stable.word_91 (top_global_leaves v) = global_word_116 v.
Proof. unfold Stable.word_91, global_word_116, Stable.closed_word_91, global_closed_116, Stable.expr_word_91, global_expr_116.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_91 global_word_116.
Transparent Stable.word_92 global_word_117. Lemma top_word_92 v : Stable.word_92 (top_global_leaves v) = global_word_117 v.
Proof. unfold Stable.word_92, global_word_117, Stable.closed_word_92, global_closed_117, Stable.expr_word_92, global_expr_117.
 rewrite top_word_54 top_word_90 top_word_91.
 reflexivity. Qed. Opaque Stable.word_92 global_word_117.
Transparent Stable.word_93 global_word_118. Lemma top_word_93 v : Stable.word_93 (top_global_leaves v) = global_word_118 v.
Proof. unfold Stable.word_93, global_word_118, Stable.closed_word_93, global_closed_118, Stable.expr_word_93, global_expr_118.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_93 global_word_118.
Transparent Stable.word_94 global_word_119. Lemma top_word_94 v : Stable.word_94 (top_global_leaves v) = global_word_119 v.
Proof. unfold Stable.word_94, global_word_119, Stable.closed_word_94, global_closed_119, Stable.expr_word_94, global_expr_119.
 rewrite top_word_42 top_word_92 top_word_93.
 reflexivity. Qed. Opaque Stable.word_94 global_word_119.
Transparent Stable.word_95 global_word_120. Lemma top_word_95 v : Stable.word_95 (top_global_leaves v) = global_word_120 v.
Proof. unfold Stable.word_95, global_word_120, Stable.closed_word_95, global_closed_120, Stable.expr_word_95, global_expr_120.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_95 global_word_120.
Transparent Stable.word_96 global_word_121. Lemma top_word_96 v : Stable.word_96 (top_global_leaves v) = global_word_121 v.
Proof. unfold Stable.word_96, global_word_121, Stable.closed_word_96, global_closed_121, Stable.expr_word_96, global_expr_121.
 rewrite top_word_42 top_word_94 top_word_95.
 reflexivity. Qed. Opaque Stable.word_96 global_word_121.
Transparent Stable.word_97 global_word_122. Lemma top_word_97 v : Stable.word_97 (top_global_leaves v) = global_word_122 v.
Proof. unfold Stable.word_97, global_word_122, Stable.closed_word_97, global_closed_122, Stable.expr_word_97, global_expr_122.
 rewrite top_word_96.
 reflexivity. Qed. Opaque Stable.word_97 global_word_122.
Transparent Stable.word_98 global_word_123. Lemma top_word_98 v : Stable.word_98 (top_global_leaves v) = global_word_123 v.
Proof. unfold Stable.word_98, global_word_123, Stable.closed_word_98, global_closed_123, Stable.expr_word_98, global_expr_123.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_98 global_word_123.
Transparent Stable.word_99 global_word_124. Lemma top_word_99 v : Stable.word_99 (top_global_leaves v) = global_word_124 v.
Proof. unfold Stable.word_99, global_word_124, Stable.closed_word_99, global_closed_124, Stable.expr_word_99, global_expr_124.
 rewrite top_word_98.
 reflexivity. Qed. Opaque Stable.word_99 global_word_124.
Transparent Stable.word_100 global_word_125. Lemma top_word_100 v : Stable.word_100 (top_global_leaves v) = global_word_125 v.
Proof. unfold Stable.word_100, global_word_125, Stable.closed_word_100, global_closed_125, Stable.expr_word_100, global_expr_125.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_100 global_word_125.
Transparent Stable.word_101 global_word_126. Lemma top_word_101 v : Stable.word_101 (top_global_leaves v) = global_word_126 v.
Proof. unfold Stable.word_101, global_word_126, Stable.closed_word_101, global_closed_126, Stable.expr_word_101, global_expr_126.
 rewrite top_word_99 top_word_100.
 reflexivity. Qed. Opaque Stable.word_101 global_word_126.
Transparent Stable.word_102 global_word_127. Lemma top_word_102 v : Stable.word_102 (top_global_leaves v) = global_word_127 v.
Proof. unfold Stable.word_102, global_word_127, Stable.closed_word_102, global_closed_127, Stable.expr_word_102, global_expr_127.
 rewrite top_word_45.
 reflexivity. Qed. Opaque Stable.word_102 global_word_127.
Transparent Stable.word_103 global_word_128. Lemma top_word_103 v : Stable.word_103 (top_global_leaves v) = global_word_128 v.
Proof. unfold Stable.word_103, global_word_128, Stable.closed_word_103, global_closed_128, Stable.expr_word_103, global_expr_128.
 rewrite top_word_101 top_word_102.
 reflexivity. Qed. Opaque Stable.word_103 global_word_128.
Transparent Stable.word_104 global_word_129. Lemma top_word_104 v : Stable.word_104 (top_global_leaves v) = global_word_129 v.
Proof. unfold Stable.word_104, global_word_129, Stable.closed_word_104, global_closed_129, Stable.expr_word_104, global_expr_129.
 rewrite top_word_97.
 reflexivity. Qed. Opaque Stable.word_104 global_word_129.
Transparent Stable.word_105 global_word_130. Lemma top_word_105 v : Stable.word_105 (top_global_leaves v) = global_word_130 v.
Proof. unfold Stable.word_105, global_word_130, Stable.closed_word_105, global_closed_130, Stable.expr_word_105, global_expr_130.
 rewrite top_word_96 top_word_103.
 reflexivity. Qed. Opaque Stable.word_105 global_word_130.
Transparent Stable.word_106 global_word_131. Lemma top_word_106 v : Stable.word_106 (top_global_leaves v) = global_word_131 v.
Proof. unfold Stable.word_106, global_word_131, Stable.closed_word_106, global_closed_131, Stable.expr_word_106, global_expr_131.
 rewrite top_word_104.
 reflexivity. Qed. Opaque Stable.word_106 global_word_131.
Transparent Stable.word_107 global_word_132. Lemma top_word_107 v : Stable.word_107 (top_global_leaves v) = global_word_132 v.
Proof. unfold Stable.word_107, global_word_132, Stable.closed_word_107, global_closed_132, Stable.expr_word_107, global_expr_132.
 rewrite top_word_105 top_word_106.
 reflexivity. Qed. Opaque Stable.word_107 global_word_132.
Transparent Stable.word_108 global_word_133. Lemma top_word_108 v : Stable.word_108 (top_global_leaves v) = global_word_133 v.
Proof. unfold Stable.word_108, global_word_133, Stable.closed_word_108, global_closed_133, Stable.expr_word_108, global_expr_133.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_108 global_word_133.
Transparent Stable.word_109 global_word_134. Lemma top_word_109 v : Stable.word_109 (top_global_leaves v) = global_word_134 v.
Proof. unfold Stable.word_109, global_word_134, Stable.closed_word_109, global_closed_134, Stable.expr_word_109, global_expr_134.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_109 global_word_134.
Transparent Stable.word_110 global_word_135. Lemma top_word_110 v : Stable.word_110 (top_global_leaves v) = global_word_135 v.
Proof. unfold Stable.word_110, global_word_135, Stable.closed_word_110, global_closed_135, Stable.expr_word_110, global_expr_135.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_110 global_word_135.
Transparent Stable.word_111 global_word_136. Lemma top_word_111 v : Stable.word_111 (top_global_leaves v) = global_word_136 v.
Proof. unfold Stable.word_111, global_word_136, Stable.closed_word_111, global_closed_136, Stable.expr_word_111, global_expr_136.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_111 global_word_136.
Transparent Stable.word_112 global_word_137. Lemma top_word_112 v : Stable.word_112 (top_global_leaves v) = global_word_137 v.
Proof. unfold Stable.word_112, global_word_137, Stable.closed_word_112, global_closed_137, Stable.expr_word_112, global_expr_137.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_112 global_word_137.
Transparent Stable.word_113 global_word_138. Lemma top_word_113 v : Stable.word_113 (top_global_leaves v) = global_word_138 v.
Proof. unfold Stable.word_113, global_word_138, Stable.closed_word_113, global_closed_138, Stable.expr_word_113, global_expr_138.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_113 global_word_138.
Transparent Stable.word_114 global_word_139. Lemma top_word_114 v : Stable.word_114 (top_global_leaves v) = global_word_139 v.
Proof. unfold Stable.word_114, global_word_139, Stable.closed_word_114, global_closed_139, Stable.expr_word_114, global_expr_139.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_114 global_word_139.
Transparent Stable.word_115 global_word_140. Lemma top_word_115 v : Stable.word_115 (top_global_leaves v) = global_word_140 v.
Proof. unfold Stable.word_115, global_word_140, Stable.closed_word_115, global_closed_140, Stable.expr_word_115, global_expr_140.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_115 global_word_140.
Transparent Stable.word_116 global_word_141. Lemma top_word_116 v : Stable.word_116 (top_global_leaves v) = global_word_141 v.
Proof. unfold Stable.word_116, global_word_141, Stable.closed_word_116, global_closed_141, Stable.expr_word_116, global_expr_141.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_116 global_word_141.
Transparent Stable.word_117 global_word_142. Lemma top_word_117 v : Stable.word_117 (top_global_leaves v) = global_word_142 v.
Proof. unfold Stable.word_117, global_word_142, Stable.closed_word_117, global_closed_142, Stable.expr_word_117, global_expr_142.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_117 global_word_142.
Transparent Stable.word_118 global_word_143. Lemma top_word_118 v : Stable.word_118 (top_global_leaves v) = global_word_143 v.
Proof. unfold Stable.word_118, global_word_143, Stable.closed_word_118, global_closed_143, Stable.expr_word_118, global_expr_143.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_118 global_word_143.
Transparent Stable.word_119 global_word_144. Lemma top_word_119 v : Stable.word_119 (top_global_leaves v) = global_word_144 v.
Proof. unfold Stable.word_119, global_word_144, Stable.closed_word_119, global_closed_144, Stable.expr_word_119, global_expr_144.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_119 global_word_144.
Transparent Stable.word_120 global_word_145. Lemma top_word_120 v : Stable.word_120 (top_global_leaves v) = global_word_145 v.
Proof. unfold Stable.word_120, global_word_145, Stable.closed_word_120, global_closed_145, Stable.expr_word_120, global_expr_145.
 rewrite top_word_107.
 reflexivity. Qed. Opaque Stable.word_120 global_word_145.
Transparent Stable.word_121 global_word_146. Lemma top_word_121 v : Stable.word_121 (top_global_leaves v) = global_word_146 v.
Proof. unfold Stable.word_121, global_word_146, Stable.closed_word_121, global_closed_146, Stable.expr_word_121, global_expr_146.
 rewrite top_word_2.
 reflexivity. Qed. Opaque Stable.word_121 global_word_146.
Transparent Stable.word_122 global_word_147. Lemma top_word_122 v : Stable.word_122 (top_global_leaves v) = global_word_147 v.
Proof. unfold Stable.word_122, global_word_147, Stable.closed_word_122, global_closed_147, Stable.expr_word_122, global_expr_147.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_122 global_word_147.
Transparent Stable.word_123 global_word_148. Lemma top_word_123 v : Stable.word_123 (top_global_leaves v) = global_word_148 v.
Proof. unfold Stable.word_123, global_word_148, Stable.closed_word_123, global_closed_148, Stable.expr_word_123, global_expr_148.
 rewrite top_word_39 top_word_122.
 reflexivity. Qed. Opaque Stable.word_123 global_word_148.
Transparent Stable.word_124 global_word_149. Lemma top_word_124 v : Stable.word_124 (top_global_leaves v) = global_word_149 v.
Proof. unfold Stable.word_124, global_word_149, Stable.closed_word_124, global_closed_149, Stable.expr_word_124, global_expr_149.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_124 global_word_149.
Transparent Stable.word_125 global_word_150. Lemma top_word_125 v : Stable.word_125 (top_global_leaves v) = global_word_150 v.
Proof. unfold Stable.word_125, global_word_150, Stable.closed_word_125, global_closed_150, Stable.expr_word_125, global_expr_150.
 rewrite top_word_39 top_word_123 top_word_124.
 reflexivity. Qed. Opaque Stable.word_125 global_word_150.
Transparent Stable.word_126 global_word_151. Lemma top_word_126 v : Stable.word_126 (top_global_leaves v) = global_word_151 v.
Proof. unfold Stable.word_126, global_word_151, Stable.closed_word_126, global_closed_151, Stable.expr_word_126, global_expr_151.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_126 global_word_151.
Transparent Stable.word_127 global_word_152. Lemma top_word_127 v : Stable.word_127 (top_global_leaves v) = global_word_152 v.
Proof. unfold Stable.word_127, global_word_152, Stable.closed_word_127, global_closed_152, Stable.expr_word_127, global_expr_152.
 rewrite top_word_51 top_word_125 top_word_126.
 reflexivity. Qed. Opaque Stable.word_127 global_word_152.
Transparent Stable.word_128 global_word_153. Lemma top_word_128 v : Stable.word_128 (top_global_leaves v) = global_word_153 v.
Proof. unfold Stable.word_128, global_word_153, Stable.closed_word_128, global_closed_153, Stable.expr_word_128, global_expr_153.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_128 global_word_153.
Transparent Stable.word_129 global_word_154. Lemma top_word_129 v : Stable.word_129 (top_global_leaves v) = global_word_154 v.
Proof. unfold Stable.word_129, global_word_154, Stable.closed_word_129, global_closed_154, Stable.expr_word_129, global_expr_154.
 rewrite top_word_54 top_word_127 top_word_128.
 reflexivity. Qed. Opaque Stable.word_129 global_word_154.
Transparent Stable.word_130 global_word_155. Lemma top_word_130 v : Stable.word_130 (top_global_leaves v) = global_word_155 v.
Proof. unfold Stable.word_130, global_word_155, Stable.closed_word_130, global_closed_155, Stable.expr_word_130, global_expr_155.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_130 global_word_155.
Transparent Stable.word_131 global_word_156. Lemma top_word_131 v : Stable.word_131 (top_global_leaves v) = global_word_156 v.
Proof. unfold Stable.word_131, global_word_156, Stable.closed_word_131, global_closed_156, Stable.expr_word_131, global_expr_156.
 rewrite top_word_42 top_word_129 top_word_130.
 reflexivity. Qed. Opaque Stable.word_131 global_word_156.
Transparent Stable.word_132 global_word_157. Lemma top_word_132 v : Stable.word_132 (top_global_leaves v) = global_word_157 v.
Proof. unfold Stable.word_132, global_word_157, Stable.closed_word_132, global_closed_157, Stable.expr_word_132, global_expr_157.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_132 global_word_157.
Transparent Stable.word_133 global_word_158. Lemma top_word_133 v : Stable.word_133 (top_global_leaves v) = global_word_158 v.
Proof. unfold Stable.word_133, global_word_158, Stable.closed_word_133, global_closed_158, Stable.expr_word_133, global_expr_158.
 rewrite top_word_42 top_word_131 top_word_132.
 reflexivity. Qed. Opaque Stable.word_133 global_word_158.
Transparent Stable.word_134 global_word_159. Lemma top_word_134 v : Stable.word_134 (top_global_leaves v) = global_word_159 v.
Proof. unfold Stable.word_134, global_word_159, Stable.closed_word_134, global_closed_159, Stable.expr_word_134, global_expr_159.
 rewrite top_word_133.
 reflexivity. Qed. Opaque Stable.word_134 global_word_159.
Transparent Stable.word_135 global_word_160. Lemma top_word_135 v : Stable.word_135 (top_global_leaves v) = global_word_160 v.
Proof. unfold Stable.word_135, global_word_160, Stable.closed_word_135, global_closed_160, Stable.expr_word_135, global_expr_160.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_135 global_word_160.
Transparent Stable.word_136 global_word_161. Lemma top_word_136 v : Stable.word_136 (top_global_leaves v) = global_word_161 v.
Proof. unfold Stable.word_136, global_word_161, Stable.closed_word_136, global_closed_161, Stable.expr_word_136, global_expr_161.
 rewrite top_word_135.
 reflexivity. Qed. Opaque Stable.word_136 global_word_161.
Transparent Stable.word_137 global_word_162. Lemma top_word_137 v : Stable.word_137 (top_global_leaves v) = global_word_162 v.
Proof. unfold Stable.word_137, global_word_162, Stable.closed_word_137, global_closed_162, Stable.expr_word_137, global_expr_162.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_137 global_word_162.
Transparent Stable.word_138 global_word_163. Lemma top_word_138 v : Stable.word_138 (top_global_leaves v) = global_word_163 v.
Proof. unfold Stable.word_138, global_word_163, Stable.closed_word_138, global_closed_163, Stable.expr_word_138, global_expr_163.
 rewrite top_word_136 top_word_137.
 reflexivity. Qed. Opaque Stable.word_138 global_word_163.
Transparent Stable.word_139 global_word_164. Lemma top_word_139 v : Stable.word_139 (top_global_leaves v) = global_word_164 v.
Proof. unfold Stable.word_139, global_word_164, Stable.closed_word_139, global_closed_164, Stable.expr_word_139, global_expr_164.
 rewrite top_word_84.
 reflexivity. Qed. Opaque Stable.word_139 global_word_164.
Transparent Stable.word_140 global_word_165. Lemma top_word_140 v : Stable.word_140 (top_global_leaves v) = global_word_165 v.
Proof. unfold Stable.word_140, global_word_165, Stable.closed_word_140, global_closed_165, Stable.expr_word_140, global_expr_165.
 rewrite top_word_138 top_word_139.
 reflexivity. Qed. Opaque Stable.word_140 global_word_165.
Transparent Stable.word_141 global_word_166. Lemma top_word_141 v : Stable.word_141 (top_global_leaves v) = global_word_166 v.
Proof. unfold Stable.word_141, global_word_166, Stable.closed_word_141, global_closed_166, Stable.expr_word_141, global_expr_166.
 rewrite top_word_134.
 reflexivity. Qed. Opaque Stable.word_141 global_word_166.
Transparent Stable.word_142 global_word_167. Lemma top_word_142 v : Stable.word_142 (top_global_leaves v) = global_word_167 v.
Proof. unfold Stable.word_142, global_word_167, Stable.closed_word_142, global_closed_167, Stable.expr_word_142, global_expr_167.
 rewrite top_word_133 top_word_140.
 reflexivity. Qed. Opaque Stable.word_142 global_word_167.
Transparent Stable.word_143 global_word_168. Lemma top_word_143 v : Stable.word_143 (top_global_leaves v) = global_word_168 v.
Proof. unfold Stable.word_143, global_word_168, Stable.closed_word_143, global_closed_168, Stable.expr_word_143, global_expr_168.
 rewrite top_word_141.
 reflexivity. Qed. Opaque Stable.word_143 global_word_168.
Transparent Stable.word_144 global_word_169. Lemma top_word_144 v : Stable.word_144 (top_global_leaves v) = global_word_169 v.
Proof. unfold Stable.word_144, global_word_169, Stable.closed_word_144, global_closed_169, Stable.expr_word_144, global_expr_169.
 rewrite top_word_142 top_word_143.
 reflexivity. Qed. Opaque Stable.word_144 global_word_169.
Transparent Stable.word_145 global_word_170. Lemma top_word_145 v : Stable.word_145 (top_global_leaves v) = global_word_170 v.
Proof. unfold Stable.word_145, global_word_170, Stable.closed_word_145, global_closed_170, Stable.expr_word_145, global_expr_170.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_145 global_word_170.
Transparent Stable.word_146 global_word_171. Lemma top_word_146 v : Stable.word_146 (top_global_leaves v) = global_word_171 v.
Proof. unfold Stable.word_146, global_word_171, Stable.closed_word_146, global_closed_171, Stable.expr_word_146, global_expr_171.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_146 global_word_171.
Transparent Stable.word_147 global_word_172. Lemma top_word_147 v : Stable.word_147 (top_global_leaves v) = global_word_172 v.
Proof. unfold Stable.word_147, global_word_172, Stable.closed_word_147, global_closed_172, Stable.expr_word_147, global_expr_172.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_147 global_word_172.
Transparent Stable.word_148 global_word_173. Lemma top_word_148 v : Stable.word_148 (top_global_leaves v) = global_word_173 v.
Proof. unfold Stable.word_148, global_word_173, Stable.closed_word_148, global_closed_173, Stable.expr_word_148, global_expr_173.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_148 global_word_173.
Transparent Stable.word_149 global_word_174. Lemma top_word_149 v : Stable.word_149 (top_global_leaves v) = global_word_174 v.
Proof. unfold Stable.word_149, global_word_174, Stable.closed_word_149, global_closed_174, Stable.expr_word_149, global_expr_174.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_149 global_word_174.
Transparent Stable.word_150 global_word_175. Lemma top_word_150 v : Stable.word_150 (top_global_leaves v) = global_word_175 v.
Proof. unfold Stable.word_150, global_word_175, Stable.closed_word_150, global_closed_175, Stable.expr_word_150, global_expr_175.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_150 global_word_175.
Transparent Stable.word_151 global_word_176. Lemma top_word_151 v : Stable.word_151 (top_global_leaves v) = global_word_176 v.
Proof. unfold Stable.word_151, global_word_176, Stable.closed_word_151, global_closed_176, Stable.expr_word_151, global_expr_176.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_151 global_word_176.
Transparent Stable.word_152 global_word_177. Lemma top_word_152 v : Stable.word_152 (top_global_leaves v) = global_word_177 v.
Proof. unfold Stable.word_152, global_word_177, Stable.closed_word_152, global_closed_177, Stable.expr_word_152, global_expr_177.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_152 global_word_177.
Transparent Stable.word_153 global_word_178. Lemma top_word_153 v : Stable.word_153 (top_global_leaves v) = global_word_178 v.
Proof. unfold Stable.word_153, global_word_178, Stable.closed_word_153, global_closed_178, Stable.expr_word_153, global_expr_178.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_153 global_word_178.
Transparent Stable.word_154 global_word_179. Lemma top_word_154 v : Stable.word_154 (top_global_leaves v) = global_word_179 v.
Proof. unfold Stable.word_154, global_word_179, Stable.closed_word_154, global_closed_179, Stable.expr_word_154, global_expr_179.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_154 global_word_179.
Transparent Stable.word_155 global_word_180. Lemma top_word_155 v : Stable.word_155 (top_global_leaves v) = global_word_180 v.
Proof. unfold Stable.word_155, global_word_180, Stable.closed_word_155, global_closed_180, Stable.expr_word_155, global_expr_180.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_155 global_word_180.
Transparent Stable.word_156 global_word_181. Lemma top_word_156 v : Stable.word_156 (top_global_leaves v) = global_word_181 v.
Proof. unfold Stable.word_156, global_word_181, Stable.closed_word_156, global_closed_181, Stable.expr_word_156, global_expr_181.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_156 global_word_181.
Transparent Stable.word_157 global_word_182. Lemma top_word_157 v : Stable.word_157 (top_global_leaves v) = global_word_182 v.
Proof. unfold Stable.word_157, global_word_182, Stable.closed_word_157, global_closed_182, Stable.expr_word_157, global_expr_182.
 rewrite top_word_144.
 reflexivity. Qed. Opaque Stable.word_157 global_word_182.
Transparent Stable.word_158 global_word_183. Lemma top_word_158 v : Stable.word_158 (top_global_leaves v) = global_word_183 v.
Proof. unfold Stable.word_158, global_word_183, Stable.closed_word_158, global_closed_183, Stable.expr_word_158, global_expr_183.
 rewrite top_word_2.
 reflexivity. Qed. Opaque Stable.word_158 global_word_183.
Transparent Stable.word_159 global_word_184. Lemma top_word_159 v : Stable.word_159 (top_global_leaves v) = global_word_184 v.
Proof. unfold Stable.word_159, global_word_184, Stable.closed_word_159, global_closed_184, Stable.expr_word_159, global_expr_184.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_159 global_word_184.
Transparent Stable.word_160 global_word_185. Lemma top_word_160 v : Stable.word_160 (top_global_leaves v) = global_word_185 v.
Proof. unfold Stable.word_160, global_word_185, Stable.closed_word_160, global_closed_185, Stable.expr_word_160, global_expr_185.
 rewrite top_word_39 top_word_159.
 reflexivity. Qed. Opaque Stable.word_160 global_word_185.
Transparent Stable.word_161 global_word_186. Lemma top_word_161 v : Stable.word_161 (top_global_leaves v) = global_word_186 v.
Proof. unfold Stable.word_161, global_word_186, Stable.closed_word_161, global_closed_186, Stable.expr_word_161, global_expr_186.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_161 global_word_186.
Transparent Stable.word_162 global_word_187. Lemma top_word_162 v : Stable.word_162 (top_global_leaves v) = global_word_187 v.
Proof. unfold Stable.word_162, global_word_187, Stable.closed_word_162, global_closed_187, Stable.expr_word_162, global_expr_187.
 rewrite top_word_39 top_word_160 top_word_161.
 reflexivity. Qed. Opaque Stable.word_162 global_word_187.
Transparent Stable.word_163 global_word_188. Lemma top_word_163 v : Stable.word_163 (top_global_leaves v) = global_word_188 v.
Proof. unfold Stable.word_163, global_word_188, Stable.closed_word_163, global_closed_188, Stable.expr_word_163, global_expr_188.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_163 global_word_188.
Transparent Stable.word_164 global_word_189. Lemma top_word_164 v : Stable.word_164 (top_global_leaves v) = global_word_189 v.
Proof. unfold Stable.word_164, global_word_189, Stable.closed_word_164, global_closed_189, Stable.expr_word_164, global_expr_189.
 rewrite top_word_51 top_word_162 top_word_163.
 reflexivity. Qed. Opaque Stable.word_164 global_word_189.
Transparent Stable.word_165 global_word_190. Lemma top_word_165 v : Stable.word_165 (top_global_leaves v) = global_word_190 v.
Proof. unfold Stable.word_165, global_word_190, Stable.closed_word_165, global_closed_190, Stable.expr_word_165, global_expr_190.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_165 global_word_190.
Transparent Stable.word_166 global_word_191. Lemma top_word_166 v : Stable.word_166 (top_global_leaves v) = global_word_191 v.
Proof. unfold Stable.word_166, global_word_191, Stable.closed_word_166, global_closed_191, Stable.expr_word_166, global_expr_191.
 rewrite top_word_54 top_word_164 top_word_165.
 reflexivity. Qed. Opaque Stable.word_166 global_word_191.
Transparent Stable.word_167 global_word_192. Lemma top_word_167 v : Stable.word_167 (top_global_leaves v) = global_word_192 v.
Proof. unfold Stable.word_167, global_word_192, Stable.closed_word_167, global_closed_192, Stable.expr_word_167, global_expr_192.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_167 global_word_192.
Transparent Stable.word_168 global_word_193. Lemma top_word_168 v : Stable.word_168 (top_global_leaves v) = global_word_193 v.
Proof. unfold Stable.word_168, global_word_193, Stable.closed_word_168, global_closed_193, Stable.expr_word_168, global_expr_193.
 rewrite top_word_42 top_word_166 top_word_167.
 reflexivity. Qed. Opaque Stable.word_168 global_word_193.
Transparent Stable.word_169 global_word_194. Lemma top_word_169 v : Stable.word_169 (top_global_leaves v) = global_word_194 v.
Proof. unfold Stable.word_169, global_word_194, Stable.closed_word_169, global_closed_194, Stable.expr_word_169, global_expr_194.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_169 global_word_194.
Transparent Stable.word_170 global_word_195. Lemma top_word_170 v : Stable.word_170 (top_global_leaves v) = global_word_195 v.
Proof. unfold Stable.word_170, global_word_195, Stable.closed_word_170, global_closed_195, Stable.expr_word_170, global_expr_195.
 rewrite top_word_42 top_word_168 top_word_169.
 reflexivity. Qed. Opaque Stable.word_170 global_word_195.
Transparent Stable.word_171 global_word_196. Lemma top_word_171 v : Stable.word_171 (top_global_leaves v) = global_word_196 v.
Proof. unfold Stable.word_171, global_word_196, Stable.closed_word_171, global_closed_196, Stable.expr_word_171, global_expr_196.
 rewrite top_word_170.
 reflexivity. Qed. Opaque Stable.word_171 global_word_196.
Transparent Stable.word_172 global_word_197. Lemma top_word_172 v : Stable.word_172 (top_global_leaves v) = global_word_197 v.
Proof. unfold Stable.word_172, global_word_197, Stable.closed_word_172, global_closed_197, Stable.expr_word_172, global_expr_197.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_172 global_word_197.
Transparent Stable.word_173 global_word_198. Lemma top_word_173 v : Stable.word_173 (top_global_leaves v) = global_word_198 v.
Proof. unfold Stable.word_173, global_word_198, Stable.closed_word_173, global_closed_198, Stable.expr_word_173, global_expr_198.
 rewrite top_word_172.
 reflexivity. Qed. Opaque Stable.word_173 global_word_198.
Transparent Stable.word_174 global_word_199. Lemma top_word_174 v : Stable.word_174 (top_global_leaves v) = global_word_199 v.
Proof. unfold Stable.word_174, global_word_199, Stable.closed_word_174, global_closed_199, Stable.expr_word_174, global_expr_199.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_174 global_word_199.
Transparent Stable.word_175 global_word_200. Lemma top_word_175 v : Stable.word_175 (top_global_leaves v) = global_word_200 v.
Proof. unfold Stable.word_175, global_word_200, Stable.closed_word_175, global_closed_200, Stable.expr_word_175, global_expr_200.
 rewrite top_word_173 top_word_174.
 reflexivity. Qed. Opaque Stable.word_175 global_word_200.
Transparent Stable.word_176 global_word_201. Lemma top_word_176 v : Stable.word_176 (top_global_leaves v) = global_word_201 v.
Proof. unfold Stable.word_176, global_word_201, Stable.closed_word_176, global_closed_201, Stable.expr_word_176, global_expr_201.
 rewrite top_word_121.
 reflexivity. Qed. Opaque Stable.word_176 global_word_201.
Transparent Stable.word_177 global_word_202. Lemma top_word_177 v : Stable.word_177 (top_global_leaves v) = global_word_202 v.
Proof. unfold Stable.word_177, global_word_202, Stable.closed_word_177, global_closed_202, Stable.expr_word_177, global_expr_202.
 rewrite top_word_175 top_word_176.
 reflexivity. Qed. Opaque Stable.word_177 global_word_202.
Transparent Stable.word_178 global_word_203. Lemma top_word_178 v : Stable.word_178 (top_global_leaves v) = global_word_203 v.
Proof. unfold Stable.word_178, global_word_203, Stable.closed_word_178, global_closed_203, Stable.expr_word_178, global_expr_203.
 rewrite top_word_171.
 reflexivity. Qed. Opaque Stable.word_178 global_word_203.
Transparent Stable.word_179 global_word_204. Lemma top_word_179 v : Stable.word_179 (top_global_leaves v) = global_word_204 v.
Proof. unfold Stable.word_179, global_word_204, Stable.closed_word_179, global_closed_204, Stable.expr_word_179, global_expr_204.
 rewrite top_word_170 top_word_178.
 reflexivity. Qed. Opaque Stable.word_179 global_word_204.
Transparent Stable.word_180 global_word_205. Lemma top_word_180 v : Stable.word_180 (top_global_leaves v) = global_word_205 v.
Proof. unfold Stable.word_180, global_word_205, Stable.closed_word_180, global_closed_205, Stable.expr_word_180, global_expr_205.
 rewrite top_word_177 top_word_179.
 reflexivity. Qed. Opaque Stable.word_180 global_word_205.
Transparent Stable.word_181 global_word_206. Lemma top_word_181 v : Stable.word_181 (top_global_leaves v) = global_word_206 v.
Proof. unfold Stable.word_181, global_word_206, Stable.closed_word_181, global_closed_206, Stable.expr_word_181, global_expr_206.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_181 global_word_206.
Transparent Stable.word_182 global_word_207. Lemma top_word_182 v : Stable.word_182 (top_global_leaves v) = global_word_207 v.
Proof. unfold Stable.word_182, global_word_207, Stable.closed_word_182, global_closed_207, Stable.expr_word_182, global_expr_207.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_182 global_word_207.
Transparent Stable.word_183 global_word_208. Lemma top_word_183 v : Stable.word_183 (top_global_leaves v) = global_word_208 v.
Proof. unfold Stable.word_183, global_word_208, Stable.closed_word_183, global_closed_208, Stable.expr_word_183, global_expr_208.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_183 global_word_208.
Transparent Stable.word_184 global_word_209. Lemma top_word_184 v : Stable.word_184 (top_global_leaves v) = global_word_209 v.
Proof. unfold Stable.word_184, global_word_209, Stable.closed_word_184, global_closed_209, Stable.expr_word_184, global_expr_209.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_184 global_word_209.
Transparent Stable.word_185 global_word_210. Lemma top_word_185 v : Stable.word_185 (top_global_leaves v) = global_word_210 v.
Proof. unfold Stable.word_185, global_word_210, Stable.closed_word_185, global_closed_210, Stable.expr_word_185, global_expr_210.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_185 global_word_210.
Transparent Stable.word_186 global_word_211. Lemma top_word_186 v : Stable.word_186 (top_global_leaves v) = global_word_211 v.
Proof. unfold Stable.word_186, global_word_211, Stable.closed_word_186, global_closed_211, Stable.expr_word_186, global_expr_211.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_186 global_word_211.
Transparent Stable.word_187 global_word_212. Lemma top_word_187 v : Stable.word_187 (top_global_leaves v) = global_word_212 v.
Proof. unfold Stable.word_187, global_word_212, Stable.closed_word_187, global_closed_212, Stable.expr_word_187, global_expr_212.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_187 global_word_212.
Transparent Stable.word_188 global_word_213. Lemma top_word_188 v : Stable.word_188 (top_global_leaves v) = global_word_213 v.
Proof. unfold Stable.word_188, global_word_213, Stable.closed_word_188, global_closed_213, Stable.expr_word_188, global_expr_213.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_188 global_word_213.
Transparent Stable.word_189 global_word_214. Lemma top_word_189 v : Stable.word_189 (top_global_leaves v) = global_word_214 v.
Proof. unfold Stable.word_189, global_word_214, Stable.closed_word_189, global_closed_214, Stable.expr_word_189, global_expr_214.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_189 global_word_214.
Transparent Stable.word_190 global_word_215. Lemma top_word_190 v : Stable.word_190 (top_global_leaves v) = global_word_215 v.
Proof. unfold Stable.word_190, global_word_215, Stable.closed_word_190, global_closed_215, Stable.expr_word_190, global_expr_215.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_190 global_word_215.
Transparent Stable.word_191 global_word_216. Lemma top_word_191 v : Stable.word_191 (top_global_leaves v) = global_word_216 v.
Proof. unfold Stable.word_191, global_word_216, Stable.closed_word_191, global_closed_216, Stable.expr_word_191, global_expr_216.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_191 global_word_216.
Transparent Stable.word_192 global_word_217. Lemma top_word_192 v : Stable.word_192 (top_global_leaves v) = global_word_217 v.
Proof. unfold Stable.word_192, global_word_217, Stable.closed_word_192, global_closed_217, Stable.expr_word_192, global_expr_217.
 rewrite top_word_180.
 reflexivity. Qed. Opaque Stable.word_192 global_word_217.
Transparent Stable.word_193 global_word_218. Lemma top_word_193 v : Stable.word_193 (top_global_leaves v) = global_word_218 v.
Proof. unfold Stable.word_193, global_word_218, Stable.closed_word_193, global_closed_218, Stable.expr_word_193, global_expr_218.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_193 global_word_218.
Transparent Stable.word_194 global_word_219. Lemma top_word_194 v : Stable.word_194 (top_global_leaves v) = global_word_219 v.
Proof. unfold Stable.word_194, global_word_219, Stable.closed_word_194, global_closed_219, Stable.expr_word_194, global_expr_219.
 rewrite top_word_193.
 reflexivity. Qed. Opaque Stable.word_194 global_word_219.
Transparent Stable.word_195 global_word_220. Lemma top_word_195 v : Stable.word_195 (top_global_leaves v) = global_word_220 v.
Proof. unfold Stable.word_195, global_word_220, Stable.closed_word_195, global_closed_220, Stable.expr_word_195, global_expr_220.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_195 global_word_220.
Transparent Stable.word_196 global_word_221. Lemma top_word_196 v : Stable.word_196 (top_global_leaves v) = global_word_221 v.
Proof. unfold Stable.word_196, global_word_221, Stable.closed_word_196, global_closed_221, Stable.expr_word_196, global_expr_221.
 rewrite top_word_194 top_word_195.
 reflexivity. Qed. Opaque Stable.word_196 global_word_221.
Transparent Stable.word_197 global_word_222. Lemma top_word_197 v : Stable.word_197 (top_global_leaves v) = global_word_222 v.
Proof. unfold Stable.word_197, global_word_222, Stable.closed_word_197, global_closed_222, Stable.expr_word_197, global_expr_222.
 rewrite top_word_158.
 reflexivity. Qed. Opaque Stable.word_197 global_word_222.
Transparent Stable.word_198 global_word_223. Lemma top_word_198 v : Stable.word_198 (top_global_leaves v) = global_word_223 v.
Proof. unfold Stable.word_198, global_word_223, Stable.closed_word_198, global_closed_223, Stable.expr_word_198, global_expr_223.
 rewrite top_word_196 top_word_197.
 reflexivity. Qed. Opaque Stable.word_198 global_word_223.
Transparent Stable.word_199 global_word_224. Lemma top_word_199 v : Stable.word_199 (top_global_leaves v) = global_word_224 v.
Proof. unfold Stable.word_199, global_word_224, Stable.closed_word_199, global_closed_224, Stable.expr_word_199, global_expr_224.
 rewrite top_word_198.
 reflexivity. Qed. Opaque Stable.word_199 global_word_224.
Transparent Stable.word_200 global_word_225. Lemma top_word_200 v : Stable.word_200 (top_global_leaves v) = global_word_225 v.
Proof. unfold Stable.word_200, global_word_225, Stable.closed_word_200, global_closed_225, Stable.expr_word_200, global_expr_225.
 rewrite top_word_198.
 reflexivity. Qed. Opaque Stable.word_200 global_word_225.
Transparent Stable.word_202 global_word_226. Lemma top_word_202 v : Stable.word_202 (top_global_leaves v) = global_word_226 v.
Proof. unfold Stable.word_202, global_word_226, Stable.closed_word_202, global_closed_226, Stable.expr_word_202, global_expr_226.
 rewrite top_word_4 top_word_72 top_word_201.
 reflexivity. Qed. Opaque Stable.word_202 global_word_226.
Transparent Stable.word_204 global_word_227. Lemma top_word_204 v : Stable.word_204 (top_global_leaves v) = global_word_227 v.
Proof. unfold Stable.word_204, global_word_227, Stable.closed_word_204, global_closed_227, Stable.expr_word_204, global_expr_227.
 rewrite top_word_4 top_word_108 top_word_203.
 reflexivity. Qed. Opaque Stable.word_204 global_word_227.
Transparent Stable.word_206 global_word_228. Lemma top_word_206 v : Stable.word_206 (top_global_leaves v) = global_word_228 v.
Proof. unfold Stable.word_206, global_word_228, Stable.closed_word_206, global_closed_228, Stable.expr_word_206, global_expr_228.
 rewrite top_word_4 top_word_73 top_word_205.
 reflexivity. Qed. Opaque Stable.word_206 global_word_228.
Transparent Stable.word_208 global_word_229. Lemma top_word_208 v : Stable.word_208 (top_global_leaves v) = global_word_229 v.
Proof. unfold Stable.word_208, global_word_229, Stable.closed_word_208, global_closed_229, Stable.expr_word_208, global_expr_229.
 rewrite top_word_4 top_word_109 top_word_207.
 reflexivity. Qed. Opaque Stable.word_208 global_word_229.
Transparent Stable.word_210 global_word_230. Lemma top_word_210 v : Stable.word_210 (top_global_leaves v) = global_word_230 v.
Proof. unfold Stable.word_210, global_word_230, Stable.closed_word_210, global_closed_230, Stable.expr_word_210, global_expr_230.
 rewrite top_word_4 top_word_74 top_word_209.
 reflexivity. Qed. Opaque Stable.word_210 global_word_230.
Transparent Stable.word_212 global_word_231. Lemma top_word_212 v : Stable.word_212 (top_global_leaves v) = global_word_231 v.
Proof. unfold Stable.word_212, global_word_231, Stable.closed_word_212, global_closed_231, Stable.expr_word_212, global_expr_231.
 rewrite top_word_4 top_word_110 top_word_211.
 reflexivity. Qed. Opaque Stable.word_212 global_word_231.
Transparent Stable.word_214 global_word_232. Lemma top_word_214 v : Stable.word_214 (top_global_leaves v) = global_word_232 v.
Proof. unfold Stable.word_214, global_word_232, Stable.closed_word_214, global_closed_232, Stable.expr_word_214, global_expr_232.
 rewrite top_word_4 top_word_145 top_word_213.
 reflexivity. Qed. Opaque Stable.word_214 global_word_232.
Transparent Stable.word_216 global_word_233. Lemma top_word_216 v : Stable.word_216 (top_global_leaves v) = global_word_233 v.
Proof. unfold Stable.word_216, global_word_233, Stable.closed_word_216, global_closed_233, Stable.expr_word_216, global_expr_233.
 rewrite top_word_4 top_word_75 top_word_215.
 reflexivity. Qed. Opaque Stable.word_216 global_word_233.
Transparent Stable.word_218 global_word_234. Lemma top_word_218 v : Stable.word_218 (top_global_leaves v) = global_word_234 v.
Proof. unfold Stable.word_218, global_word_234, Stable.closed_word_218, global_closed_234, Stable.expr_word_218, global_expr_234.
 rewrite top_word_4 top_word_111 top_word_217.
 reflexivity. Qed. Opaque Stable.word_218 global_word_234.
Transparent Stable.word_220 global_word_235. Lemma top_word_220 v : Stable.word_220 (top_global_leaves v) = global_word_235 v.
Proof. unfold Stable.word_220, global_word_235, Stable.closed_word_220, global_closed_235, Stable.expr_word_220, global_expr_235.
 rewrite top_word_4 top_word_146 top_word_219.
 reflexivity. Qed. Opaque Stable.word_220 global_word_235.
Transparent Stable.word_222 global_word_236. Lemma top_word_222 v : Stable.word_222 (top_global_leaves v) = global_word_236 v.
Proof. unfold Stable.word_222, global_word_236, Stable.closed_word_222, global_closed_236, Stable.expr_word_222, global_expr_236.
 rewrite top_word_4 top_word_76 top_word_221.
 reflexivity. Qed. Opaque Stable.word_222 global_word_236.
Transparent Stable.word_224 global_word_237. Lemma top_word_224 v : Stable.word_224 (top_global_leaves v) = global_word_237 v.
Proof. unfold Stable.word_224, global_word_237, Stable.closed_word_224, global_closed_237, Stable.expr_word_224, global_expr_237.
 rewrite top_word_4 top_word_112 top_word_223.
 reflexivity. Qed. Opaque Stable.word_224 global_word_237.
Transparent Stable.word_226 global_word_238. Lemma top_word_226 v : Stable.word_226 (top_global_leaves v) = global_word_238 v.
Proof. unfold Stable.word_226, global_word_238, Stable.closed_word_226, global_closed_238, Stable.expr_word_226, global_expr_238.
 rewrite top_word_4 top_word_147 top_word_225.
 reflexivity. Qed. Opaque Stable.word_226 global_word_238.
Transparent Stable.word_228 global_word_239. Lemma top_word_228 v : Stable.word_228 (top_global_leaves v) = global_word_239 v.
Proof. unfold Stable.word_228, global_word_239, Stable.closed_word_228, global_closed_239, Stable.expr_word_228, global_expr_239.
 rewrite top_word_4 top_word_181 top_word_227.
 reflexivity. Qed. Opaque Stable.word_228 global_word_239.
Transparent Stable.word_230 global_word_240. Lemma top_word_230 v : Stable.word_230 (top_global_leaves v) = global_word_240 v.
Proof. unfold Stable.word_230, global_word_240, Stable.closed_word_230, global_closed_240, Stable.expr_word_230, global_expr_240.
 rewrite top_word_4 top_word_77 top_word_229.
 reflexivity. Qed. Opaque Stable.word_230 global_word_240.
Transparent Stable.word_232 global_word_241. Lemma top_word_232 v : Stable.word_232 (top_global_leaves v) = global_word_241 v.
Proof. unfold Stable.word_232, global_word_241, Stable.closed_word_232, global_closed_241, Stable.expr_word_232, global_expr_241.
 rewrite top_word_4 top_word_113 top_word_231.
 reflexivity. Qed. Opaque Stable.word_232 global_word_241.
Transparent Stable.word_234 global_word_242. Lemma top_word_234 v : Stable.word_234 (top_global_leaves v) = global_word_242 v.
Proof. unfold Stable.word_234, global_word_242, Stable.closed_word_234, global_closed_242, Stable.expr_word_234, global_expr_242.
 rewrite top_word_4 top_word_148 top_word_233.
 reflexivity. Qed. Opaque Stable.word_234 global_word_242.
Transparent Stable.word_236 global_word_243. Lemma top_word_236 v : Stable.word_236 (top_global_leaves v) = global_word_243 v.
Proof. unfold Stable.word_236, global_word_243, Stable.closed_word_236, global_closed_243, Stable.expr_word_236, global_expr_243.
 rewrite top_word_4 top_word_182 top_word_235.
 reflexivity. Qed. Opaque Stable.word_236 global_word_243.
Transparent Stable.word_238 global_word_244. Lemma top_word_238 v : Stable.word_238 (top_global_leaves v) = global_word_244 v.
Proof. unfold Stable.word_238, global_word_244, Stable.closed_word_238, global_closed_244, Stable.expr_word_238, global_expr_244.
 rewrite top_word_4 top_word_78 top_word_237.
 reflexivity. Qed. Opaque Stable.word_238 global_word_244.
Transparent Stable.word_240 global_word_245. Lemma top_word_240 v : Stable.word_240 (top_global_leaves v) = global_word_245 v.
Proof. unfold Stable.word_240, global_word_245, Stable.closed_word_240, global_closed_245, Stable.expr_word_240, global_expr_245.
 rewrite top_word_4 top_word_114 top_word_239.
 reflexivity. Qed. Opaque Stable.word_240 global_word_245.
Transparent Stable.word_242 global_word_246. Lemma top_word_242 v : Stable.word_242 (top_global_leaves v) = global_word_246 v.
Proof. unfold Stable.word_242, global_word_246, Stable.closed_word_242, global_closed_246, Stable.expr_word_242, global_expr_246.
 rewrite top_word_4 top_word_149 top_word_241.
 reflexivity. Qed. Opaque Stable.word_242 global_word_246.
Transparent Stable.word_244 global_word_247. Lemma top_word_244 v : Stable.word_244 (top_global_leaves v) = global_word_247 v.
Proof. unfold Stable.word_244, global_word_247, Stable.closed_word_244, global_closed_247, Stable.expr_word_244, global_expr_247.
 rewrite top_word_4 top_word_183 top_word_243.
 reflexivity. Qed. Opaque Stable.word_244 global_word_247.
Transparent Stable.word_246 global_word_248. Lemma top_word_246 v : Stable.word_246 (top_global_leaves v) = global_word_248 v.
Proof. unfold Stable.word_246, global_word_248, Stable.closed_word_246, global_closed_248, Stable.expr_word_246, global_expr_248.
 rewrite top_word_4 top_word_199 top_word_245.
 reflexivity. Qed. Opaque Stable.word_246 global_word_248.
Transparent Stable.word_248 global_word_249. Lemma top_word_248 v : Stable.word_248 (top_global_leaves v) = global_word_249 v.
Proof. unfold Stable.word_248, global_word_249, Stable.closed_word_248, global_closed_249, Stable.expr_word_248, global_expr_249.
 rewrite top_word_4 top_word_79 top_word_247.
 reflexivity. Qed. Opaque Stable.word_248 global_word_249.
Transparent Stable.word_250 global_word_250. Lemma top_word_250 v : Stable.word_250 (top_global_leaves v) = global_word_250 v.
Proof. unfold Stable.word_250, global_word_250, Stable.closed_word_250, global_closed_250, Stable.expr_word_250, global_expr_250.
 rewrite top_word_4 top_word_115 top_word_249.
 reflexivity. Qed. Opaque Stable.word_250 global_word_250.
Transparent Stable.word_252 global_word_251. Lemma top_word_252 v : Stable.word_252 (top_global_leaves v) = global_word_251 v.
Proof. unfold Stable.word_252, global_word_251, Stable.closed_word_252, global_closed_251, Stable.expr_word_252, global_expr_251.
 rewrite top_word_4 top_word_150 top_word_251.
 reflexivity. Qed. Opaque Stable.word_252 global_word_251.
Transparent Stable.word_254 global_word_252. Lemma top_word_254 v : Stable.word_254 (top_global_leaves v) = global_word_252 v.
Proof. unfold Stable.word_254, global_word_252, Stable.closed_word_254, global_closed_252, Stable.expr_word_254, global_expr_252.
 rewrite top_word_4 top_word_184 top_word_253.
 reflexivity. Qed. Opaque Stable.word_254 global_word_252.
Transparent Stable.word_256 global_word_253. Lemma top_word_256 v : Stable.word_256 (top_global_leaves v) = global_word_253 v.
Proof. unfold Stable.word_256, global_word_253, Stable.closed_word_256, global_closed_253, Stable.expr_word_256, global_expr_253.
 rewrite top_word_4 top_word_200 top_word_255.
 reflexivity. Qed. Opaque Stable.word_256 global_word_253.
Transparent Stable.word_258 global_word_254. Lemma top_word_258 v : Stable.word_258 (top_global_leaves v) = global_word_254 v.
Proof. unfold Stable.word_258, global_word_254, Stable.closed_word_258, global_closed_254, Stable.expr_word_258, global_expr_254.
 rewrite top_word_4 top_word_80 top_word_257.
 reflexivity. Qed. Opaque Stable.word_258 global_word_254.
Transparent Stable.word_260 global_word_255. Lemma top_word_260 v : Stable.word_260 (top_global_leaves v) = global_word_255 v.
Proof. unfold Stable.word_260, global_word_255, Stable.closed_word_260, global_closed_255, Stable.expr_word_260, global_expr_255.
 rewrite top_word_4 top_word_116 top_word_259.
 reflexivity. Qed. Opaque Stable.word_260 global_word_255.
Transparent Stable.word_262 global_word_256. Lemma top_word_262 v : Stable.word_262 (top_global_leaves v) = global_word_256 v.
Proof. unfold Stable.word_262, global_word_256, Stable.closed_word_262, global_closed_256, Stable.expr_word_262, global_expr_256.
 rewrite top_word_4 top_word_151 top_word_261.
 reflexivity. Qed. Opaque Stable.word_262 global_word_256.
Transparent Stable.word_264 global_word_257. Lemma top_word_264 v : Stable.word_264 (top_global_leaves v) = global_word_257 v.
Proof. unfold Stable.word_264, global_word_257, Stable.closed_word_264, global_closed_257, Stable.expr_word_264, global_expr_257.
 rewrite top_word_4 top_word_185 top_word_263.
 reflexivity. Qed. Opaque Stable.word_264 global_word_257.
Transparent Stable.word_266 global_word_258. Lemma top_word_266 v : Stable.word_266 (top_global_leaves v) = global_word_258 v.
Proof. unfold Stable.word_266, global_word_258, Stable.closed_word_266, global_closed_258, Stable.expr_word_266, global_expr_258.
 rewrite top_word_4 top_word_81 top_word_265.
 reflexivity. Qed. Opaque Stable.word_266 global_word_258.
Transparent Stable.word_268 global_word_259. Lemma top_word_268 v : Stable.word_268 (top_global_leaves v) = global_word_259 v.
Proof. unfold Stable.word_268, global_word_259, Stable.closed_word_268, global_closed_259, Stable.expr_word_268, global_expr_259.
 rewrite top_word_4 top_word_117 top_word_267.
 reflexivity. Qed. Opaque Stable.word_268 global_word_259.
Transparent Stable.word_270 global_word_260. Lemma top_word_270 v : Stable.word_270 (top_global_leaves v) = global_word_260 v.
Proof. unfold Stable.word_270, global_word_260, Stable.closed_word_270, global_closed_260, Stable.expr_word_270, global_expr_260.
 rewrite top_word_4 top_word_152 top_word_269.
 reflexivity. Qed. Opaque Stable.word_270 global_word_260.
Transparent Stable.word_272 global_word_261. Lemma top_word_272 v : Stable.word_272 (top_global_leaves v) = global_word_261 v.
Proof. unfold Stable.word_272, global_word_261, Stable.closed_word_272, global_closed_261, Stable.expr_word_272, global_expr_261.
 rewrite top_word_4 top_word_186 top_word_271.
 reflexivity. Qed. Opaque Stable.word_272 global_word_261.
Transparent Stable.word_274 global_word_262. Lemma top_word_274 v : Stable.word_274 (top_global_leaves v) = global_word_262 v.
Proof. unfold Stable.word_274, global_word_262, Stable.closed_word_274, global_closed_262, Stable.expr_word_274, global_expr_262.
 rewrite top_word_4 top_word_82 top_word_273.
 reflexivity. Qed. Opaque Stable.word_274 global_word_262.
Transparent Stable.word_276 global_word_263. Lemma top_word_276 v : Stable.word_276 (top_global_leaves v) = global_word_263 v.
Proof. unfold Stable.word_276, global_word_263, Stable.closed_word_276, global_closed_263, Stable.expr_word_276, global_expr_263.
 rewrite top_word_4 top_word_118 top_word_275.
 reflexivity. Qed. Opaque Stable.word_276 global_word_263.
Transparent Stable.word_278 global_word_264. Lemma top_word_278 v : Stable.word_278 (top_global_leaves v) = global_word_264 v.
Proof. unfold Stable.word_278, global_word_264, Stable.closed_word_278, global_closed_264, Stable.expr_word_278, global_expr_264.
 rewrite top_word_4 top_word_153 top_word_277.
 reflexivity. Qed. Opaque Stable.word_278 global_word_264.
Transparent Stable.word_280 global_word_265. Lemma top_word_280 v : Stable.word_280 (top_global_leaves v) = global_word_265 v.
Proof. unfold Stable.word_280, global_word_265, Stable.closed_word_280, global_closed_265, Stable.expr_word_280, global_expr_265.
 rewrite top_word_4 top_word_187 top_word_279.
 reflexivity. Qed. Opaque Stable.word_280 global_word_265.
Transparent Stable.word_282 global_word_266. Lemma top_word_282 v : Stable.word_282 (top_global_leaves v) = global_word_266 v.
Proof. unfold Stable.word_282, global_word_266, Stable.closed_word_282, global_closed_266, Stable.expr_word_282, global_expr_266.
 rewrite top_word_4 top_word_83 top_word_281.
 reflexivity. Qed. Opaque Stable.word_282 global_word_266.
Transparent Stable.word_284 global_word_267. Lemma top_word_284 v : Stable.word_284 (top_global_leaves v) = global_word_267 v.
Proof. unfold Stable.word_284, global_word_267, Stable.closed_word_284, global_closed_267, Stable.expr_word_284, global_expr_267.
 rewrite top_word_4 top_word_119 top_word_283.
 reflexivity. Qed. Opaque Stable.word_284 global_word_267.
Transparent Stable.word_286 global_word_268. Lemma top_word_286 v : Stable.word_286 (top_global_leaves v) = global_word_268 v.
Proof. unfold Stable.word_286, global_word_268, Stable.closed_word_286, global_closed_268, Stable.expr_word_286, global_expr_268.
 rewrite top_word_4 top_word_154 top_word_285.
 reflexivity. Qed. Opaque Stable.word_286 global_word_268.
Transparent Stable.word_288 global_word_269. Lemma top_word_288 v : Stable.word_288 (top_global_leaves v) = global_word_269 v.
Proof. unfold Stable.word_288, global_word_269, Stable.closed_word_288, global_closed_269, Stable.expr_word_288, global_expr_269.
 rewrite top_word_4 top_word_188 top_word_287.
 reflexivity. Qed. Opaque Stable.word_288 global_word_269.
Transparent Stable.word_290 global_word_270. Lemma top_word_290 v : Stable.word_290 (top_global_leaves v) = global_word_270 v.
Proof. unfold Stable.word_290, global_word_270, Stable.closed_word_290, global_closed_270, Stable.expr_word_290, global_expr_270.
 rewrite top_word_4 top_word_120 top_word_289.
 reflexivity. Qed. Opaque Stable.word_290 global_word_270.
Transparent Stable.word_292 global_word_271. Lemma top_word_292 v : Stable.word_292 (top_global_leaves v) = global_word_271 v.
Proof. unfold Stable.word_292, global_word_271, Stable.closed_word_292, global_closed_271, Stable.expr_word_292, global_expr_271.
 rewrite top_word_4 top_word_155 top_word_291.
 reflexivity. Qed. Opaque Stable.word_292 global_word_271.
Transparent Stable.word_294 global_word_272. Lemma top_word_294 v : Stable.word_294 (top_global_leaves v) = global_word_272 v.
Proof. unfold Stable.word_294, global_word_272, Stable.closed_word_294, global_closed_272, Stable.expr_word_294, global_expr_272.
 rewrite top_word_4 top_word_189 top_word_293.
 reflexivity. Qed. Opaque Stable.word_294 global_word_272.
Transparent Stable.word_296 global_word_273. Lemma top_word_296 v : Stable.word_296 (top_global_leaves v) = global_word_273 v.
Proof. unfold Stable.word_296, global_word_273, Stable.closed_word_296, global_closed_273, Stable.expr_word_296, global_expr_273.
 rewrite top_word_4 top_word_156 top_word_295.
 reflexivity. Qed. Opaque Stable.word_296 global_word_273.
Transparent Stable.word_298 global_word_274. Lemma top_word_298 v : Stable.word_298 (top_global_leaves v) = global_word_274 v.
Proof. unfold Stable.word_298, global_word_274, Stable.closed_word_298, global_closed_274, Stable.expr_word_298, global_expr_274.
 rewrite top_word_4 top_word_190 top_word_297.
 reflexivity. Qed. Opaque Stable.word_298 global_word_274.
Transparent Stable.word_300 global_word_275. Lemma top_word_300 v : Stable.word_300 (top_global_leaves v) = global_word_275 v.
Proof. unfold Stable.word_300, global_word_275, Stable.closed_word_300, global_closed_275, Stable.expr_word_300, global_expr_275.
 rewrite top_word_4 top_word_157 top_word_299.
 reflexivity. Qed. Opaque Stable.word_300 global_word_275.
Transparent Stable.word_302 global_word_276. Lemma top_word_302 v : Stable.word_302 (top_global_leaves v) = global_word_276 v.
Proof. unfold Stable.word_302, global_word_276, Stable.closed_word_302, global_closed_276, Stable.expr_word_302, global_expr_276.
 rewrite top_word_4 top_word_191 top_word_301.
 reflexivity. Qed. Opaque Stable.word_302 global_word_276.
Transparent Stable.word_304 global_word_277. Lemma top_word_304 v : Stable.word_304 (top_global_leaves v) = global_word_277 v.
Proof. unfold Stable.word_304, global_word_277, Stable.closed_word_304, global_closed_277, Stable.expr_word_304, global_expr_277.
 rewrite top_word_4 top_word_192 top_word_303.
 reflexivity. Qed. Opaque Stable.word_304 global_word_277.
Transparent Stable.word_305 global_word_291. Lemma top_word_305 v : Stable.word_305 (top_global_leaves v) = global_word_291 v.
Proof. unfold Stable.word_305, global_word_291, Stable.closed_word_305, global_closed_291, Stable.expr_word_305, global_expr_291.
 rewrite top_port_7_4.
 reflexivity. Qed. Opaque Stable.word_305 global_word_291.
Transparent Stable.word_306 global_word_295. Lemma top_word_306 v : Stable.word_306 (top_global_leaves v) = global_word_295 v.
Proof. unfold Stable.word_306, global_word_295, Stable.closed_word_306, global_closed_295, Stable.expr_word_306, global_expr_295.
 rewrite top_port_7_5.
 reflexivity. Qed. Opaque Stable.word_306 global_word_295.
Transparent Stable.word_307 global_word_309. Lemma top_word_307 v : Stable.word_307 (top_global_leaves v) = global_word_309 v.
Proof. unfold Stable.word_307, global_word_309, Stable.closed_word_307, global_closed_309, Stable.expr_word_307, global_expr_309.
 rewrite top_port_8_4.
 reflexivity. Qed. Opaque Stable.word_307 global_word_309.
Transparent Stable.word_308 global_word_313. Lemma top_word_308 v : Stable.word_308 (top_global_leaves v) = global_word_313 v.
Proof. unfold Stable.word_308, global_word_313, Stable.closed_word_308, global_closed_313, Stable.expr_word_308, global_expr_313.
 rewrite top_port_8_5.
 reflexivity. Qed. Opaque Stable.word_308 global_word_313.
Transparent Stable.word_309 global_word_333. Lemma top_word_309 v : Stable.word_309 (top_global_leaves v) = global_word_333 v.
Proof. unfold Stable.word_309, global_word_333, Stable.closed_word_309, global_closed_333, Stable.expr_word_309, global_expr_333.
 rewrite top_port_9_5.
 reflexivity. Qed. Opaque Stable.word_309 global_word_333.
Transparent Stable.word_310 global_word_337. Lemma top_word_310 v : Stable.word_310 (top_global_leaves v) = global_word_337 v.
Proof. unfold Stable.word_310, global_word_337, Stable.closed_word_310, global_closed_337, Stable.expr_word_310, global_expr_337.
 rewrite top_port_9_6.
 reflexivity. Qed. Opaque Stable.word_310 global_word_337.
Transparent Stable.word_311 global_word_357. Lemma top_word_311 v : Stable.word_311 (top_global_leaves v) = global_word_357 v.
Proof. unfold Stable.word_311, global_word_357, Stable.closed_word_311, global_closed_357, Stable.expr_word_311, global_expr_357.
 rewrite top_port_10_5.
 reflexivity. Qed. Opaque Stable.word_311 global_word_357.
Transparent Stable.word_312 global_word_361. Lemma top_word_312 v : Stable.word_312 (top_global_leaves v) = global_word_361 v.
Proof. unfold Stable.word_312, global_word_361, Stable.closed_word_312, global_closed_361, Stable.expr_word_312, global_expr_361.
 rewrite top_port_10_6.
 reflexivity. Qed. Opaque Stable.word_312 global_word_361.
Transparent Stable.word_313 global_word_416. Lemma top_word_313 v : Stable.word_313 (top_global_leaves v) = global_word_416 v.
Proof. unfold Stable.word_313, global_word_416, Stable.closed_word_313, global_closed_416, Stable.expr_word_313, global_expr_416.
 rewrite top_port_11_7.
 reflexivity. Qed. Opaque Stable.word_313 global_word_416.
Transparent Stable.word_314 global_word_423. Lemma top_word_314 v : Stable.word_314 (top_global_leaves v) = global_word_423 v.
Proof. unfold Stable.word_314, global_word_423, Stable.closed_word_314, global_closed_423, Stable.expr_word_314, global_expr_423.
 rewrite top_port_11_8.
 reflexivity. Qed. Opaque Stable.word_314 global_word_423.
Transparent Stable.word_315 global_word_430. Lemma top_word_315 v : Stable.word_315 (top_global_leaves v) = global_word_430 v.
Proof. unfold Stable.word_315, global_word_430, Stable.closed_word_315, global_closed_430, Stable.expr_word_315, global_expr_430.
 rewrite top_port_11_9.
 reflexivity. Qed. Opaque Stable.word_315 global_word_430.
Transparent Stable.word_316 global_word_485. Lemma top_word_316 v : Stable.word_316 (top_global_leaves v) = global_word_485 v.
Proof. unfold Stable.word_316, global_word_485, Stable.closed_word_316, global_closed_485, Stable.expr_word_316, global_expr_485.
 rewrite top_port_12_7.
 reflexivity. Qed. Opaque Stable.word_316 global_word_485.
Transparent Stable.word_317 global_word_492. Lemma top_word_317 v : Stable.word_317 (top_global_leaves v) = global_word_492 v.
Proof. unfold Stable.word_317, global_word_492, Stable.closed_word_317, global_closed_492, Stable.expr_word_317, global_expr_492.
 rewrite top_port_12_8.
 reflexivity. Qed. Opaque Stable.word_317 global_word_492.
Transparent Stable.word_318 global_word_499. Lemma top_word_318 v : Stable.word_318 (top_global_leaves v) = global_word_499 v.
Proof. unfold Stable.word_318, global_word_499, Stable.closed_word_318, global_closed_499, Stable.expr_word_318, global_expr_499.
 rewrite top_port_12_9.
 reflexivity. Qed. Opaque Stable.word_318 global_word_499.
Transparent Stable.word_319 global_word_554. Lemma top_word_319 v : Stable.word_319 (top_global_leaves v) = global_word_554 v.
Proof. unfold Stable.word_319, global_word_554, Stable.closed_word_319, global_closed_554, Stable.expr_word_319, global_expr_554.
 rewrite top_port_13_7.
 reflexivity. Qed. Opaque Stable.word_319 global_word_554.
Transparent Stable.word_320 global_word_561. Lemma top_word_320 v : Stable.word_320 (top_global_leaves v) = global_word_561 v.
Proof. unfold Stable.word_320, global_word_561, Stable.closed_word_320, global_closed_561, Stable.expr_word_320, global_expr_561.
 rewrite top_port_13_8.
 reflexivity. Qed. Opaque Stable.word_320 global_word_561.
Transparent Stable.word_321 global_word_568. Lemma top_word_321 v : Stable.word_321 (top_global_leaves v) = global_word_568 v.
Proof. unfold Stable.word_321, global_word_568, Stable.closed_word_321, global_closed_568, Stable.expr_word_321, global_expr_568.
 rewrite top_port_13_9.
 reflexivity. Qed. Opaque Stable.word_321 global_word_568.
Transparent Stable.word_322 global_word_623. Lemma top_word_322 v : Stable.word_322 (top_global_leaves v) = global_word_623 v.
Proof. unfold Stable.word_322, global_word_623, Stable.closed_word_322, global_closed_623, Stable.expr_word_322, global_expr_623.
 rewrite top_port_14_7.
 reflexivity. Qed. Opaque Stable.word_322 global_word_623.
Transparent Stable.word_323 global_word_630. Lemma top_word_323 v : Stable.word_323 (top_global_leaves v) = global_word_630 v.
Proof. unfold Stable.word_323, global_word_630, Stable.closed_word_323, global_closed_630, Stable.expr_word_323, global_expr_630.
 rewrite top_port_14_8.
 reflexivity. Qed. Opaque Stable.word_323 global_word_630.
Transparent Stable.word_324 global_word_637. Lemma top_word_324 v : Stable.word_324 (top_global_leaves v) = global_word_637 v.
Proof. unfold Stable.word_324, global_word_637, Stable.closed_word_324, global_closed_637, Stable.expr_word_324, global_expr_637.
 rewrite top_port_14_9.
 reflexivity. Qed. Opaque Stable.word_324 global_word_637.
Transparent Stable.word_325 global_word_692. Lemma top_word_325 v : Stable.word_325 (top_global_leaves v) = global_word_692 v.
Proof. unfold Stable.word_325, global_word_692, Stable.closed_word_325, global_closed_692, Stable.expr_word_325, global_expr_692.
 rewrite top_port_15_7.
 reflexivity. Qed. Opaque Stable.word_325 global_word_692.
Transparent Stable.word_326 global_word_699. Lemma top_word_326 v : Stable.word_326 (top_global_leaves v) = global_word_699 v.
Proof. unfold Stable.word_326, global_word_699, Stable.closed_word_326, global_closed_699, Stable.expr_word_326, global_expr_699.
 rewrite top_port_15_8.
 reflexivity. Qed. Opaque Stable.word_326 global_word_699.
Transparent Stable.word_327 global_word_706. Lemma top_word_327 v : Stable.word_327 (top_global_leaves v) = global_word_706 v.
Proof. unfold Stable.word_327, global_word_706, Stable.closed_word_327, global_closed_706, Stable.expr_word_327, global_expr_706.
 rewrite top_port_15_9.
 reflexivity. Qed. Opaque Stable.word_327 global_word_706.
Transparent Stable.word_328 global_word_761. Lemma top_word_328 v : Stable.word_328 (top_global_leaves v) = global_word_761 v.
Proof. unfold Stable.word_328, global_word_761, Stable.closed_word_328, global_closed_761, Stable.expr_word_328, global_expr_761.
 rewrite top_port_16_7.
 reflexivity. Qed. Opaque Stable.word_328 global_word_761.
Transparent Stable.word_329 global_word_768. Lemma top_word_329 v : Stable.word_329 (top_global_leaves v) = global_word_768 v.
Proof. unfold Stable.word_329, global_word_768, Stable.closed_word_329, global_closed_768, Stable.expr_word_329, global_expr_768.
 rewrite top_port_16_8.
 reflexivity. Qed. Opaque Stable.word_329 global_word_768.
Transparent Stable.word_330 global_word_775. Lemma top_word_330 v : Stable.word_330 (top_global_leaves v) = global_word_775 v.
Proof. unfold Stable.word_330, global_word_775, Stable.closed_word_330, global_closed_775, Stable.expr_word_330, global_expr_775.
 rewrite top_port_16_9.
 reflexivity. Qed. Opaque Stable.word_330 global_word_775.
Transparent Stable.word_331 global_word_830. Lemma top_word_331 v : Stable.word_331 (top_global_leaves v) = global_word_830 v.
Proof. unfold Stable.word_331, global_word_830, Stable.closed_word_331, global_closed_830, Stable.expr_word_331, global_expr_830.
 rewrite top_port_17_7.
 reflexivity. Qed. Opaque Stable.word_331 global_word_830.
Transparent Stable.word_332 global_word_837. Lemma top_word_332 v : Stable.word_332 (top_global_leaves v) = global_word_837 v.
Proof. unfold Stable.word_332, global_word_837, Stable.closed_word_332, global_closed_837, Stable.expr_word_332, global_expr_837.
 rewrite top_port_17_8.
 reflexivity. Qed. Opaque Stable.word_332 global_word_837.
Transparent Stable.word_333 global_word_844. Lemma top_word_333 v : Stable.word_333 (top_global_leaves v) = global_word_844 v.
Proof. unfold Stable.word_333, global_word_844, Stable.closed_word_333, global_closed_844, Stable.expr_word_333, global_expr_844.
 rewrite top_port_17_9.
 reflexivity. Qed. Opaque Stable.word_333 global_word_844.
Transparent Stable.word_334 global_word_899. Lemma top_word_334 v : Stable.word_334 (top_global_leaves v) = global_word_899 v.
Proof. unfold Stable.word_334, global_word_899, Stable.closed_word_334, global_closed_899, Stable.expr_word_334, global_expr_899.
 rewrite top_port_18_7.
 reflexivity. Qed. Opaque Stable.word_334 global_word_899.
Transparent Stable.word_335 global_word_906. Lemma top_word_335 v : Stable.word_335 (top_global_leaves v) = global_word_906 v.
Proof. unfold Stable.word_335, global_word_906, Stable.closed_word_335, global_closed_906, Stable.expr_word_335, global_expr_906.
 rewrite top_port_18_8.
 reflexivity. Qed. Opaque Stable.word_335 global_word_906.
Transparent Stable.word_336 global_word_913. Lemma top_word_336 v : Stable.word_336 (top_global_leaves v) = global_word_913 v.
Proof. unfold Stable.word_336, global_word_913, Stable.closed_word_336, global_closed_913, Stable.expr_word_336, global_expr_913.
 rewrite top_port_18_9.
 reflexivity. Qed. Opaque Stable.word_336 global_word_913.
Transparent Stable.word_337 global_word_933. Lemma top_word_337 v : Stable.word_337 (top_global_leaves v) = global_word_933 v.
Proof. unfold Stable.word_337, global_word_933, Stable.closed_word_337, global_closed_933, Stable.expr_word_337, global_expr_933.
 rewrite top_port_19_5.
 reflexivity. Qed. Opaque Stable.word_337 global_word_933.
Transparent Stable.word_338 global_word_937. Lemma top_word_338 v : Stable.word_338 (top_global_leaves v) = global_word_937 v.
Proof. unfold Stable.word_338, global_word_937, Stable.closed_word_338, global_closed_937, Stable.expr_word_338, global_expr_937.
 rewrite top_port_19_6.
 reflexivity. Qed. Opaque Stable.word_338 global_word_937.
Transparent Stable.word_339 global_word_951. Lemma top_word_339 v : Stable.word_339 (top_global_leaves v) = global_word_951 v.
Proof. unfold Stable.word_339, global_word_951, Stable.closed_word_339, global_closed_951, Stable.expr_word_339, global_expr_951.
 rewrite top_port_20_4.
 reflexivity. Qed. Opaque Stable.word_339 global_word_951.
Transparent Stable.word_340 global_word_955. Lemma top_word_340 v : Stable.word_340 (top_global_leaves v) = global_word_955 v.
Proof. unfold Stable.word_340, global_word_955, Stable.closed_word_340, global_closed_955, Stable.expr_word_340, global_expr_955.
 rewrite top_port_20_5.
 reflexivity. Qed. Opaque Stable.word_340 global_word_955.
Transparent Stable.word_341 global_word_969. Lemma top_word_341 v : Stable.word_341 (top_global_leaves v) = global_word_969 v.
Proof. unfold Stable.word_341, global_word_969, Stable.closed_word_341, global_closed_969, Stable.expr_word_341, global_expr_969.
 rewrite top_port_21_4.
 reflexivity. Qed. Opaque Stable.word_341 global_word_969.
Transparent Stable.word_342 global_word_973. Lemma top_word_342 v : Stable.word_342 (top_global_leaves v) = global_word_973 v.
Proof. unfold Stable.word_342, global_word_973, Stable.closed_word_342, global_closed_973, Stable.expr_word_342, global_expr_973.
 rewrite top_port_21_5.
 reflexivity. Qed. Opaque Stable.word_342 global_word_973.
Transparent Stable.word_343 global_word_987. Lemma top_word_343 v : Stable.word_343 (top_global_leaves v) = global_word_987 v.
Proof. unfold Stable.word_343, global_word_987, Stable.closed_word_343, global_closed_987, Stable.expr_word_343, global_expr_987.
 rewrite top_port_22_4.
 reflexivity. Qed. Opaque Stable.word_343 global_word_987.
Transparent Stable.word_344 global_word_991. Lemma top_word_344 v : Stable.word_344 (top_global_leaves v) = global_word_991 v.
Proof. unfold Stable.word_344, global_word_991, Stable.closed_word_344, global_closed_991, Stable.expr_word_344, global_expr_991.
 rewrite top_port_22_5.
 reflexivity. Qed. Opaque Stable.word_344 global_word_991.
Transparent Stable.word_345 global_word_1005. Lemma top_word_345 v : Stable.word_345 (top_global_leaves v) = global_word_1005 v.
Proof. unfold Stable.word_345, global_word_1005, Stable.closed_word_345, global_closed_1005, Stable.expr_word_345, global_expr_1005.
 rewrite top_port_23_4.
 reflexivity. Qed. Opaque Stable.word_345 global_word_1005.
Transparent Stable.word_346 global_word_1009. Lemma top_word_346 v : Stable.word_346 (top_global_leaves v) = global_word_1009 v.
Proof. unfold Stable.word_346, global_word_1009, Stable.closed_word_346, global_closed_1009, Stable.expr_word_346, global_expr_1009.
 rewrite top_port_23_5.
 reflexivity. Qed. Opaque Stable.word_346 global_word_1009.
Transparent Stable.word_347 global_word_1023. Lemma top_word_347 v : Stable.word_347 (top_global_leaves v) = global_word_1023 v.
Proof. unfold Stable.word_347, global_word_1023, Stable.closed_word_347, global_closed_1023, Stable.expr_word_347, global_expr_1023.
 rewrite top_port_24_4.
 reflexivity. Qed. Opaque Stable.word_347 global_word_1023.
Transparent Stable.word_348 global_word_1027. Lemma top_word_348 v : Stable.word_348 (top_global_leaves v) = global_word_1027 v.
Proof. unfold Stable.word_348, global_word_1027, Stable.closed_word_348, global_closed_1027, Stable.expr_word_348, global_expr_1027.
 rewrite top_port_24_5.
 reflexivity. Qed. Opaque Stable.word_348 global_word_1027.
Transparent Stable.word_349 global_word_1041. Lemma top_word_349 v : Stable.word_349 (top_global_leaves v) = global_word_1041 v.
Proof. unfold Stable.word_349, global_word_1041, Stable.closed_word_349, global_closed_1041, Stable.expr_word_349, global_expr_1041.
 rewrite top_port_25_4.
 reflexivity. Qed. Opaque Stable.word_349 global_word_1041.
Transparent Stable.word_350 global_word_1045. Lemma top_word_350 v : Stable.word_350 (top_global_leaves v) = global_word_1045 v.
Proof. unfold Stable.word_350, global_word_1045, Stable.closed_word_350, global_closed_1045, Stable.expr_word_350, global_expr_1045.
 rewrite top_port_25_5.
 reflexivity. Qed. Opaque Stable.word_350 global_word_1045.
Transparent Stable.word_351 global_word_1059. Lemma top_word_351 v : Stable.word_351 (top_global_leaves v) = global_word_1059 v.
Proof. unfold Stable.word_351, global_word_1059, Stable.closed_word_351, global_closed_1059, Stable.expr_word_351, global_expr_1059.
 rewrite top_port_26_4.
 reflexivity. Qed. Opaque Stable.word_351 global_word_1059.
Transparent Stable.word_352 global_word_1063. Lemma top_word_352 v : Stable.word_352 (top_global_leaves v) = global_word_1063 v.
Proof. unfold Stable.word_352, global_word_1063, Stable.closed_word_352, global_closed_1063, Stable.expr_word_352, global_expr_1063.
 rewrite top_port_26_5.
 reflexivity. Qed. Opaque Stable.word_352 global_word_1063.
Transparent Stable.word_353 global_word_1083. Lemma top_word_353 v : Stable.word_353 (top_global_leaves v) = global_word_1083 v.
Proof. unfold Stable.word_353, global_word_1083, Stable.closed_word_353, global_closed_1083, Stable.expr_word_353, global_expr_1083.
 rewrite top_port_27_5.
 reflexivity. Qed. Opaque Stable.word_353 global_word_1083.
Transparent Stable.word_354 global_word_1087. Lemma top_word_354 v : Stable.word_354 (top_global_leaves v) = global_word_1087 v.
Proof. unfold Stable.word_354, global_word_1087, Stable.closed_word_354, global_closed_1087, Stable.expr_word_354, global_expr_1087.
 rewrite top_port_27_6.
 reflexivity. Qed. Opaque Stable.word_354 global_word_1087.
Transparent Stable.word_355 global_word_1107. Lemma top_word_355 v : Stable.word_355 (top_global_leaves v) = global_word_1107 v.
Proof. unfold Stable.word_355, global_word_1107, Stable.closed_word_355, global_closed_1107, Stable.expr_word_355, global_expr_1107.
 rewrite top_port_28_5.
 reflexivity. Qed. Opaque Stable.word_355 global_word_1107.
Transparent Stable.word_356 global_word_1111. Lemma top_word_356 v : Stable.word_356 (top_global_leaves v) = global_word_1111 v.
Proof. unfold Stable.word_356, global_word_1111, Stable.closed_word_356, global_closed_1111, Stable.expr_word_356, global_expr_1111.
 rewrite top_port_28_6.
 reflexivity. Qed. Opaque Stable.word_356 global_word_1111.
Transparent Stable.word_357 global_word_1125. Lemma top_word_357 v : Stable.word_357 (top_global_leaves v) = global_word_1125 v.
Proof. unfold Stable.word_357, global_word_1125, Stable.closed_word_357, global_closed_1125, Stable.expr_word_357, global_expr_1125.
 rewrite top_port_29_4.
 reflexivity. Qed. Opaque Stable.word_357 global_word_1125.
Transparent Stable.word_358 global_word_1129. Lemma top_word_358 v : Stable.word_358 (top_global_leaves v) = global_word_1129 v.
Proof. unfold Stable.word_358, global_word_1129, Stable.closed_word_358, global_closed_1129, Stable.expr_word_358, global_expr_1129.
 rewrite top_port_29_5.
 reflexivity. Qed. Opaque Stable.word_358 global_word_1129.
Transparent Stable.word_359 global_word_1143. Lemma top_word_359 v : Stable.word_359 (top_global_leaves v) = global_word_1143 v.
Proof. unfold Stable.word_359, global_word_1143, Stable.closed_word_359, global_closed_1143, Stable.expr_word_359, global_expr_1143.
 rewrite top_port_30_4.
 reflexivity. Qed. Opaque Stable.word_359 global_word_1143.
Transparent Stable.word_360 global_word_1147. Lemma top_word_360 v : Stable.word_360 (top_global_leaves v) = global_word_1147 v.
Proof. unfold Stable.word_360, global_word_1147, Stable.closed_word_360, global_closed_1147, Stable.expr_word_360, global_expr_1147.
 rewrite top_port_30_5.
 reflexivity. Qed. Opaque Stable.word_360 global_word_1147.
Transparent Stable.word_361 global_word_1161. Lemma top_word_361 v : Stable.word_361 (top_global_leaves v) = global_word_1161 v.
Proof. unfold Stable.word_361, global_word_1161, Stable.closed_word_361, global_closed_1161, Stable.expr_word_361, global_expr_1161.
 rewrite top_port_31_4.
 reflexivity. Qed. Opaque Stable.word_361 global_word_1161.
Transparent Stable.word_362 global_word_1165. Lemma top_word_362 v : Stable.word_362 (top_global_leaves v) = global_word_1165 v.
Proof. unfold Stable.word_362, global_word_1165, Stable.closed_word_362, global_closed_1165, Stable.expr_word_362, global_expr_1165.
 rewrite top_port_31_5.
 reflexivity. Qed. Opaque Stable.word_362 global_word_1165.
Transparent Stable.word_363 global_word_1179. Lemma top_word_363 v : Stable.word_363 (top_global_leaves v) = global_word_1179 v.
Proof. unfold Stable.word_363, global_word_1179, Stable.closed_word_363, global_closed_1179, Stable.expr_word_363, global_expr_1179.
 rewrite top_port_32_4.
 reflexivity. Qed. Opaque Stable.word_363 global_word_1179.
Transparent Stable.word_364 global_word_1183. Lemma top_word_364 v : Stable.word_364 (top_global_leaves v) = global_word_1183 v.
Proof. unfold Stable.word_364, global_word_1183, Stable.closed_word_364, global_closed_1183, Stable.expr_word_364, global_expr_1183.
 rewrite top_port_32_5.
 reflexivity. Qed. Opaque Stable.word_364 global_word_1183.
Transparent Stable.word_365 global_word_1203. Lemma top_word_365 v : Stable.word_365 (top_global_leaves v) = global_word_1203 v.
Proof. unfold Stable.word_365, global_word_1203, Stable.closed_word_365, global_closed_1203, Stable.expr_word_365, global_expr_1203.
 rewrite top_port_33_5.
 reflexivity. Qed. Opaque Stable.word_365 global_word_1203.
Transparent Stable.word_366 global_word_1207. Lemma top_word_366 v : Stable.word_366 (top_global_leaves v) = global_word_1207 v.
Proof. unfold Stable.word_366, global_word_1207, Stable.closed_word_366, global_closed_1207, Stable.expr_word_366, global_expr_1207.
 rewrite top_port_33_6.
 reflexivity. Qed. Opaque Stable.word_366 global_word_1207.
Transparent Stable.word_367 global_word_1221. Lemma top_word_367 v : Stable.word_367 (top_global_leaves v) = global_word_1221 v.
Proof. unfold Stable.word_367, global_word_1221, Stable.closed_word_367, global_closed_1221, Stable.expr_word_367, global_expr_1221.
 rewrite top_port_34_4.
 reflexivity. Qed. Opaque Stable.word_367 global_word_1221.
Transparent Stable.word_368 global_word_1225. Lemma top_word_368 v : Stable.word_368 (top_global_leaves v) = global_word_1225 v.
Proof. unfold Stable.word_368, global_word_1225, Stable.closed_word_368, global_closed_1225, Stable.expr_word_368, global_expr_1225.
 rewrite top_port_34_5.
 reflexivity. Qed. Opaque Stable.word_368 global_word_1225.
Transparent Stable.word_369 global_word_1239. Lemma top_word_369 v : Stable.word_369 (top_global_leaves v) = global_word_1239 v.
Proof. unfold Stable.word_369, global_word_1239, Stable.closed_word_369, global_closed_1239, Stable.expr_word_369, global_expr_1239.
 rewrite top_port_35_4.
 reflexivity. Qed. Opaque Stable.word_369 global_word_1239.
Transparent Stable.word_370 global_word_1243. Lemma top_word_370 v : Stable.word_370 (top_global_leaves v) = global_word_1243 v.
Proof. unfold Stable.word_370, global_word_1243, Stable.closed_word_370, global_closed_1243, Stable.expr_word_370, global_expr_1243.
 rewrite top_port_35_5.
 reflexivity. Qed. Opaque Stable.word_370 global_word_1243.
Transparent Stable.word_371 global_word_1257. Lemma top_word_371 v : Stable.word_371 (top_global_leaves v) = global_word_1257 v.
Proof. unfold Stable.word_371, global_word_1257, Stable.closed_word_371, global_closed_1257, Stable.expr_word_371, global_expr_1257.
 rewrite top_port_36_4.
 reflexivity. Qed. Opaque Stable.word_371 global_word_1257.
Transparent Stable.word_372 global_word_1261. Lemma top_word_372 v : Stable.word_372 (top_global_leaves v) = global_word_1261 v.
Proof. unfold Stable.word_372, global_word_1261, Stable.closed_word_372, global_closed_1261, Stable.expr_word_372, global_expr_1261.
 rewrite top_port_36_5.
 reflexivity. Qed. Opaque Stable.word_372 global_word_1261.
Transparent Stable.word_373 global_word_1262. Lemma top_word_373 v : Stable.word_373 (top_global_leaves v) = global_word_1262 v.
Proof. unfold Stable.word_373, global_word_1262, Stable.closed_word_373, global_closed_1262, Stable.expr_word_373, global_expr_1262.
 rewrite top_word_305 top_word_343.
 reflexivity. Qed. Opaque Stable.word_373 global_word_1262.
Transparent Stable.word_374 global_word_1263. Lemma top_word_374 v : Stable.word_374 (top_global_leaves v) = global_word_1263 v.
Proof. unfold Stable.word_374, global_word_1263, Stable.closed_word_374, global_closed_1263, Stable.expr_word_374, global_expr_1263.
 rewrite top_word_345 top_word_347.
 reflexivity. Qed. Opaque Stable.word_374 global_word_1263.
Transparent Stable.word_375 global_word_1264. Lemma top_word_375 v : Stable.word_375 (top_global_leaves v) = global_word_1264 v.
Proof. unfold Stable.word_375, global_word_1264, Stable.closed_word_375, global_closed_1264, Stable.expr_word_375, global_expr_1264.
 rewrite top_word_373 top_word_374.
 reflexivity. Qed. Opaque Stable.word_375 global_word_1264.
Transparent Stable.word_376 global_word_1265. Lemma top_word_376 v : Stable.word_376 (top_global_leaves v) = global_word_1265 v.
Proof. unfold Stable.word_376, global_word_1265, Stable.closed_word_376, global_closed_1265, Stable.expr_word_376, global_expr_1265.
 rewrite top_word_349 top_word_351.
 reflexivity. Qed. Opaque Stable.word_376 global_word_1265.
Transparent Stable.word_377 global_word_1266. Lemma top_word_377 v : Stable.word_377 (top_global_leaves v) = global_word_1266 v.
Proof. unfold Stable.word_377, global_word_1266, Stable.closed_word_377, global_closed_1266, Stable.expr_word_377, global_expr_1266.
 rewrite top_word_353 top_word_355.
 reflexivity. Qed. Opaque Stable.word_377 global_word_1266.
Transparent Stable.word_378 global_word_1267. Lemma top_word_378 v : Stable.word_378 (top_global_leaves v) = global_word_1267 v.
Proof. unfold Stable.word_378, global_word_1267, Stable.closed_word_378, global_closed_1267, Stable.expr_word_378, global_expr_1267.
 rewrite top_word_376 top_word_377.
 reflexivity. Qed. Opaque Stable.word_378 global_word_1267.
Transparent Stable.word_379 global_word_1268. Lemma top_word_379 v : Stable.word_379 (top_global_leaves v) = global_word_1268 v.
Proof. unfold Stable.word_379, global_word_1268, Stable.closed_word_379, global_closed_1268, Stable.expr_word_379, global_expr_1268.
 rewrite top_word_375 top_word_378.
 reflexivity. Qed. Opaque Stable.word_379 global_word_1268.
Transparent Stable.word_380 global_word_1269. Lemma top_word_380 v : Stable.word_380 (top_global_leaves v) = global_word_1269 v.
Proof. unfold Stable.word_380, global_word_1269, Stable.closed_word_380, global_closed_1269, Stable.expr_word_380, global_expr_1269.
 rewrite top_word_357 top_word_359.
 reflexivity. Qed. Opaque Stable.word_380 global_word_1269.
Transparent Stable.word_381 global_word_1270. Lemma top_word_381 v : Stable.word_381 (top_global_leaves v) = global_word_1270 v.
Proof. unfold Stable.word_381, global_word_1270, Stable.closed_word_381, global_closed_1270, Stable.expr_word_381, global_expr_1270.
 rewrite top_word_361 top_word_363.
 reflexivity. Qed. Opaque Stable.word_381 global_word_1270.
Transparent Stable.word_382 global_word_1271. Lemma top_word_382 v : Stable.word_382 (top_global_leaves v) = global_word_1271 v.
Proof. unfold Stable.word_382, global_word_1271, Stable.closed_word_382, global_closed_1271, Stable.expr_word_382, global_expr_1271.
 rewrite top_word_380 top_word_381.
 reflexivity. Qed. Opaque Stable.word_382 global_word_1271.
Transparent Stable.word_383 global_word_1272. Lemma top_word_383 v : Stable.word_383 (top_global_leaves v) = global_word_1272 v.
Proof. unfold Stable.word_383, global_word_1272, Stable.closed_word_383, global_closed_1272, Stable.expr_word_383, global_expr_1272.
 rewrite top_word_365 top_word_367.
 reflexivity. Qed. Opaque Stable.word_383 global_word_1272.
Transparent Stable.word_384 global_word_1273. Lemma top_word_384 v : Stable.word_384 (top_global_leaves v) = global_word_1273 v.
Proof. unfold Stable.word_384, global_word_1273, Stable.closed_word_384, global_closed_1273, Stable.expr_word_384, global_expr_1273.
 rewrite top_word_369 top_word_371.
 reflexivity. Qed. Opaque Stable.word_384 global_word_1273.
Transparent Stable.word_385 global_word_1274. Lemma top_word_385 v : Stable.word_385 (top_global_leaves v) = global_word_1274 v.
Proof. unfold Stable.word_385, global_word_1274, Stable.closed_word_385, global_closed_1274, Stable.expr_word_385, global_expr_1274.
 rewrite top_word_383 top_word_384.
 reflexivity. Qed. Opaque Stable.word_385 global_word_1274.
Transparent Stable.word_386 global_word_1275. Lemma top_word_386 v : Stable.word_386 (top_global_leaves v) = global_word_1275 v.
Proof. unfold Stable.word_386, global_word_1275, Stable.closed_word_386, global_closed_1275, Stable.expr_word_386, global_expr_1275.
 rewrite top_word_382 top_word_385.
 reflexivity. Qed. Opaque Stable.word_386 global_word_1275.
Transparent Stable.word_387 global_word_1276. Lemma top_word_387 v : Stable.word_387 (top_global_leaves v) = global_word_1276 v.
Proof. unfold Stable.word_387, global_word_1276, Stable.closed_word_387, global_closed_1276, Stable.expr_word_387, global_expr_1276.
 rewrite top_word_379 top_word_386.
 reflexivity. Qed. Opaque Stable.word_387 global_word_1276.
Transparent Stable.word_388 global_word_1277. Lemma top_word_388 v : Stable.word_388 (top_global_leaves v) = global_word_1277 v.
Proof. unfold Stable.word_388, global_word_1277, Stable.closed_word_388, global_closed_1277, Stable.expr_word_388, global_expr_1277.
 rewrite top_word_346 top_word_348.
 reflexivity. Qed. Opaque Stable.word_388 global_word_1277.
Transparent Stable.word_389 global_word_1278. Lemma top_word_389 v : Stable.word_389 (top_global_leaves v) = global_word_1278 v.
Proof. unfold Stable.word_389, global_word_1278, Stable.closed_word_389, global_closed_1278, Stable.expr_word_389, global_expr_1278.
 rewrite top_word_344 top_word_388.
 reflexivity. Qed. Opaque Stable.word_389 global_word_1278.
Transparent Stable.word_390 global_word_1279. Lemma top_word_390 v : Stable.word_390 (top_global_leaves v) = global_word_1279 v.
Proof. unfold Stable.word_390, global_word_1279, Stable.closed_word_390, global_closed_1279, Stable.expr_word_390, global_expr_1279.
 rewrite top_word_350 top_word_352.
 reflexivity. Qed. Opaque Stable.word_390 global_word_1279.
Transparent Stable.word_391 global_word_1280. Lemma top_word_391 v : Stable.word_391 (top_global_leaves v) = global_word_1280 v.
Proof. unfold Stable.word_391, global_word_1280, Stable.closed_word_391, global_closed_1280, Stable.expr_word_391, global_expr_1280.
 rewrite top_word_354 top_word_356.
 reflexivity. Qed. Opaque Stable.word_391 global_word_1280.
Transparent Stable.word_392 global_word_1281. Lemma top_word_392 v : Stable.word_392 (top_global_leaves v) = global_word_1281 v.
Proof. unfold Stable.word_392, global_word_1281, Stable.closed_word_392, global_closed_1281, Stable.expr_word_392, global_expr_1281.
 rewrite top_word_390 top_word_391.
 reflexivity. Qed. Opaque Stable.word_392 global_word_1281.
Transparent Stable.word_393 global_word_1282. Lemma top_word_393 v : Stable.word_393 (top_global_leaves v) = global_word_1282 v.
Proof. unfold Stable.word_393, global_word_1282, Stable.closed_word_393, global_closed_1282, Stable.expr_word_393, global_expr_1282.
 rewrite top_word_389 top_word_392.
 reflexivity. Qed. Opaque Stable.word_393 global_word_1282.
Transparent Stable.word_394 global_word_1283. Lemma top_word_394 v : Stable.word_394 (top_global_leaves v) = global_word_1283 v.
Proof. unfold Stable.word_394, global_word_1283, Stable.closed_word_394, global_closed_1283, Stable.expr_word_394, global_expr_1283.
 rewrite top_word_360 top_word_362.
 reflexivity. Qed. Opaque Stable.word_394 global_word_1283.
Transparent Stable.word_395 global_word_1284. Lemma top_word_395 v : Stable.word_395 (top_global_leaves v) = global_word_1284 v.
Proof. unfold Stable.word_395, global_word_1284, Stable.closed_word_395, global_closed_1284, Stable.expr_word_395, global_expr_1284.
 rewrite top_word_358 top_word_394.
 reflexivity. Qed. Opaque Stable.word_395 global_word_1284.
Transparent Stable.word_396 global_word_1285. Lemma top_word_396 v : Stable.word_396 (top_global_leaves v) = global_word_1285 v.
Proof. unfold Stable.word_396, global_word_1285, Stable.closed_word_396, global_closed_1285, Stable.expr_word_396, global_expr_1285.
 rewrite top_word_364 top_word_366.
 reflexivity. Qed. Opaque Stable.word_396 global_word_1285.
Transparent Stable.word_397 global_word_1286. Lemma top_word_397 v : Stable.word_397 (top_global_leaves v) = global_word_1286 v.
Proof. unfold Stable.word_397, global_word_1286, Stable.closed_word_397, global_closed_1286, Stable.expr_word_397, global_expr_1286.
 rewrite top_word_368 top_word_370.
 reflexivity. Qed. Opaque Stable.word_397 global_word_1286.
Transparent Stable.word_398 global_word_1287. Lemma top_word_398 v : Stable.word_398 (top_global_leaves v) = global_word_1287 v.
Proof. unfold Stable.word_398, global_word_1287, Stable.closed_word_398, global_closed_1287, Stable.expr_word_398, global_expr_1287.
 rewrite top_word_396 top_word_397.
 reflexivity. Qed. Opaque Stable.word_398 global_word_1287.
Transparent Stable.word_399 global_word_1288. Lemma top_word_399 v : Stable.word_399 (top_global_leaves v) = global_word_1288 v.
Proof. unfold Stable.word_399, global_word_1288, Stable.closed_word_399, global_closed_1288, Stable.expr_word_399, global_expr_1288.
 rewrite top_word_395 top_word_398.
 reflexivity. Qed. Opaque Stable.word_399 global_word_1288.
Transparent Stable.word_400 global_word_1289. Lemma top_word_400 v : Stable.word_400 (top_global_leaves v) = global_word_1289 v.
Proof. unfold Stable.word_400, global_word_1289, Stable.closed_word_400, global_closed_1289, Stable.expr_word_400, global_expr_1289.
 rewrite top_word_393 top_word_399.
 reflexivity. Qed. Opaque Stable.word_400 global_word_1289.
Transparent Stable.word_401 global_word_1290. Lemma top_word_401 v : Stable.word_401 (top_global_leaves v) = global_word_1290 v.
Proof. unfold Stable.word_401, global_word_1290, Stable.closed_word_401, global_closed_1290, Stable.expr_word_401, global_expr_1290.
 rewrite top_word_400.
 reflexivity. Qed. Opaque Stable.word_401 global_word_1290.
Transparent Stable.word_402 global_word_1291. Lemma top_word_402 v : Stable.word_402 (top_global_leaves v) = global_word_1291 v.
Proof. unfold Stable.word_402, global_word_1291, Stable.closed_word_402, global_closed_1291, Stable.expr_word_402, global_expr_1291.
 rewrite top_word_387 top_word_401.
 reflexivity. Qed. Opaque Stable.word_402 global_word_1291.
Transparent Stable.word_403 global_word_1292. Lemma top_word_403 v : Stable.word_403 (top_global_leaves v) = global_word_1292 v.
Proof. unfold Stable.word_403, global_word_1292, Stable.closed_word_403, global_closed_1292, Stable.expr_word_403, global_expr_1292.
 rewrite top_word_402.
 reflexivity. Qed. Opaque Stable.word_403 global_word_1292.
Transparent Stable.word_404 global_word_1293. Lemma top_word_404 v : Stable.word_404 (top_global_leaves v) = global_word_1293 v.
Proof. unfold Stable.word_404, global_word_1293, Stable.closed_word_404, global_closed_1293, Stable.expr_word_404, global_expr_1293.
 rewrite top_word_2.
 reflexivity. Qed. Opaque Stable.word_404 global_word_1293.
Transparent Stable.word_405 global_word_1294. Lemma top_word_405 v : Stable.word_405 (top_global_leaves v) = global_word_1294 v.
Proof. unfold Stable.word_405, global_word_1294, Stable.closed_word_405, global_closed_1294, Stable.expr_word_405, global_expr_1294.
 rewrite top_word_3.
 reflexivity. Qed. Opaque Stable.word_405 global_word_1294.
Transparent Stable.word_406 global_word_1295. Lemma top_word_406 v : Stable.word_406 (top_global_leaves v) = global_word_1295 v.
Proof. unfold Stable.word_406, global_word_1295, Stable.closed_word_406, global_closed_1295, Stable.expr_word_406, global_expr_1295.
 rewrite top_word_404 top_word_405.
 reflexivity. Qed. Opaque Stable.word_406 global_word_1295.
Transparent Stable.word_407 global_word_1296. Lemma top_word_407 v : Stable.word_407 (top_global_leaves v) = global_word_1296 v.
Proof. unfold Stable.word_407, global_word_1296, Stable.closed_word_407, global_closed_1296, Stable.expr_word_407, global_expr_1296.
 rewrite top_word_406.
 reflexivity. Qed. Opaque Stable.word_407 global_word_1296.
Transparent Stable.word_409 global_word_1297. Lemma top_word_409 v : Stable.word_409 (top_global_leaves v) = global_word_1297 v.
Proof. unfold Stable.word_409, global_word_1297, Stable.closed_word_409, global_closed_1297, Stable.expr_word_409, global_expr_1297.
 rewrite top_word_4 top_word_407 top_word_408.
 reflexivity. Qed. Opaque Stable.word_409 global_word_1297.
Transparent Stable.word_411 global_word_1298. Lemma top_word_411 v : Stable.word_411 (top_global_leaves v) = global_word_1298 v.
Proof. unfold Stable.word_411, global_word_1298, Stable.closed_word_411, global_closed_1298, Stable.expr_word_411, global_expr_1298.
 rewrite top_word_4 top_word_410.
 reflexivity. Qed. Opaque Stable.word_411 global_word_1298.
Transparent Stable.word_6 global_word_1299. Lemma top_word_6 v : Stable.word_6 (top_global_leaves v) = global_word_1299 v.
Proof. unfold Stable.word_6, global_word_1299, Stable.closed_word_6, global_closed_1299, Stable.expr_word_6, global_expr_1299.
 rewrite top_word_403.
 reflexivity. Qed. Opaque Stable.word_6 global_word_1299.
Transparent Stable.word_412 global_word_1300. Lemma top_word_412 v : Stable.word_412 (top_global_leaves v) = global_word_1300 v.
Proof. unfold Stable.word_412, global_word_1300, Stable.closed_word_412, global_closed_1300, Stable.expr_word_412, global_expr_1300.
 rewrite top_word_6 top_word_408.
 reflexivity. Qed. Opaque Stable.word_412 global_word_1300.
Transparent Stable.word_413 global_word_1301. Lemma top_word_413 v : Stable.word_413 (top_global_leaves v) = global_word_1301 v.
Proof. unfold Stable.word_413, global_word_1301, Stable.closed_word_413, global_closed_1301, Stable.expr_word_413, global_expr_1301.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.word_413 global_word_1301.
Transparent Stable.word_414 global_word_1302. Lemma top_word_414 v : Stable.word_414 (top_global_leaves v) = global_word_1302 v.
Proof. unfold Stable.word_414, global_word_1302, Stable.closed_word_414, global_closed_1302, Stable.expr_word_414, global_expr_1302.
 rewrite top_word_413.
 reflexivity. Qed. Opaque Stable.word_414 global_word_1302.
Transparent Stable.word_415 global_word_1303. Lemma top_word_415 v : Stable.word_415 (top_global_leaves v) = global_word_1303 v.
Proof. unfold Stable.word_415, global_word_1303, Stable.closed_word_415, global_closed_1303, Stable.expr_word_415, global_expr_1303.
 rewrite top_word_412.
 reflexivity. Qed. Opaque Stable.word_415 global_word_1303.
Transparent Stable.word_417 global_word_1304. Lemma top_word_417 v : Stable.word_417 (top_global_leaves v) = global_word_1304 v.
Proof. unfold Stable.word_417, global_word_1304, Stable.closed_word_417, global_closed_1304, Stable.expr_word_417, global_expr_1304.
 rewrite top_word_4.
 reflexivity. Qed. Opaque Stable.word_417 global_word_1304.
Transparent Stable.word_418 global_word_1305. Lemma top_word_418 v : Stable.word_418 (top_global_leaves v) = global_word_1305 v.
Proof. unfold Stable.word_418, global_word_1305, Stable.closed_word_418, global_closed_1305, Stable.expr_word_418, global_expr_1305.
 rewrite top_word_410 top_word_417.
 reflexivity. Qed. Opaque Stable.word_418 global_word_1305.
Transparent Stable.word_420 global_word_1306. Lemma top_word_420 v : Stable.word_420 (top_global_leaves v) = global_word_1306 v.
Proof. unfold Stable.word_420, global_word_1306, Stable.closed_word_420, global_closed_1306, Stable.expr_word_420, global_expr_1306.
 rewrite top_word_6 top_word_416.
 reflexivity. Qed. Opaque Stable.word_420 global_word_1306.
Transparent Stable.word_421 global_word_1307. Lemma top_word_421 v : Stable.word_421 (top_global_leaves v) = global_word_1307 v.
Proof. unfold Stable.word_421, global_word_1307, Stable.closed_word_421, global_closed_1307, Stable.expr_word_421, global_expr_1307.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.word_421 global_word_1307.
Transparent Stable.word_422 global_word_1308. Lemma top_word_422 v : Stable.word_422 (top_global_leaves v) = global_word_1308 v.
Proof. unfold Stable.word_422, global_word_1308, Stable.closed_word_422, global_closed_1308, Stable.expr_word_422, global_expr_1308.
 rewrite top_word_421.
 reflexivity. Qed. Opaque Stable.word_422 global_word_1308.
Transparent Stable.word_423 global_word_1309. Lemma top_word_423 v : Stable.word_423 (top_global_leaves v) = global_word_1309 v.
Proof. unfold Stable.word_423, global_word_1309, Stable.closed_word_423, global_closed_1309, Stable.expr_word_423, global_expr_1309.
 rewrite top_word_420.
 reflexivity. Qed. Opaque Stable.word_423 global_word_1309.
Transparent Stable.port_7_0 global_word_1310. Lemma top_port_7_0 v : Stable.port_7_0 (top_global_leaves v) = global_word_1310 v.
Proof. unfold Stable.port_7_0, global_word_1310, Stable.closed_port_7_0, global_closed_1310, Stable.expr_port_7_0, global_expr_1310.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_7_0 global_word_1310.
Transparent Stable.port_7_1 global_word_1311. Lemma top_port_7_1 v : Stable.port_7_1 (top_global_leaves v) = global_word_1311 v.
Proof. unfold Stable.port_7_1, global_word_1311, Stable.closed_port_7_1, global_closed_1311, Stable.expr_port_7_1, global_expr_1311.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_7_1 global_word_1311.
Transparent Stable.port_7_2 global_word_278. Lemma top_port_7_2 v : Stable.port_7_2 (top_global_leaves v) = global_word_278 v.
Proof. unfold Stable.port_7_2, global_word_278, Stable.closed_port_7_2, global_closed_278, Stable.expr_port_7_2, global_expr_278.
 rewrite top_word_201.
 reflexivity. Qed. Opaque Stable.port_7_2 global_word_278.
Transparent Stable.port_7_3 global_word_281. Lemma top_port_7_3 v : Stable.port_7_3 (top_global_leaves v) = global_word_281 v.
Proof. unfold Stable.port_7_3, global_word_281, Stable.closed_port_7_3, global_closed_281, Stable.expr_port_7_3, global_expr_281.
 rewrite top_word_203.
 reflexivity. Qed. Opaque Stable.port_7_3 global_word_281.
Transparent Stable.port_8_0 global_word_1312. Lemma top_port_8_0 v : Stable.port_8_0 (top_global_leaves v) = global_word_1312 v.
Proof. unfold Stable.port_8_0, global_word_1312, Stable.closed_port_8_0, global_closed_1312, Stable.expr_port_8_0, global_expr_1312.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_8_0 global_word_1312.
Transparent Stable.port_8_1 global_word_1313. Lemma top_port_8_1 v : Stable.port_8_1 (top_global_leaves v) = global_word_1313 v.
Proof. unfold Stable.port_8_1, global_word_1313, Stable.closed_port_8_1, global_closed_1313, Stable.expr_port_8_1, global_expr_1313.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_8_1 global_word_1313.
Transparent Stable.port_8_2 global_word_296. Lemma top_port_8_2 v : Stable.port_8_2 (top_global_leaves v) = global_word_296 v.
Proof. unfold Stable.port_8_2, global_word_296, Stable.closed_port_8_2, global_closed_296, Stable.expr_port_8_2, global_expr_296.
 rewrite top_word_205.
 reflexivity. Qed. Opaque Stable.port_8_2 global_word_296.
Transparent Stable.port_8_3 global_word_299. Lemma top_port_8_3 v : Stable.port_8_3 (top_global_leaves v) = global_word_299 v.
Proof. unfold Stable.port_8_3, global_word_299, Stable.closed_port_8_3, global_closed_299, Stable.expr_port_8_3, global_expr_299.
 rewrite top_word_207.
 reflexivity. Qed. Opaque Stable.port_8_3 global_word_299.
Transparent Stable.port_9_0 global_word_1314. Lemma top_port_9_0 v : Stable.port_9_0 (top_global_leaves v) = global_word_1314 v.
Proof. unfold Stable.port_9_0, global_word_1314, Stable.closed_port_9_0, global_closed_1314, Stable.expr_port_9_0, global_expr_1314.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_9_0 global_word_1314.
Transparent Stable.port_9_1 global_word_1315. Lemma top_port_9_1 v : Stable.port_9_1 (top_global_leaves v) = global_word_1315 v.
Proof. unfold Stable.port_9_1, global_word_1315, Stable.closed_port_9_1, global_closed_1315, Stable.expr_port_9_1, global_expr_1315.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_9_1 global_word_1315.
Transparent Stable.port_9_2 global_word_317. Lemma top_port_9_2 v : Stable.port_9_2 (top_global_leaves v) = global_word_317 v.
Proof. unfold Stable.port_9_2, global_word_317, Stable.closed_port_9_2, global_closed_317, Stable.expr_port_9_2, global_expr_317.
 rewrite top_word_209.
 reflexivity. Qed. Opaque Stable.port_9_2 global_word_317.
Transparent Stable.port_9_3 global_word_320. Lemma top_port_9_3 v : Stable.port_9_3 (top_global_leaves v) = global_word_320 v.
Proof. unfold Stable.port_9_3, global_word_320, Stable.closed_port_9_3, global_closed_320, Stable.expr_port_9_3, global_expr_320.
 rewrite top_word_211.
 reflexivity. Qed. Opaque Stable.port_9_3 global_word_320.
Transparent Stable.port_9_4 global_word_314. Lemma top_port_9_4 v : Stable.port_9_4 (top_global_leaves v) = global_word_314 v.
Proof. unfold Stable.port_9_4, global_word_314, Stable.closed_port_9_4, global_closed_314, Stable.expr_port_9_4, global_expr_314.
 rewrite top_word_213.
 reflexivity. Qed. Opaque Stable.port_9_4 global_word_314.
Transparent Stable.port_10_0 global_word_1316. Lemma top_port_10_0 v : Stable.port_10_0 (top_global_leaves v) = global_word_1316 v.
Proof. unfold Stable.port_10_0, global_word_1316, Stable.closed_port_10_0, global_closed_1316, Stable.expr_port_10_0, global_expr_1316.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_10_0 global_word_1316.
Transparent Stable.port_10_1 global_word_1317. Lemma top_port_10_1 v : Stable.port_10_1 (top_global_leaves v) = global_word_1317 v.
Proof. unfold Stable.port_10_1, global_word_1317, Stable.closed_port_10_1, global_closed_1317, Stable.expr_port_10_1, global_expr_1317.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_10_1 global_word_1317.
Transparent Stable.port_10_2 global_word_341. Lemma top_port_10_2 v : Stable.port_10_2 (top_global_leaves v) = global_word_341 v.
Proof. unfold Stable.port_10_2, global_word_341, Stable.closed_port_10_2, global_closed_341, Stable.expr_port_10_2, global_expr_341.
 rewrite top_word_215.
 reflexivity. Qed. Opaque Stable.port_10_2 global_word_341.
Transparent Stable.port_10_3 global_word_344. Lemma top_port_10_3 v : Stable.port_10_3 (top_global_leaves v) = global_word_344 v.
Proof. unfold Stable.port_10_3, global_word_344, Stable.closed_port_10_3, global_closed_344, Stable.expr_port_10_3, global_expr_344.
 rewrite top_word_217.
 reflexivity. Qed. Opaque Stable.port_10_3 global_word_344.
Transparent Stable.port_10_4 global_word_338. Lemma top_port_10_4 v : Stable.port_10_4 (top_global_leaves v) = global_word_338 v.
Proof. unfold Stable.port_10_4, global_word_338, Stable.closed_port_10_4, global_closed_338, Stable.expr_port_10_4, global_expr_338.
 rewrite top_word_219.
 reflexivity. Qed. Opaque Stable.port_10_4 global_word_338.
Transparent Stable.port_11_0 global_word_1318. Lemma top_port_11_0 v : Stable.port_11_0 (top_global_leaves v) = global_word_1318 v.
Proof. unfold Stable.port_11_0, global_word_1318, Stable.closed_port_11_0, global_closed_1318, Stable.expr_port_11_0, global_expr_1318.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_11_0 global_word_1318.
Transparent Stable.port_11_1 global_word_1319. Lemma top_port_11_1 v : Stable.port_11_1 (top_global_leaves v) = global_word_1319 v.
Proof. unfold Stable.port_11_1, global_word_1319, Stable.closed_port_11_1, global_closed_1319, Stable.expr_port_11_1, global_expr_1319.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_11_1 global_word_1319.
Transparent Stable.port_11_2 global_word_373. Lemma top_port_11_2 v : Stable.port_11_2 (top_global_leaves v) = global_word_373 v.
Proof. unfold Stable.port_11_2, global_word_373, Stable.closed_port_11_2, global_closed_373, Stable.expr_port_11_2, global_expr_373.
 rewrite top_word_221.
 reflexivity. Qed. Opaque Stable.port_11_2 global_word_373.
Transparent Stable.port_11_3 global_word_378. Lemma top_port_11_3 v : Stable.port_11_3 (top_global_leaves v) = global_word_378 v.
Proof. unfold Stable.port_11_3, global_word_378, Stable.closed_port_11_3, global_closed_378, Stable.expr_port_11_3, global_expr_378.
 rewrite top_word_223.
 reflexivity. Qed. Opaque Stable.port_11_3 global_word_378.
Transparent Stable.port_11_4 global_word_368. Lemma top_port_11_4 v : Stable.port_11_4 (top_global_leaves v) = global_word_368 v.
Proof. unfold Stable.port_11_4, global_word_368, Stable.closed_port_11_4, global_closed_368, Stable.expr_port_11_4, global_expr_368.
 rewrite top_word_225.
 reflexivity. Qed. Opaque Stable.port_11_4 global_word_368.
Transparent Stable.port_11_5 global_word_397. Lemma top_port_11_5 v : Stable.port_11_5 (top_global_leaves v) = global_word_397 v.
Proof. unfold Stable.port_11_5, global_word_397, Stable.closed_port_11_5, global_closed_397, Stable.expr_port_11_5, global_expr_397.
 rewrite top_word_227.
 reflexivity. Qed. Opaque Stable.port_11_5 global_word_397.
Transparent Stable.port_11_6 global_word_362. Lemma top_port_11_6 v : Stable.port_11_6 (top_global_leaves v) = global_word_362 v.
Proof. unfold Stable.port_11_6, global_word_362, Stable.closed_port_11_6, global_closed_362, Stable.expr_port_11_6, global_expr_362.
 reflexivity. Qed. Opaque Stable.port_11_6 global_word_362.
Transparent Stable.port_12_0 global_word_1320. Lemma top_port_12_0 v : Stable.port_12_0 (top_global_leaves v) = global_word_1320 v.
Proof. unfold Stable.port_12_0, global_word_1320, Stable.closed_port_12_0, global_closed_1320, Stable.expr_port_12_0, global_expr_1320.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_12_0 global_word_1320.
Transparent Stable.port_12_1 global_word_1321. Lemma top_port_12_1 v : Stable.port_12_1 (top_global_leaves v) = global_word_1321 v.
Proof. unfold Stable.port_12_1, global_word_1321, Stable.closed_port_12_1, global_closed_1321, Stable.expr_port_12_1, global_expr_1321.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_12_1 global_word_1321.
Transparent Stable.port_12_2 global_word_442. Lemma top_port_12_2 v : Stable.port_12_2 (top_global_leaves v) = global_word_442 v.
Proof. unfold Stable.port_12_2, global_word_442, Stable.closed_port_12_2, global_closed_442, Stable.expr_port_12_2, global_expr_442.
 rewrite top_word_229.
 reflexivity. Qed. Opaque Stable.port_12_2 global_word_442.
Transparent Stable.port_12_3 global_word_447. Lemma top_port_12_3 v : Stable.port_12_3 (top_global_leaves v) = global_word_447 v.
Proof. unfold Stable.port_12_3, global_word_447, Stable.closed_port_12_3, global_closed_447, Stable.expr_port_12_3, global_expr_447.
 rewrite top_word_231.
 reflexivity. Qed. Opaque Stable.port_12_3 global_word_447.
Transparent Stable.port_12_4 global_word_437. Lemma top_port_12_4 v : Stable.port_12_4 (top_global_leaves v) = global_word_437 v.
Proof. unfold Stable.port_12_4, global_word_437, Stable.closed_port_12_4, global_closed_437, Stable.expr_port_12_4, global_expr_437.
 rewrite top_word_233.
 reflexivity. Qed. Opaque Stable.port_12_4 global_word_437.
Transparent Stable.port_12_5 global_word_466. Lemma top_port_12_5 v : Stable.port_12_5 (top_global_leaves v) = global_word_466 v.
Proof. unfold Stable.port_12_5, global_word_466, Stable.closed_port_12_5, global_closed_466, Stable.expr_port_12_5, global_expr_466.
 rewrite top_word_235.
 reflexivity. Qed. Opaque Stable.port_12_5 global_word_466.
Transparent Stable.port_12_6 global_word_431. Lemma top_port_12_6 v : Stable.port_12_6 (top_global_leaves v) = global_word_431 v.
Proof. unfold Stable.port_12_6, global_word_431, Stable.closed_port_12_6, global_closed_431, Stable.expr_port_12_6, global_expr_431.
 rewrite top_word_314.
 reflexivity. Qed. Opaque Stable.port_12_6 global_word_431.
Transparent Stable.port_13_0 global_word_1322. Lemma top_port_13_0 v : Stable.port_13_0 (top_global_leaves v) = global_word_1322 v.
Proof. unfold Stable.port_13_0, global_word_1322, Stable.closed_port_13_0, global_closed_1322, Stable.expr_port_13_0, global_expr_1322.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_13_0 global_word_1322.
Transparent Stable.port_13_1 global_word_1323. Lemma top_port_13_1 v : Stable.port_13_1 (top_global_leaves v) = global_word_1323 v.
Proof. unfold Stable.port_13_1, global_word_1323, Stable.closed_port_13_1, global_closed_1323, Stable.expr_port_13_1, global_expr_1323.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_13_1 global_word_1323.
Transparent Stable.port_13_2 global_word_511. Lemma top_port_13_2 v : Stable.port_13_2 (top_global_leaves v) = global_word_511 v.
Proof. unfold Stable.port_13_2, global_word_511, Stable.closed_port_13_2, global_closed_511, Stable.expr_port_13_2, global_expr_511.
 rewrite top_word_237.
 reflexivity. Qed. Opaque Stable.port_13_2 global_word_511.
Transparent Stable.port_13_3 global_word_516. Lemma top_port_13_3 v : Stable.port_13_3 (top_global_leaves v) = global_word_516 v.
Proof. unfold Stable.port_13_3, global_word_516, Stable.closed_port_13_3, global_closed_516, Stable.expr_port_13_3, global_expr_516.
 rewrite top_word_239.
 reflexivity. Qed. Opaque Stable.port_13_3 global_word_516.
Transparent Stable.port_13_4 global_word_506. Lemma top_port_13_4 v : Stable.port_13_4 (top_global_leaves v) = global_word_506 v.
Proof. unfold Stable.port_13_4, global_word_506, Stable.closed_port_13_4, global_closed_506, Stable.expr_port_13_4, global_expr_506.
 rewrite top_word_241.
 reflexivity. Qed. Opaque Stable.port_13_4 global_word_506.
Transparent Stable.port_13_5 global_word_535. Lemma top_port_13_5 v : Stable.port_13_5 (top_global_leaves v) = global_word_535 v.
Proof. unfold Stable.port_13_5, global_word_535, Stable.closed_port_13_5, global_closed_535, Stable.expr_port_13_5, global_expr_535.
 rewrite top_word_243.
 reflexivity. Qed. Opaque Stable.port_13_5 global_word_535.
Transparent Stable.port_13_6 global_word_500. Lemma top_port_13_6 v : Stable.port_13_6 (top_global_leaves v) = global_word_500 v.
Proof. unfold Stable.port_13_6, global_word_500, Stable.closed_port_13_6, global_closed_500, Stable.expr_port_13_6, global_expr_500.
 rewrite top_word_317.
 reflexivity. Qed. Opaque Stable.port_13_6 global_word_500.
Transparent Stable.port_14_0 global_word_1324. Lemma top_port_14_0 v : Stable.port_14_0 (top_global_leaves v) = global_word_1324 v.
Proof. unfold Stable.port_14_0, global_word_1324, Stable.closed_port_14_0, global_closed_1324, Stable.expr_port_14_0, global_expr_1324.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_14_0 global_word_1324.
Transparent Stable.port_14_1 global_word_1325. Lemma top_port_14_1 v : Stable.port_14_1 (top_global_leaves v) = global_word_1325 v.
Proof. unfold Stable.port_14_1, global_word_1325, Stable.closed_port_14_1, global_closed_1325, Stable.expr_port_14_1, global_expr_1325.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_14_1 global_word_1325.
Transparent Stable.port_14_2 global_word_580. Lemma top_port_14_2 v : Stable.port_14_2 (top_global_leaves v) = global_word_580 v.
Proof. unfold Stable.port_14_2, global_word_580, Stable.closed_port_14_2, global_closed_580, Stable.expr_port_14_2, global_expr_580.
 rewrite top_word_247.
 reflexivity. Qed. Opaque Stable.port_14_2 global_word_580.
Transparent Stable.port_14_3 global_word_585. Lemma top_port_14_3 v : Stable.port_14_3 (top_global_leaves v) = global_word_585 v.
Proof. unfold Stable.port_14_3, global_word_585, Stable.closed_port_14_3, global_closed_585, Stable.expr_port_14_3, global_expr_585.
 rewrite top_word_249.
 reflexivity. Qed. Opaque Stable.port_14_3 global_word_585.
Transparent Stable.port_14_4 global_word_575. Lemma top_port_14_4 v : Stable.port_14_4 (top_global_leaves v) = global_word_575 v.
Proof. unfold Stable.port_14_4, global_word_575, Stable.closed_port_14_4, global_closed_575, Stable.expr_port_14_4, global_expr_575.
 rewrite top_word_251.
 reflexivity. Qed. Opaque Stable.port_14_4 global_word_575.
Transparent Stable.port_14_5 global_word_604. Lemma top_port_14_5 v : Stable.port_14_5 (top_global_leaves v) = global_word_604 v.
Proof. unfold Stable.port_14_5, global_word_604, Stable.closed_port_14_5, global_closed_604, Stable.expr_port_14_5, global_expr_604.
 rewrite top_word_253.
 reflexivity. Qed. Opaque Stable.port_14_5 global_word_604.
Transparent Stable.port_14_6 global_word_569. Lemma top_port_14_6 v : Stable.port_14_6 (top_global_leaves v) = global_word_569 v.
Proof. unfold Stable.port_14_6, global_word_569, Stable.closed_port_14_6, global_closed_569, Stable.expr_port_14_6, global_expr_569.
 rewrite top_word_320.
 reflexivity. Qed. Opaque Stable.port_14_6 global_word_569.
Transparent Stable.port_15_0 global_word_1326. Lemma top_port_15_0 v : Stable.port_15_0 (top_global_leaves v) = global_word_1326 v.
Proof. unfold Stable.port_15_0, global_word_1326, Stable.closed_port_15_0, global_closed_1326, Stable.expr_port_15_0, global_expr_1326.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_15_0 global_word_1326.
Transparent Stable.port_15_1 global_word_1327. Lemma top_port_15_1 v : Stable.port_15_1 (top_global_leaves v) = global_word_1327 v.
Proof. unfold Stable.port_15_1, global_word_1327, Stable.closed_port_15_1, global_closed_1327, Stable.expr_port_15_1, global_expr_1327.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_15_1 global_word_1327.
Transparent Stable.port_15_2 global_word_649. Lemma top_port_15_2 v : Stable.port_15_2 (top_global_leaves v) = global_word_649 v.
Proof. unfold Stable.port_15_2, global_word_649, Stable.closed_port_15_2, global_closed_649, Stable.expr_port_15_2, global_expr_649.
 rewrite top_word_257.
 reflexivity. Qed. Opaque Stable.port_15_2 global_word_649.
Transparent Stable.port_15_3 global_word_654. Lemma top_port_15_3 v : Stable.port_15_3 (top_global_leaves v) = global_word_654 v.
Proof. unfold Stable.port_15_3, global_word_654, Stable.closed_port_15_3, global_closed_654, Stable.expr_port_15_3, global_expr_654.
 rewrite top_word_259.
 reflexivity. Qed. Opaque Stable.port_15_3 global_word_654.
Transparent Stable.port_15_4 global_word_644. Lemma top_port_15_4 v : Stable.port_15_4 (top_global_leaves v) = global_word_644 v.
Proof. unfold Stable.port_15_4, global_word_644, Stable.closed_port_15_4, global_closed_644, Stable.expr_port_15_4, global_expr_644.
 rewrite top_word_261.
 reflexivity. Qed. Opaque Stable.port_15_4 global_word_644.
Transparent Stable.port_15_5 global_word_673. Lemma top_port_15_5 v : Stable.port_15_5 (top_global_leaves v) = global_word_673 v.
Proof. unfold Stable.port_15_5, global_word_673, Stable.closed_port_15_5, global_closed_673, Stable.expr_port_15_5, global_expr_673.
 rewrite top_word_263.
 reflexivity. Qed. Opaque Stable.port_15_5 global_word_673.
Transparent Stable.port_15_6 global_word_638. Lemma top_port_15_6 v : Stable.port_15_6 (top_global_leaves v) = global_word_638 v.
Proof. unfold Stable.port_15_6, global_word_638, Stable.closed_port_15_6, global_closed_638, Stable.expr_port_15_6, global_expr_638.
 rewrite top_word_323.
 reflexivity. Qed. Opaque Stable.port_15_6 global_word_638.
Transparent Stable.port_16_0 global_word_1328. Lemma top_port_16_0 v : Stable.port_16_0 (top_global_leaves v) = global_word_1328 v.
Proof. unfold Stable.port_16_0, global_word_1328, Stable.closed_port_16_0, global_closed_1328, Stable.expr_port_16_0, global_expr_1328.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_16_0 global_word_1328.
Transparent Stable.port_16_1 global_word_1329. Lemma top_port_16_1 v : Stable.port_16_1 (top_global_leaves v) = global_word_1329 v.
Proof. unfold Stable.port_16_1, global_word_1329, Stable.closed_port_16_1, global_closed_1329, Stable.expr_port_16_1, global_expr_1329.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_16_1 global_word_1329.
Transparent Stable.port_16_2 global_word_718. Lemma top_port_16_2 v : Stable.port_16_2 (top_global_leaves v) = global_word_718 v.
Proof. unfold Stable.port_16_2, global_word_718, Stable.closed_port_16_2, global_closed_718, Stable.expr_port_16_2, global_expr_718.
 rewrite top_word_265.
 reflexivity. Qed. Opaque Stable.port_16_2 global_word_718.
Transparent Stable.port_16_3 global_word_723. Lemma top_port_16_3 v : Stable.port_16_3 (top_global_leaves v) = global_word_723 v.
Proof. unfold Stable.port_16_3, global_word_723, Stable.closed_port_16_3, global_closed_723, Stable.expr_port_16_3, global_expr_723.
 rewrite top_word_267.
 reflexivity. Qed. Opaque Stable.port_16_3 global_word_723.
Transparent Stable.port_16_4 global_word_713. Lemma top_port_16_4 v : Stable.port_16_4 (top_global_leaves v) = global_word_713 v.
Proof. unfold Stable.port_16_4, global_word_713, Stable.closed_port_16_4, global_closed_713, Stable.expr_port_16_4, global_expr_713.
 rewrite top_word_269.
 reflexivity. Qed. Opaque Stable.port_16_4 global_word_713.
Transparent Stable.port_16_5 global_word_742. Lemma top_port_16_5 v : Stable.port_16_5 (top_global_leaves v) = global_word_742 v.
Proof. unfold Stable.port_16_5, global_word_742, Stable.closed_port_16_5, global_closed_742, Stable.expr_port_16_5, global_expr_742.
 rewrite top_word_271.
 reflexivity. Qed. Opaque Stable.port_16_5 global_word_742.
Transparent Stable.port_16_6 global_word_707. Lemma top_port_16_6 v : Stable.port_16_6 (top_global_leaves v) = global_word_707 v.
Proof. unfold Stable.port_16_6, global_word_707, Stable.closed_port_16_6, global_closed_707, Stable.expr_port_16_6, global_expr_707.
 rewrite top_word_326.
 reflexivity. Qed. Opaque Stable.port_16_6 global_word_707.
Transparent Stable.port_17_0 global_word_1330. Lemma top_port_17_0 v : Stable.port_17_0 (top_global_leaves v) = global_word_1330 v.
Proof. unfold Stable.port_17_0, global_word_1330, Stable.closed_port_17_0, global_closed_1330, Stable.expr_port_17_0, global_expr_1330.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_17_0 global_word_1330.
Transparent Stable.port_17_1 global_word_1331. Lemma top_port_17_1 v : Stable.port_17_1 (top_global_leaves v) = global_word_1331 v.
Proof. unfold Stable.port_17_1, global_word_1331, Stable.closed_port_17_1, global_closed_1331, Stable.expr_port_17_1, global_expr_1331.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_17_1 global_word_1331.
Transparent Stable.port_17_2 global_word_787. Lemma top_port_17_2 v : Stable.port_17_2 (top_global_leaves v) = global_word_787 v.
Proof. unfold Stable.port_17_2, global_word_787, Stable.closed_port_17_2, global_closed_787, Stable.expr_port_17_2, global_expr_787.
 rewrite top_word_273.
 reflexivity. Qed. Opaque Stable.port_17_2 global_word_787.
Transparent Stable.port_17_3 global_word_792. Lemma top_port_17_3 v : Stable.port_17_3 (top_global_leaves v) = global_word_792 v.
Proof. unfold Stable.port_17_3, global_word_792, Stable.closed_port_17_3, global_closed_792, Stable.expr_port_17_3, global_expr_792.
 rewrite top_word_275.
 reflexivity. Qed. Opaque Stable.port_17_3 global_word_792.
Transparent Stable.port_17_4 global_word_782. Lemma top_port_17_4 v : Stable.port_17_4 (top_global_leaves v) = global_word_782 v.
Proof. unfold Stable.port_17_4, global_word_782, Stable.closed_port_17_4, global_closed_782, Stable.expr_port_17_4, global_expr_782.
 rewrite top_word_277.
 reflexivity. Qed. Opaque Stable.port_17_4 global_word_782.
Transparent Stable.port_17_5 global_word_811. Lemma top_port_17_5 v : Stable.port_17_5 (top_global_leaves v) = global_word_811 v.
Proof. unfold Stable.port_17_5, global_word_811, Stable.closed_port_17_5, global_closed_811, Stable.expr_port_17_5, global_expr_811.
 rewrite top_word_279.
 reflexivity. Qed. Opaque Stable.port_17_5 global_word_811.
Transparent Stable.port_17_6 global_word_776. Lemma top_port_17_6 v : Stable.port_17_6 (top_global_leaves v) = global_word_776 v.
Proof. unfold Stable.port_17_6, global_word_776, Stable.closed_port_17_6, global_closed_776, Stable.expr_port_17_6, global_expr_776.
 rewrite top_word_329.
 reflexivity. Qed. Opaque Stable.port_17_6 global_word_776.
Transparent Stable.port_18_0 global_word_1332. Lemma top_port_18_0 v : Stable.port_18_0 (top_global_leaves v) = global_word_1332 v.
Proof. unfold Stable.port_18_0, global_word_1332, Stable.closed_port_18_0, global_closed_1332, Stable.expr_port_18_0, global_expr_1332.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_18_0 global_word_1332.
Transparent Stable.port_18_1 global_word_1333. Lemma top_port_18_1 v : Stable.port_18_1 (top_global_leaves v) = global_word_1333 v.
Proof. unfold Stable.port_18_1, global_word_1333, Stable.closed_port_18_1, global_closed_1333, Stable.expr_port_18_1, global_expr_1333.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_18_1 global_word_1333.
Transparent Stable.port_18_2 global_word_856. Lemma top_port_18_2 v : Stable.port_18_2 (top_global_leaves v) = global_word_856 v.
Proof. unfold Stable.port_18_2, global_word_856, Stable.closed_port_18_2, global_closed_856, Stable.expr_port_18_2, global_expr_856.
 rewrite top_word_281.
 reflexivity. Qed. Opaque Stable.port_18_2 global_word_856.
Transparent Stable.port_18_3 global_word_861. Lemma top_port_18_3 v : Stable.port_18_3 (top_global_leaves v) = global_word_861 v.
Proof. unfold Stable.port_18_3, global_word_861, Stable.closed_port_18_3, global_closed_861, Stable.expr_port_18_3, global_expr_861.
 rewrite top_word_283.
 reflexivity. Qed. Opaque Stable.port_18_3 global_word_861.
Transparent Stable.port_18_4 global_word_851. Lemma top_port_18_4 v : Stable.port_18_4 (top_global_leaves v) = global_word_851 v.
Proof. unfold Stable.port_18_4, global_word_851, Stable.closed_port_18_4, global_closed_851, Stable.expr_port_18_4, global_expr_851.
 rewrite top_word_285.
 reflexivity. Qed. Opaque Stable.port_18_4 global_word_851.
Transparent Stable.port_18_5 global_word_880. Lemma top_port_18_5 v : Stable.port_18_5 (top_global_leaves v) = global_word_880 v.
Proof. unfold Stable.port_18_5, global_word_880, Stable.closed_port_18_5, global_closed_880, Stable.expr_port_18_5, global_expr_880.
 rewrite top_word_287.
 reflexivity. Qed. Opaque Stable.port_18_5 global_word_880.
Transparent Stable.port_18_6 global_word_845. Lemma top_port_18_6 v : Stable.port_18_6 (top_global_leaves v) = global_word_845 v.
Proof. unfold Stable.port_18_6, global_word_845, Stable.closed_port_18_6, global_closed_845, Stable.expr_port_18_6, global_expr_845.
 rewrite top_word_332.
 reflexivity. Qed. Opaque Stable.port_18_6 global_word_845.
Transparent Stable.port_19_0 global_word_1334. Lemma top_port_19_0 v : Stable.port_19_0 (top_global_leaves v) = global_word_1334 v.
Proof. unfold Stable.port_19_0, global_word_1334, Stable.closed_port_19_0, global_closed_1334, Stable.expr_port_19_0, global_expr_1334.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_19_0 global_word_1334.
Transparent Stable.port_19_1 global_word_1335. Lemma top_port_19_1 v : Stable.port_19_1 (top_global_leaves v) = global_word_1335 v.
Proof. unfold Stable.port_19_1, global_word_1335, Stable.closed_port_19_1, global_closed_1335, Stable.expr_port_19_1, global_expr_1335.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_19_1 global_word_1335.
Transparent Stable.port_19_2 global_word_917. Lemma top_port_19_2 v : Stable.port_19_2 (top_global_leaves v) = global_word_917 v.
Proof. unfold Stable.port_19_2, global_word_917, Stable.closed_port_19_2, global_closed_917, Stable.expr_port_19_2, global_expr_917.
 rewrite top_word_289.
 reflexivity. Qed. Opaque Stable.port_19_2 global_word_917.
Transparent Stable.port_19_3 global_word_920. Lemma top_port_19_3 v : Stable.port_19_3 (top_global_leaves v) = global_word_920 v.
Proof. unfold Stable.port_19_3, global_word_920, Stable.closed_port_19_3, global_closed_920, Stable.expr_port_19_3, global_expr_920.
 rewrite top_word_291.
 reflexivity. Qed. Opaque Stable.port_19_3 global_word_920.
Transparent Stable.port_19_4 global_word_914. Lemma top_port_19_4 v : Stable.port_19_4 (top_global_leaves v) = global_word_914 v.
Proof. unfold Stable.port_19_4, global_word_914, Stable.closed_port_19_4, global_closed_914, Stable.expr_port_19_4, global_expr_914.
 rewrite top_word_293.
 reflexivity. Qed. Opaque Stable.port_19_4 global_word_914.
Transparent Stable.port_20_0 global_word_1336. Lemma top_port_20_0 v : Stable.port_20_0 (top_global_leaves v) = global_word_1336 v.
Proof. unfold Stable.port_20_0, global_word_1336, Stable.closed_port_20_0, global_closed_1336, Stable.expr_port_20_0, global_expr_1336.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_20_0 global_word_1336.
Transparent Stable.port_20_1 global_word_1337. Lemma top_port_20_1 v : Stable.port_20_1 (top_global_leaves v) = global_word_1337 v.
Proof. unfold Stable.port_20_1, global_word_1337, Stable.closed_port_20_1, global_closed_1337, Stable.expr_port_20_1, global_expr_1337.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_20_1 global_word_1337.
Transparent Stable.port_20_2 global_word_938. Lemma top_port_20_2 v : Stable.port_20_2 (top_global_leaves v) = global_word_938 v.
Proof. unfold Stable.port_20_2, global_word_938, Stable.closed_port_20_2, global_closed_938, Stable.expr_port_20_2, global_expr_938.
 rewrite top_word_295.
 reflexivity. Qed. Opaque Stable.port_20_2 global_word_938.
Transparent Stable.port_20_3 global_word_941. Lemma top_port_20_3 v : Stable.port_20_3 (top_global_leaves v) = global_word_941 v.
Proof. unfold Stable.port_20_3, global_word_941, Stable.closed_port_20_3, global_closed_941, Stable.expr_port_20_3, global_expr_941.
 rewrite top_word_297.
 reflexivity. Qed. Opaque Stable.port_20_3 global_word_941.
Transparent Stable.port_21_0 global_word_1338. Lemma top_port_21_0 v : Stable.port_21_0 (top_global_leaves v) = global_word_1338 v.
Proof. unfold Stable.port_21_0, global_word_1338, Stable.closed_port_21_0, global_closed_1338, Stable.expr_port_21_0, global_expr_1338.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_21_0 global_word_1338.
Transparent Stable.port_21_1 global_word_1339. Lemma top_port_21_1 v : Stable.port_21_1 (top_global_leaves v) = global_word_1339 v.
Proof. unfold Stable.port_21_1, global_word_1339, Stable.closed_port_21_1, global_closed_1339, Stable.expr_port_21_1, global_expr_1339.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_21_1 global_word_1339.
Transparent Stable.port_21_2 global_word_956. Lemma top_port_21_2 v : Stable.port_21_2 (top_global_leaves v) = global_word_956 v.
Proof. unfold Stable.port_21_2, global_word_956, Stable.closed_port_21_2, global_closed_956, Stable.expr_port_21_2, global_expr_956.
 rewrite top_word_299.
 reflexivity. Qed. Opaque Stable.port_21_2 global_word_956.
Transparent Stable.port_21_3 global_word_959. Lemma top_port_21_3 v : Stable.port_21_3 (top_global_leaves v) = global_word_959 v.
Proof. unfold Stable.port_21_3, global_word_959, Stable.closed_port_21_3, global_closed_959, Stable.expr_port_21_3, global_expr_959.
 rewrite top_word_301.
 reflexivity. Qed. Opaque Stable.port_21_3 global_word_959.
Transparent Stable.port_22_0 global_word_1340. Lemma top_port_22_0 v : Stable.port_22_0 (top_global_leaves v) = global_word_1340 v.
Proof. unfold Stable.port_22_0, global_word_1340, Stable.closed_port_22_0, global_closed_1340, Stable.expr_port_22_0, global_expr_1340.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_22_0 global_word_1340.
Transparent Stable.port_22_1 global_word_1341. Lemma top_port_22_1 v : Stable.port_22_1 (top_global_leaves v) = global_word_1341 v.
Proof. unfold Stable.port_22_1, global_word_1341, Stable.closed_port_22_1, global_closed_1341, Stable.expr_port_22_1, global_expr_1341.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_22_1 global_word_1341.
Transparent Stable.port_22_2 global_word_974. Lemma top_port_22_2 v : Stable.port_22_2 (top_global_leaves v) = global_word_974 v.
Proof. unfold Stable.port_22_2, global_word_974, Stable.closed_port_22_2, global_closed_974, Stable.expr_port_22_2, global_expr_974.
 rewrite top_word_307.
 reflexivity. Qed. Opaque Stable.port_22_2 global_word_974.
Transparent Stable.port_22_3 global_word_977. Lemma top_port_22_3 v : Stable.port_22_3 (top_global_leaves v) = global_word_977 v.
Proof. unfold Stable.port_22_3, global_word_977, Stable.closed_port_22_3, global_closed_977, Stable.expr_port_22_3, global_expr_977.
 rewrite top_word_306.
 reflexivity. Qed. Opaque Stable.port_22_3 global_word_977.
Transparent Stable.port_23_0 global_word_1342. Lemma top_port_23_0 v : Stable.port_23_0 (top_global_leaves v) = global_word_1342 v.
Proof. unfold Stable.port_23_0, global_word_1342, Stable.closed_port_23_0, global_closed_1342, Stable.expr_port_23_0, global_expr_1342.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_23_0 global_word_1342.
Transparent Stable.port_23_1 global_word_1343. Lemma top_port_23_1 v : Stable.port_23_1 (top_global_leaves v) = global_word_1343 v.
Proof. unfold Stable.port_23_1, global_word_1343, Stable.closed_port_23_1, global_closed_1343, Stable.expr_port_23_1, global_expr_1343.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_23_1 global_word_1343.
Transparent Stable.port_23_2 global_word_992. Lemma top_port_23_2 v : Stable.port_23_2 (top_global_leaves v) = global_word_992 v.
Proof. unfold Stable.port_23_2, global_word_992, Stable.closed_port_23_2, global_closed_992, Stable.expr_port_23_2, global_expr_992.
 rewrite top_word_309.
 reflexivity. Qed. Opaque Stable.port_23_2 global_word_992.
Transparent Stable.port_23_3 global_word_995. Lemma top_port_23_3 v : Stable.port_23_3 (top_global_leaves v) = global_word_995 v.
Proof. unfold Stable.port_23_3, global_word_995, Stable.closed_port_23_3, global_closed_995, Stable.expr_port_23_3, global_expr_995.
 rewrite top_word_308.
 reflexivity. Qed. Opaque Stable.port_23_3 global_word_995.
Transparent Stable.port_24_0 global_word_1344. Lemma top_port_24_0 v : Stable.port_24_0 (top_global_leaves v) = global_word_1344 v.
Proof. unfold Stable.port_24_0, global_word_1344, Stable.closed_port_24_0, global_closed_1344, Stable.expr_port_24_0, global_expr_1344.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_24_0 global_word_1344.
Transparent Stable.port_24_1 global_word_1345. Lemma top_port_24_1 v : Stable.port_24_1 (top_global_leaves v) = global_word_1345 v.
Proof. unfold Stable.port_24_1, global_word_1345, Stable.closed_port_24_1, global_closed_1345, Stable.expr_port_24_1, global_expr_1345.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_24_1 global_word_1345.
Transparent Stable.port_24_2 global_word_1010. Lemma top_port_24_2 v : Stable.port_24_2 (top_global_leaves v) = global_word_1010 v.
Proof. unfold Stable.port_24_2, global_word_1010, Stable.closed_port_24_2, global_closed_1010, Stable.expr_port_24_2, global_expr_1010.
 rewrite top_word_311.
 reflexivity. Qed. Opaque Stable.port_24_2 global_word_1010.
Transparent Stable.port_24_3 global_word_1013. Lemma top_port_24_3 v : Stable.port_24_3 (top_global_leaves v) = global_word_1013 v.
Proof. unfold Stable.port_24_3, global_word_1013, Stable.closed_port_24_3, global_closed_1013, Stable.expr_port_24_3, global_expr_1013.
 rewrite top_word_310.
 reflexivity. Qed. Opaque Stable.port_24_3 global_word_1013.
Transparent Stable.port_25_0 global_word_1346. Lemma top_port_25_0 v : Stable.port_25_0 (top_global_leaves v) = global_word_1346 v.
Proof. unfold Stable.port_25_0, global_word_1346, Stable.closed_port_25_0, global_closed_1346, Stable.expr_port_25_0, global_expr_1346.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_25_0 global_word_1346.
Transparent Stable.port_25_1 global_word_1347. Lemma top_port_25_1 v : Stable.port_25_1 (top_global_leaves v) = global_word_1347 v.
Proof. unfold Stable.port_25_1, global_word_1347, Stable.closed_port_25_1, global_closed_1347, Stable.expr_port_25_1, global_expr_1347.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_25_1 global_word_1347.
Transparent Stable.port_25_2 global_word_1028. Lemma top_port_25_2 v : Stable.port_25_2 (top_global_leaves v) = global_word_1028 v.
Proof. unfold Stable.port_25_2, global_word_1028, Stable.closed_port_25_2, global_closed_1028, Stable.expr_port_25_2, global_expr_1028.
 rewrite top_word_313.
 reflexivity. Qed. Opaque Stable.port_25_2 global_word_1028.
Transparent Stable.port_25_3 global_word_1031. Lemma top_port_25_3 v : Stable.port_25_3 (top_global_leaves v) = global_word_1031 v.
Proof. unfold Stable.port_25_3, global_word_1031, Stable.closed_port_25_3, global_closed_1031, Stable.expr_port_25_3, global_expr_1031.
 rewrite top_word_312.
 reflexivity. Qed. Opaque Stable.port_25_3 global_word_1031.
Transparent Stable.port_26_0 global_word_1348. Lemma top_port_26_0 v : Stable.port_26_0 (top_global_leaves v) = global_word_1348 v.
Proof. unfold Stable.port_26_0, global_word_1348, Stable.closed_port_26_0, global_closed_1348, Stable.expr_port_26_0, global_expr_1348.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_26_0 global_word_1348.
Transparent Stable.port_26_1 global_word_1349. Lemma top_port_26_1 v : Stable.port_26_1 (top_global_leaves v) = global_word_1349 v.
Proof. unfold Stable.port_26_1, global_word_1349, Stable.closed_port_26_1, global_closed_1349, Stable.expr_port_26_1, global_expr_1349.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_26_1 global_word_1349.
Transparent Stable.port_26_2 global_word_1046. Lemma top_port_26_2 v : Stable.port_26_2 (top_global_leaves v) = global_word_1046 v.
Proof. unfold Stable.port_26_2, global_word_1046, Stable.closed_port_26_2, global_closed_1046, Stable.expr_port_26_2, global_expr_1046.
 rewrite top_word_316.
 reflexivity. Qed. Opaque Stable.port_26_2 global_word_1046.
Transparent Stable.port_26_3 global_word_1049. Lemma top_port_26_3 v : Stable.port_26_3 (top_global_leaves v) = global_word_1049 v.
Proof. unfold Stable.port_26_3, global_word_1049, Stable.closed_port_26_3, global_closed_1049, Stable.expr_port_26_3, global_expr_1049.
 rewrite top_word_315.
 reflexivity. Qed. Opaque Stable.port_26_3 global_word_1049.
Transparent Stable.port_27_0 global_word_1350. Lemma top_port_27_0 v : Stable.port_27_0 (top_global_leaves v) = global_word_1350 v.
Proof. unfold Stable.port_27_0, global_word_1350, Stable.closed_port_27_0, global_closed_1350, Stable.expr_port_27_0, global_expr_1350.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_27_0 global_word_1350.
Transparent Stable.port_27_1 global_word_1351. Lemma top_port_27_1 v : Stable.port_27_1 (top_global_leaves v) = global_word_1351 v.
Proof. unfold Stable.port_27_1, global_word_1351, Stable.closed_port_27_1, global_closed_1351, Stable.expr_port_27_1, global_expr_1351.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_27_1 global_word_1351.
Transparent Stable.port_27_2 global_word_1067. Lemma top_port_27_2 v : Stable.port_27_2 (top_global_leaves v) = global_word_1067 v.
Proof. unfold Stable.port_27_2, global_word_1067, Stable.closed_port_27_2, global_closed_1067, Stable.expr_port_27_2, global_expr_1067.
 rewrite top_word_319.
 reflexivity. Qed. Opaque Stable.port_27_2 global_word_1067.
Transparent Stable.port_27_3 global_word_1070. Lemma top_port_27_3 v : Stable.port_27_3 (top_global_leaves v) = global_word_1070 v.
Proof. unfold Stable.port_27_3, global_word_1070, Stable.closed_port_27_3, global_closed_1070, Stable.expr_port_27_3, global_expr_1070.
 rewrite top_word_245.
 reflexivity. Qed. Opaque Stable.port_27_3 global_word_1070.
Transparent Stable.port_27_4 global_word_1064. Lemma top_port_27_4 v : Stable.port_27_4 (top_global_leaves v) = global_word_1064 v.
Proof. unfold Stable.port_27_4, global_word_1064, Stable.closed_port_27_4, global_closed_1064, Stable.expr_port_27_4, global_expr_1064.
 rewrite top_word_318.
 reflexivity. Qed. Opaque Stable.port_27_4 global_word_1064.
Transparent Stable.port_28_0 global_word_1352. Lemma top_port_28_0 v : Stable.port_28_0 (top_global_leaves v) = global_word_1352 v.
Proof. unfold Stable.port_28_0, global_word_1352, Stable.closed_port_28_0, global_closed_1352, Stable.expr_port_28_0, global_expr_1352.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_28_0 global_word_1352.
Transparent Stable.port_28_1 global_word_1353. Lemma top_port_28_1 v : Stable.port_28_1 (top_global_leaves v) = global_word_1353 v.
Proof. unfold Stable.port_28_1, global_word_1353, Stable.closed_port_28_1, global_closed_1353, Stable.expr_port_28_1, global_expr_1353.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_28_1 global_word_1353.
Transparent Stable.port_28_2 global_word_1091. Lemma top_port_28_2 v : Stable.port_28_2 (top_global_leaves v) = global_word_1091 v.
Proof. unfold Stable.port_28_2, global_word_1091, Stable.closed_port_28_2, global_closed_1091, Stable.expr_port_28_2, global_expr_1091.
 rewrite top_word_322.
 reflexivity. Qed. Opaque Stable.port_28_2 global_word_1091.
Transparent Stable.port_28_3 global_word_1094. Lemma top_port_28_3 v : Stable.port_28_3 (top_global_leaves v) = global_word_1094 v.
Proof. unfold Stable.port_28_3, global_word_1094, Stable.closed_port_28_3, global_closed_1094, Stable.expr_port_28_3, global_expr_1094.
 rewrite top_word_255.
 reflexivity. Qed. Opaque Stable.port_28_3 global_word_1094.
Transparent Stable.port_28_4 global_word_1088. Lemma top_port_28_4 v : Stable.port_28_4 (top_global_leaves v) = global_word_1088 v.
Proof. unfold Stable.port_28_4, global_word_1088, Stable.closed_port_28_4, global_closed_1088, Stable.expr_port_28_4, global_expr_1088.
 rewrite top_word_321.
 reflexivity. Qed. Opaque Stable.port_28_4 global_word_1088.
Transparent Stable.port_29_0 global_word_1354. Lemma top_port_29_0 v : Stable.port_29_0 (top_global_leaves v) = global_word_1354 v.
Proof. unfold Stable.port_29_0, global_word_1354, Stable.closed_port_29_0, global_closed_1354, Stable.expr_port_29_0, global_expr_1354.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_29_0 global_word_1354.
Transparent Stable.port_29_1 global_word_1355. Lemma top_port_29_1 v : Stable.port_29_1 (top_global_leaves v) = global_word_1355 v.
Proof. unfold Stable.port_29_1, global_word_1355, Stable.closed_port_29_1, global_closed_1355, Stable.expr_port_29_1, global_expr_1355.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_29_1 global_word_1355.
Transparent Stable.port_29_2 global_word_1112. Lemma top_port_29_2 v : Stable.port_29_2 (top_global_leaves v) = global_word_1112 v.
Proof. unfold Stable.port_29_2, global_word_1112, Stable.closed_port_29_2, global_closed_1112, Stable.expr_port_29_2, global_expr_1112.
 rewrite top_word_325.
 reflexivity. Qed. Opaque Stable.port_29_2 global_word_1112.
Transparent Stable.port_29_3 global_word_1115. Lemma top_port_29_3 v : Stable.port_29_3 (top_global_leaves v) = global_word_1115 v.
Proof. unfold Stable.port_29_3, global_word_1115, Stable.closed_port_29_3, global_closed_1115, Stable.expr_port_29_3, global_expr_1115.
 rewrite top_word_324.
 reflexivity. Qed. Opaque Stable.port_29_3 global_word_1115.
Transparent Stable.port_30_0 global_word_1356. Lemma top_port_30_0 v : Stable.port_30_0 (top_global_leaves v) = global_word_1356 v.
Proof. unfold Stable.port_30_0, global_word_1356, Stable.closed_port_30_0, global_closed_1356, Stable.expr_port_30_0, global_expr_1356.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_30_0 global_word_1356.
Transparent Stable.port_30_1 global_word_1357. Lemma top_port_30_1 v : Stable.port_30_1 (top_global_leaves v) = global_word_1357 v.
Proof. unfold Stable.port_30_1, global_word_1357, Stable.closed_port_30_1, global_closed_1357, Stable.expr_port_30_1, global_expr_1357.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_30_1 global_word_1357.
Transparent Stable.port_30_2 global_word_1130. Lemma top_port_30_2 v : Stable.port_30_2 (top_global_leaves v) = global_word_1130 v.
Proof. unfold Stable.port_30_2, global_word_1130, Stable.closed_port_30_2, global_closed_1130, Stable.expr_port_30_2, global_expr_1130.
 rewrite top_word_328.
 reflexivity. Qed. Opaque Stable.port_30_2 global_word_1130.
Transparent Stable.port_30_3 global_word_1133. Lemma top_port_30_3 v : Stable.port_30_3 (top_global_leaves v) = global_word_1133 v.
Proof. unfold Stable.port_30_3, global_word_1133, Stable.closed_port_30_3, global_closed_1133, Stable.expr_port_30_3, global_expr_1133.
 rewrite top_word_327.
 reflexivity. Qed. Opaque Stable.port_30_3 global_word_1133.
Transparent Stable.port_31_0 global_word_1358. Lemma top_port_31_0 v : Stable.port_31_0 (top_global_leaves v) = global_word_1358 v.
Proof. unfold Stable.port_31_0, global_word_1358, Stable.closed_port_31_0, global_closed_1358, Stable.expr_port_31_0, global_expr_1358.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_31_0 global_word_1358.
Transparent Stable.port_31_1 global_word_1359. Lemma top_port_31_1 v : Stable.port_31_1 (top_global_leaves v) = global_word_1359 v.
Proof. unfold Stable.port_31_1, global_word_1359, Stable.closed_port_31_1, global_closed_1359, Stable.expr_port_31_1, global_expr_1359.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_31_1 global_word_1359.
Transparent Stable.port_31_2 global_word_1148. Lemma top_port_31_2 v : Stable.port_31_2 (top_global_leaves v) = global_word_1148 v.
Proof. unfold Stable.port_31_2, global_word_1148, Stable.closed_port_31_2, global_closed_1148, Stable.expr_port_31_2, global_expr_1148.
 rewrite top_word_331.
 reflexivity. Qed. Opaque Stable.port_31_2 global_word_1148.
Transparent Stable.port_31_3 global_word_1151. Lemma top_port_31_3 v : Stable.port_31_3 (top_global_leaves v) = global_word_1151 v.
Proof. unfold Stable.port_31_3, global_word_1151, Stable.closed_port_31_3, global_closed_1151, Stable.expr_port_31_3, global_expr_1151.
 rewrite top_word_330.
 reflexivity. Qed. Opaque Stable.port_31_3 global_word_1151.
Transparent Stable.port_32_0 global_word_1360. Lemma top_port_32_0 v : Stable.port_32_0 (top_global_leaves v) = global_word_1360 v.
Proof. unfold Stable.port_32_0, global_word_1360, Stable.closed_port_32_0, global_closed_1360, Stable.expr_port_32_0, global_expr_1360.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_32_0 global_word_1360.
Transparent Stable.port_32_1 global_word_1361. Lemma top_port_32_1 v : Stable.port_32_1 (top_global_leaves v) = global_word_1361 v.
Proof. unfold Stable.port_32_1, global_word_1361, Stable.closed_port_32_1, global_closed_1361, Stable.expr_port_32_1, global_expr_1361.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_32_1 global_word_1361.
Transparent Stable.port_32_2 global_word_1166. Lemma top_port_32_2 v : Stable.port_32_2 (top_global_leaves v) = global_word_1166 v.
Proof. unfold Stable.port_32_2, global_word_1166, Stable.closed_port_32_2, global_closed_1166, Stable.expr_port_32_2, global_expr_1166.
 rewrite top_word_334.
 reflexivity. Qed. Opaque Stable.port_32_2 global_word_1166.
Transparent Stable.port_32_3 global_word_1169. Lemma top_port_32_3 v : Stable.port_32_3 (top_global_leaves v) = global_word_1169 v.
Proof. unfold Stable.port_32_3, global_word_1169, Stable.closed_port_32_3, global_closed_1169, Stable.expr_port_32_3, global_expr_1169.
 rewrite top_word_333.
 reflexivity. Qed. Opaque Stable.port_32_3 global_word_1169.
Transparent Stable.port_33_0 global_word_1362. Lemma top_port_33_0 v : Stable.port_33_0 (top_global_leaves v) = global_word_1362 v.
Proof. unfold Stable.port_33_0, global_word_1362, Stable.closed_port_33_0, global_closed_1362, Stable.expr_port_33_0, global_expr_1362.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_33_0 global_word_1362.
Transparent Stable.port_33_1 global_word_1363. Lemma top_port_33_1 v : Stable.port_33_1 (top_global_leaves v) = global_word_1363 v.
Proof. unfold Stable.port_33_1, global_word_1363, Stable.closed_port_33_1, global_closed_1363, Stable.expr_port_33_1, global_expr_1363.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_33_1 global_word_1363.
Transparent Stable.port_33_2 global_word_1187. Lemma top_port_33_2 v : Stable.port_33_2 (top_global_leaves v) = global_word_1187 v.
Proof. unfold Stable.port_33_2, global_word_1187, Stable.closed_port_33_2, global_closed_1187, Stable.expr_port_33_2, global_expr_1187.
 rewrite top_word_337.
 reflexivity. Qed. Opaque Stable.port_33_2 global_word_1187.
Transparent Stable.port_33_3 global_word_1190. Lemma top_port_33_3 v : Stable.port_33_3 (top_global_leaves v) = global_word_1190 v.
Proof. unfold Stable.port_33_3, global_word_1190, Stable.closed_port_33_3, global_closed_1190, Stable.expr_port_33_3, global_expr_1190.
 rewrite top_word_335.
 reflexivity. Qed. Opaque Stable.port_33_3 global_word_1190.
Transparent Stable.port_33_4 global_word_1184. Lemma top_port_33_4 v : Stable.port_33_4 (top_global_leaves v) = global_word_1184 v.
Proof. unfold Stable.port_33_4, global_word_1184, Stable.closed_port_33_4, global_closed_1184, Stable.expr_port_33_4, global_expr_1184.
 rewrite top_word_336.
 reflexivity. Qed. Opaque Stable.port_33_4 global_word_1184.
Transparent Stable.port_34_0 global_word_1364. Lemma top_port_34_0 v : Stable.port_34_0 (top_global_leaves v) = global_word_1364 v.
Proof. unfold Stable.port_34_0, global_word_1364, Stable.closed_port_34_0, global_closed_1364, Stable.expr_port_34_0, global_expr_1364.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_34_0 global_word_1364.
Transparent Stable.port_34_1 global_word_1365. Lemma top_port_34_1 v : Stable.port_34_1 (top_global_leaves v) = global_word_1365 v.
Proof. unfold Stable.port_34_1, global_word_1365, Stable.closed_port_34_1, global_closed_1365, Stable.expr_port_34_1, global_expr_1365.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_34_1 global_word_1365.
Transparent Stable.port_34_2 global_word_1208. Lemma top_port_34_2 v : Stable.port_34_2 (top_global_leaves v) = global_word_1208 v.
Proof. unfold Stable.port_34_2, global_word_1208, Stable.closed_port_34_2, global_closed_1208, Stable.expr_port_34_2, global_expr_1208.
 rewrite top_word_339.
 reflexivity. Qed. Opaque Stable.port_34_2 global_word_1208.
Transparent Stable.port_34_3 global_word_1211. Lemma top_port_34_3 v : Stable.port_34_3 (top_global_leaves v) = global_word_1211 v.
Proof. unfold Stable.port_34_3, global_word_1211, Stable.closed_port_34_3, global_closed_1211, Stable.expr_port_34_3, global_expr_1211.
 rewrite top_word_338.
 reflexivity. Qed. Opaque Stable.port_34_3 global_word_1211.
Transparent Stable.port_35_0 global_word_1366. Lemma top_port_35_0 v : Stable.port_35_0 (top_global_leaves v) = global_word_1366 v.
Proof. unfold Stable.port_35_0, global_word_1366, Stable.closed_port_35_0, global_closed_1366, Stable.expr_port_35_0, global_expr_1366.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_35_0 global_word_1366.
Transparent Stable.port_35_1 global_word_1367. Lemma top_port_35_1 v : Stable.port_35_1 (top_global_leaves v) = global_word_1367 v.
Proof. unfold Stable.port_35_1, global_word_1367, Stable.closed_port_35_1, global_closed_1367, Stable.expr_port_35_1, global_expr_1367.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_35_1 global_word_1367.
Transparent Stable.port_35_2 global_word_1226. Lemma top_port_35_2 v : Stable.port_35_2 (top_global_leaves v) = global_word_1226 v.
Proof. unfold Stable.port_35_2, global_word_1226, Stable.closed_port_35_2, global_closed_1226, Stable.expr_port_35_2, global_expr_1226.
 rewrite top_word_341.
 reflexivity. Qed. Opaque Stable.port_35_2 global_word_1226.
Transparent Stable.port_35_3 global_word_1229. Lemma top_port_35_3 v : Stable.port_35_3 (top_global_leaves v) = global_word_1229 v.
Proof. unfold Stable.port_35_3, global_word_1229, Stable.closed_port_35_3, global_closed_1229, Stable.expr_port_35_3, global_expr_1229.
 rewrite top_word_340.
 reflexivity. Qed. Opaque Stable.port_35_3 global_word_1229.
Transparent Stable.port_36_0 global_word_1368. Lemma top_port_36_0 v : Stable.port_36_0 (top_global_leaves v) = global_word_1368 v.
Proof. unfold Stable.port_36_0, global_word_1368, Stable.closed_port_36_0, global_closed_1368, Stable.expr_port_36_0, global_expr_1368.
 rewrite top_word_0.
 reflexivity. Qed. Opaque Stable.port_36_0 global_word_1368.
Transparent Stable.port_36_1 global_word_1369. Lemma top_port_36_1 v : Stable.port_36_1 (top_global_leaves v) = global_word_1369 v.
Proof. unfold Stable.port_36_1, global_word_1369, Stable.closed_port_36_1, global_closed_1369, Stable.expr_port_36_1, global_expr_1369.
 rewrite top_word_1.
 reflexivity. Qed. Opaque Stable.port_36_1 global_word_1369.
Transparent Stable.port_36_2 global_word_1244. Lemma top_port_36_2 v : Stable.port_36_2 (top_global_leaves v) = global_word_1244 v.
Proof. unfold Stable.port_36_2, global_word_1244, Stable.closed_port_36_2, global_closed_1244, Stable.expr_port_36_2, global_expr_1244.
 rewrite top_word_303.
 reflexivity. Qed. Opaque Stable.port_36_2 global_word_1244.
Transparent Stable.port_36_3 global_word_1247. Lemma top_port_36_3 v : Stable.port_36_3 (top_global_leaves v) = global_word_1247 v.
Proof. unfold Stable.port_36_3, global_word_1247, Stable.closed_port_36_3, global_closed_1247, Stable.expr_port_36_3, global_expr_1247.
 rewrite top_word_342.
 reflexivity. Qed. Opaque Stable.port_36_3 global_word_1247.
Theorem global_packed_product v a b
 (Ha : global_word_2 v = from_N 8 a) (Hb : global_word_53 v = from_N 8 b)
 (Hamin : N.lt a 256) (Hbmin : N.lt b 256) :
 Z.modulo (to_Zpos (global_word_96 v) + to_Zpos (global_word_132 v) + 4*to_Zpos (global_word_169 v) + 16*to_Zpos (global_word_205 v) + 64*to_Zpos (global_word_223 v)) 65536 =
 Z.modulo (Z.mul (signed8 (Z.of_N a)) (signed8 (Z.of_N b))) 65536.
Proof.
 rewrite - (top_word_71 v) - (top_word_107 v) - (top_word_144 v) - (top_word_180 v) - (top_word_198 v).
 exact (ast_front_product (top_global_leaves v) a b Ha Hb Hamin Hbmin).
Qed.
Print Assumptions global_packed_product.
