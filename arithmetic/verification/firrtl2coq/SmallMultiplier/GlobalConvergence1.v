From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_1 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 200 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_200 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_201 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_202 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_203 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_204 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_205 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_206 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_207 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_208 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_209 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_210 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_211 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_212 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_213 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_214 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_215 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_216 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_217 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_218 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_219 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_220 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_221 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_222 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_223 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_224 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_225 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_226 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_227 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_228 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_229 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_230 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_231 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_232 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_233 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_234 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_235 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_236 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_237 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_238 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_239 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_240 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_241 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_242 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_243 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_244 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_245 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_246 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_247 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_248 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_249 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_250 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_251 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_252 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_253 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_254 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_255 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_256 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_257 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_258 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_259 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_260 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_261 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_262 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_263 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_264 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_265 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_266 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_267 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_268 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_269 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_270 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_271 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_272 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_273 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_274 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_275 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_276 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_277 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_278 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_279 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_280 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_281 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_282 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_283 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_284 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_285 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_286 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_287 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_288 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_289 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_290 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_291 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_292 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_293 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_294 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_295 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_296 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_297 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_298 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_299 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_300 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_301 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_302 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_303 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_304 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_305 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_306 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_307 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_308 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_309 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_310 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_311 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_312 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_313 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_314 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_315 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_316 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_317 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_318 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_319 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_320 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_321 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_322 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_323 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_324 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_325 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_326 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_327 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_328 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_329 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_330 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_331 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_332 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_333 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_334 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_335 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_336 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_337 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_338 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_339 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_340 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_341 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_342 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_343 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_344 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_345 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_346 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_347 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_348 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_349 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_350 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_351 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_352 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_353 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_354 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_355 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_356 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_357 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_358 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_359 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_360 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_361 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_362 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_363 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_364 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_365 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_366 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_367 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_368 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_369 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_370 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_371 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_372 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_373 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_374 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_375 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_376 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_377 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_378 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_379 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_380 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_381 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_382 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_383 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_384 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_385 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_386 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_387 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_388 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_389 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_390 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_391 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_392 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_393 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_394 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_395 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_396 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_397 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_398 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_399 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_1 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 200 200).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_278 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_281 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_289 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_293 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_296 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_299 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_307 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_311 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_314 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_317 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_320 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_331 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_335 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_338 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_341 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_344 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_355 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_359 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_362 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_365 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_368 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_370 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_373 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_375 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_378 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_380 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_391 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_394 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_397 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.
