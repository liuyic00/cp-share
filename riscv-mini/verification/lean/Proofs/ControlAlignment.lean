import Proofs.Pipeline
set_option linter.unusedVariables false
namespace RiscvMiniProofs
open nCoreSoc
-- Pure decoder cones copied mechanically from the unchanged model.
-- The equalities below are checked by the Lean kernel, not assumed.
def decode_v7298 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 55
def decode_v7299 (instruction : BitVec 32) : BitVec 32 := instruction
def decode_v7300 (instruction : BitVec 32) : BitVec 32 := (decode_v7299 instruction)
def decode_v7301 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def decode_v7302 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7301 instruction))
def decode_v7303 (instruction : BitVec 32) : BitVec 1 := if (decode_v7298 instruction) = (decode_v7302 instruction) then 1 else 0
def decode_v32 (instruction : BitVec 32) : BitVec 2 := BitVec.ofNat 2 0
def decode_v7304 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 23
def decode_v7305 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def decode_v7306 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7305 instruction))
def decode_v7307 (instruction : BitVec 32) : BitVec 1 := if (decode_v7304 instruction) = (decode_v7306 instruction) then 1 else 0
def decode_v7308 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 111
def decode_v7309 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def decode_v7310 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7309 instruction))
def decode_v7311 (instruction : BitVec 32) : BitVec 1 := if (decode_v7308 instruction) = (decode_v7310 instruction) then 1 else 0
def decode_v7312 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 103
def decode_v7313 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7314 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7313 instruction))
def decode_v7315 (instruction : BitVec 32) : BitVec 1 := if (decode_v7312 instruction) = (decode_v7314 instruction) then 1 else 0
def decode_v7316 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 99
def decode_v7317 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7318 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7317 instruction))
def decode_v7319 (instruction : BitVec 32) : BitVec 1 := if (decode_v7316 instruction) = (decode_v7318 instruction) then 1 else 0
def decode_v7320 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4195
def decode_v7321 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7322 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7321 instruction))
def decode_v7323 (instruction : BitVec 32) : BitVec 1 := if (decode_v7320 instruction) = (decode_v7322 instruction) then 1 else 0
def decode_v7324 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16483
def decode_v7325 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7326 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7325 instruction))
def decode_v7327 (instruction : BitVec 32) : BitVec 1 := if (decode_v7324 instruction) = (decode_v7326 instruction) then 1 else 0
def decode_v7328 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20579
def decode_v7329 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7330 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7329 instruction))
def decode_v7331 (instruction : BitVec 32) : BitVec 1 := if (decode_v7328 instruction) = (decode_v7330 instruction) then 1 else 0
def decode_v7332 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24675
def decode_v7333 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7334 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7333 instruction))
def decode_v7335 (instruction : BitVec 32) : BitVec 1 := if (decode_v7332 instruction) = (decode_v7334 instruction) then 1 else 0
def decode_v7336 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28771
def decode_v7337 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7338 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7337 instruction))
def decode_v7339 (instruction : BitVec 32) : BitVec 1 := if (decode_v7336 instruction) = (decode_v7338 instruction) then 1 else 0
def decode_v7340 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 3
def decode_v7341 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7342 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7341 instruction))
def decode_v7343 (instruction : BitVec 32) : BitVec 1 := if (decode_v7340 instruction) = (decode_v7342 instruction) then 1 else 0
def decode_v7344 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4099
def decode_v7345 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7346 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7345 instruction))
def decode_v7347 (instruction : BitVec 32) : BitVec 1 := if (decode_v7344 instruction) = (decode_v7346 instruction) then 1 else 0
def decode_v7348 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8195
def decode_v7349 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7350 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7349 instruction))
def decode_v7351 (instruction : BitVec 32) : BitVec 1 := if (decode_v7348 instruction) = (decode_v7350 instruction) then 1 else 0
def decode_v7352 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16387
def decode_v7353 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7354 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7353 instruction))
def decode_v7355 (instruction : BitVec 32) : BitVec 1 := if (decode_v7352 instruction) = (decode_v7354 instruction) then 1 else 0
def decode_v7356 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20483
def decode_v7357 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7358 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7357 instruction))
def decode_v7359 (instruction : BitVec 32) : BitVec 1 := if (decode_v7356 instruction) = (decode_v7358 instruction) then 1 else 0
def decode_v7360 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 35
def decode_v7361 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7362 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7361 instruction))
def decode_v7363 (instruction : BitVec 32) : BitVec 1 := if (decode_v7360 instruction) = (decode_v7362 instruction) then 1 else 0
def decode_v155 (instruction : BitVec 32) : BitVec 2 := BitVec.ofNat 2 3
def decode_v7364 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4131
def decode_v7365 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7366 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7365 instruction))
def decode_v7367 (instruction : BitVec 32) : BitVec 1 := if (decode_v7364 instruction) = (decode_v7366 instruction) then 1 else 0
def decode_v38 (instruction : BitVec 32) : BitVec 2 := BitVec.ofNat 2 2
def decode_v7368 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8227
def decode_v7369 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7370 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7369 instruction))
def decode_v7371 (instruction : BitVec 32) : BitVec 1 := if (decode_v7368 instruction) = (decode_v7370 instruction) then 1 else 0
def decode_v42 (instruction : BitVec 32) : BitVec 2 := BitVec.ofNat 2 1
def decode_v8174 (instruction : BitVec 32) : BitVec 2 := if (decode_v7371 instruction) = 1 then (decode_v42 instruction) else (decode_v32 instruction)
def decode_v8175 (instruction : BitVec 32) : BitVec 2 := if (decode_v7367 instruction) = 1 then (decode_v38 instruction) else (decode_v8174 instruction)
def decode_v8176 (instruction : BitVec 32) : BitVec 2 := if (decode_v7363 instruction) = 1 then (decode_v155 instruction) else (decode_v8175 instruction)
def decode_v8177 (instruction : BitVec 32) : BitVec 2 := if (decode_v7359 instruction) = 1 then (decode_v32 instruction) else (decode_v8176 instruction)
def decode_v8178 (instruction : BitVec 32) : BitVec 2 := if (decode_v7355 instruction) = 1 then (decode_v32 instruction) else (decode_v8177 instruction)
def decode_v8179 (instruction : BitVec 32) : BitVec 2 := if (decode_v7351 instruction) = 1 then (decode_v32 instruction) else (decode_v8178 instruction)
def decode_v8180 (instruction : BitVec 32) : BitVec 2 := if (decode_v7347 instruction) = 1 then (decode_v32 instruction) else (decode_v8179 instruction)
def decode_v8181 (instruction : BitVec 32) : BitVec 2 := if (decode_v7343 instruction) = 1 then (decode_v32 instruction) else (decode_v8180 instruction)
def decode_v8182 (instruction : BitVec 32) : BitVec 2 := if (decode_v7339 instruction) = 1 then (decode_v32 instruction) else (decode_v8181 instruction)
def decode_v8183 (instruction : BitVec 32) : BitVec 2 := if (decode_v7335 instruction) = 1 then (decode_v32 instruction) else (decode_v8182 instruction)
def decode_v8184 (instruction : BitVec 32) : BitVec 2 := if (decode_v7331 instruction) = 1 then (decode_v32 instruction) else (decode_v8183 instruction)
def decode_v8185 (instruction : BitVec 32) : BitVec 2 := if (decode_v7327 instruction) = 1 then (decode_v32 instruction) else (decode_v8184 instruction)
def decode_v8186 (instruction : BitVec 32) : BitVec 2 := if (decode_v7323 instruction) = 1 then (decode_v32 instruction) else (decode_v8185 instruction)
def decode_v8187 (instruction : BitVec 32) : BitVec 2 := if (decode_v7319 instruction) = 1 then (decode_v32 instruction) else (decode_v8186 instruction)
def decode_v8188 (instruction : BitVec 32) : BitVec 2 := if (decode_v7315 instruction) = 1 then (decode_v32 instruction) else (decode_v8187 instruction)
def decode_v8189 (instruction : BitVec 32) : BitVec 2 := if (decode_v7311 instruction) = 1 then (decode_v32 instruction) else (decode_v8188 instruction)
def decode_v8190 (instruction : BitVec 32) : BitVec 2 := if (decode_v7307 instruction) = 1 then (decode_v32 instruction) else (decode_v8189 instruction)
def decode_v8191 (instruction : BitVec 32) : BitVec 2 := if (decode_v7303 instruction) = 1 then (decode_v32 instruction) else (decode_v8190 instruction)
def decode_v8192 (instruction : BitVec 32) : BitVec 2 := (decode_v8191 instruction)
def decode_v8193 (instruction : BitVec 32) : BitVec 2 := (decode_v8192 instruction)
def decode_v261 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 0
def decode_v200 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 3
def decode_v26 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 2
def decode_v29 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 1
def decode_v716 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 5
def decode_v22 (instruction : BitVec 32) : BitVec 3 := BitVec.ofNat 3 4
def decode_v8197 (instruction : BitVec 32) : BitVec 3 := if (decode_v7359 instruction) = 1 then (decode_v22 instruction) else (decode_v261 instruction)
def decode_v8198 (instruction : BitVec 32) : BitVec 3 := if (decode_v7355 instruction) = 1 then (decode_v716 instruction) else (decode_v8197 instruction)
def decode_v8199 (instruction : BitVec 32) : BitVec 3 := if (decode_v7351 instruction) = 1 then (decode_v29 instruction) else (decode_v8198 instruction)
def decode_v8200 (instruction : BitVec 32) : BitVec 3 := if (decode_v7347 instruction) = 1 then (decode_v26 instruction) else (decode_v8199 instruction)
def decode_v8201 (instruction : BitVec 32) : BitVec 3 := if (decode_v7343 instruction) = 1 then (decode_v200 instruction) else (decode_v8200 instruction)
def decode_v8202 (instruction : BitVec 32) : BitVec 3 := if (decode_v7339 instruction) = 1 then (decode_v261 instruction) else (decode_v8201 instruction)
def decode_v8203 (instruction : BitVec 32) : BitVec 3 := if (decode_v7335 instruction) = 1 then (decode_v261 instruction) else (decode_v8202 instruction)
def decode_v8204 (instruction : BitVec 32) : BitVec 3 := if (decode_v7331 instruction) = 1 then (decode_v261 instruction) else (decode_v8203 instruction)
def decode_v8205 (instruction : BitVec 32) : BitVec 3 := if (decode_v7327 instruction) = 1 then (decode_v261 instruction) else (decode_v8204 instruction)
def decode_v8206 (instruction : BitVec 32) : BitVec 3 := if (decode_v7323 instruction) = 1 then (decode_v261 instruction) else (decode_v8205 instruction)
def decode_v8207 (instruction : BitVec 32) : BitVec 3 := if (decode_v7319 instruction) = 1 then (decode_v261 instruction) else (decode_v8206 instruction)
def decode_v8208 (instruction : BitVec 32) : BitVec 3 := if (decode_v7315 instruction) = 1 then (decode_v261 instruction) else (decode_v8207 instruction)
def decode_v8209 (instruction : BitVec 32) : BitVec 3 := if (decode_v7311 instruction) = 1 then (decode_v261 instruction) else (decode_v8208 instruction)
def decode_v8210 (instruction : BitVec 32) : BitVec 3 := if (decode_v7307 instruction) = 1 then (decode_v261 instruction) else (decode_v8209 instruction)
def decode_v8211 (instruction : BitVec 32) : BitVec 3 := if (decode_v7303 instruction) = 1 then (decode_v261 instruction) else (decode_v8210 instruction)
def decode_v8212 (instruction : BitVec 32) : BitVec 3 := (decode_v8211 instruction)
def decode_v8213 (instruction : BitVec 32) : BitVec 3 := (decode_v8212 instruction)
def decode_v7372 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 19
def decode_v7373 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7374 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7373 instruction))
def decode_v7375 (instruction : BitVec 32) : BitVec 1 := if (decode_v7372 instruction) = (decode_v7374 instruction) then 1 else 0
def decode_v7376 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8211
def decode_v7377 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7378 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7377 instruction))
def decode_v7379 (instruction : BitVec 32) : BitVec 1 := if (decode_v7376 instruction) = (decode_v7378 instruction) then 1 else 0
def decode_v7380 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12307
def decode_v7381 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7382 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7381 instruction))
def decode_v7383 (instruction : BitVec 32) : BitVec 1 := if (decode_v7380 instruction) = (decode_v7382 instruction) then 1 else 0
def decode_v7384 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16403
def decode_v7385 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7386 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7385 instruction))
def decode_v7387 (instruction : BitVec 32) : BitVec 1 := if (decode_v7384 instruction) = (decode_v7386 instruction) then 1 else 0
def decode_v7388 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24595
def decode_v7389 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7390 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7389 instruction))
def decode_v7391 (instruction : BitVec 32) : BitVec 1 := if (decode_v7388 instruction) = (decode_v7390 instruction) then 1 else 0
def decode_v7392 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28691
def decode_v7393 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7394 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7393 instruction))
def decode_v7395 (instruction : BitVec 32) : BitVec 1 := if (decode_v7392 instruction) = (decode_v7394 instruction) then 1 else 0
def decode_v7396 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4115
def decode_v978 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4261441663
def decode_v7397 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7398 (instruction : BitVec 32) : BitVec 1 := if (decode_v7396 instruction) = (decode_v7397 instruction) then 1 else 0
def decode_v7399 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20499
def decode_v7400 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7401 (instruction : BitVec 32) : BitVec 1 := if (decode_v7399 instruction) = (decode_v7400 instruction) then 1 else 0
def decode_v7402 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762323
def decode_v7403 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7404 (instruction : BitVec 32) : BitVec 1 := if (decode_v7402 instruction) = (decode_v7403 instruction) then 1 else 0
def decode_v7405 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 51
def decode_v7406 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7407 (instruction : BitVec 32) : BitVec 1 := if (decode_v7405 instruction) = (decode_v7406 instruction) then 1 else 0
def decode_v7408 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073741875
def decode_v7409 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7410 (instruction : BitVec 32) : BitVec 1 := if (decode_v7408 instruction) = (decode_v7409 instruction) then 1 else 0
def decode_v7411 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4147
def decode_v7412 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7413 (instruction : BitVec 32) : BitVec 1 := if (decode_v7411 instruction) = (decode_v7412 instruction) then 1 else 0
def decode_v7414 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8243
def decode_v7415 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7416 (instruction : BitVec 32) : BitVec 1 := if (decode_v7414 instruction) = (decode_v7415 instruction) then 1 else 0
def decode_v7417 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12339
def decode_v7418 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7419 (instruction : BitVec 32) : BitVec 1 := if (decode_v7417 instruction) = (decode_v7418 instruction) then 1 else 0
def decode_v7420 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16435
def decode_v7421 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7422 (instruction : BitVec 32) : BitVec 1 := if (decode_v7420 instruction) = (decode_v7421 instruction) then 1 else 0
def decode_v7423 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20531
def decode_v7424 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7425 (instruction : BitVec 32) : BitVec 1 := if (decode_v7423 instruction) = (decode_v7424 instruction) then 1 else 0
def decode_v7426 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762355
def decode_v7427 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7428 (instruction : BitVec 32) : BitVec 1 := if (decode_v7426 instruction) = (decode_v7427 instruction) then 1 else 0
def decode_v7429 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24627
def decode_v7430 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7431 (instruction : BitVec 32) : BitVec 1 := if (decode_v7429 instruction) = (decode_v7430 instruction) then 1 else 0
def decode_v7432 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28723
def decode_v7433 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v978 instruction))
def decode_v7434 (instruction : BitVec 32) : BitVec 1 := if (decode_v7432 instruction) = (decode_v7433 instruction) then 1 else 0
def decode_v7435 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 15
def decode_v7436 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4027580415
def decode_v7437 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7436 instruction))
def decode_v7438 (instruction : BitVec 32) : BitVec 1 := if (decode_v7435 instruction) = (decode_v7437 instruction) then 1 else 0
def decode_v7439 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4111
def decode_v7440 (instruction : BitVec 32) : BitVec 1 := if (decode_v7439 instruction) = (decode_v7300 instruction) then 1 else 0
def decode_v7441 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4211
def decode_v7442 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7443 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7442 instruction))
def decode_v7444 (instruction : BitVec 32) : BitVec 1 := if (decode_v7441 instruction) = (decode_v7443 instruction) then 1 else 0
def decode_v7445 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8307
def decode_v7446 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7447 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7446 instruction))
def decode_v7448 (instruction : BitVec 32) : BitVec 1 := if (decode_v7445 instruction) = (decode_v7447 instruction) then 1 else 0
def decode_v7449 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12403
def decode_v7450 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7451 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7450 instruction))
def decode_v7452 (instruction : BitVec 32) : BitVec 1 := if (decode_v7449 instruction) = (decode_v7451 instruction) then 1 else 0
def decode_v7453 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20595
def decode_v7454 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7455 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7454 instruction))
def decode_v7456 (instruction : BitVec 32) : BitVec 1 := if (decode_v7453 instruction) = (decode_v7455 instruction) then 1 else 0
def decode_v7457 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24691
def decode_v7458 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7459 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7458 instruction))
def decode_v7460 (instruction : BitVec 32) : BitVec 1 := if (decode_v7457 instruction) = (decode_v7459 instruction) then 1 else 0
def decode_v7461 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28787
def decode_v7462 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def decode_v7463 (instruction : BitVec 32) : BitVec 32 := ((decode_v7300 instruction) &&& (decode_v7462 instruction))
def decode_v7464 (instruction : BitVec 32) : BitVec 1 := if (decode_v7461 instruction) = (decode_v7463 instruction) then 1 else 0
def decode_v7465 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 115
def decode_v7466 (instruction : BitVec 32) : BitVec 1 := if (decode_v7465 instruction) = (decode_v7300 instruction) then 1 else 0
def decode_v7467 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1048691
def decode_v7468 (instruction : BitVec 32) : BitVec 1 := if (decode_v7467 instruction) = (decode_v7300 instruction) then 1 else 0
def decode_v7469 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 268435571
def decode_v7470 (instruction : BitVec 32) : BitVec 1 := if (decode_v7469 instruction) = (decode_v7300 instruction) then 1 else 0
def decode_v8216 (instruction : BitVec 32) : BitVec 2 := if (decode_v7470 instruction) = 1 then (decode_v155 instruction) else (decode_v32 instruction)
def decode_v8217 (instruction : BitVec 32) : BitVec 2 := if (decode_v7468 instruction) = 1 then (decode_v155 instruction) else (decode_v8216 instruction)
def decode_v8218 (instruction : BitVec 32) : BitVec 2 := if (decode_v7466 instruction) = 1 then (decode_v155 instruction) else (decode_v8217 instruction)
def decode_v8219 (instruction : BitVec 32) : BitVec 2 := if (decode_v7464 instruction) = 1 then (decode_v155 instruction) else (decode_v8218 instruction)
def decode_v8220 (instruction : BitVec 32) : BitVec 2 := if (decode_v7460 instruction) = 1 then (decode_v155 instruction) else (decode_v8219 instruction)
def decode_v8221 (instruction : BitVec 32) : BitVec 2 := if (decode_v7456 instruction) = 1 then (decode_v155 instruction) else (decode_v8220 instruction)
def decode_v8222 (instruction : BitVec 32) : BitVec 2 := if (decode_v7452 instruction) = 1 then (decode_v155 instruction) else (decode_v8221 instruction)
def decode_v8223 (instruction : BitVec 32) : BitVec 2 := if (decode_v7448 instruction) = 1 then (decode_v155 instruction) else (decode_v8222 instruction)
def decode_v8224 (instruction : BitVec 32) : BitVec 2 := if (decode_v7444 instruction) = 1 then (decode_v155 instruction) else (decode_v8223 instruction)
def decode_v8225 (instruction : BitVec 32) : BitVec 2 := if (decode_v7440 instruction) = 1 then (decode_v32 instruction) else (decode_v8224 instruction)
def decode_v8226 (instruction : BitVec 32) : BitVec 2 := if (decode_v7438 instruction) = 1 then (decode_v32 instruction) else (decode_v8225 instruction)
def decode_v8227 (instruction : BitVec 32) : BitVec 2 := if (decode_v7434 instruction) = 1 then (decode_v32 instruction) else (decode_v8226 instruction)
def decode_v8228 (instruction : BitVec 32) : BitVec 2 := if (decode_v7431 instruction) = 1 then (decode_v32 instruction) else (decode_v8227 instruction)
def decode_v8229 (instruction : BitVec 32) : BitVec 2 := if (decode_v7428 instruction) = 1 then (decode_v32 instruction) else (decode_v8228 instruction)
def decode_v8230 (instruction : BitVec 32) : BitVec 2 := if (decode_v7425 instruction) = 1 then (decode_v32 instruction) else (decode_v8229 instruction)
def decode_v8231 (instruction : BitVec 32) : BitVec 2 := if (decode_v7422 instruction) = 1 then (decode_v32 instruction) else (decode_v8230 instruction)
def decode_v8232 (instruction : BitVec 32) : BitVec 2 := if (decode_v7419 instruction) = 1 then (decode_v32 instruction) else (decode_v8231 instruction)
def decode_v8233 (instruction : BitVec 32) : BitVec 2 := if (decode_v7416 instruction) = 1 then (decode_v32 instruction) else (decode_v8232 instruction)
def decode_v8234 (instruction : BitVec 32) : BitVec 2 := if (decode_v7413 instruction) = 1 then (decode_v32 instruction) else (decode_v8233 instruction)
def decode_v8235 (instruction : BitVec 32) : BitVec 2 := if (decode_v7410 instruction) = 1 then (decode_v32 instruction) else (decode_v8234 instruction)
def decode_v8236 (instruction : BitVec 32) : BitVec 2 := if (decode_v7407 instruction) = 1 then (decode_v32 instruction) else (decode_v8235 instruction)
def decode_v8237 (instruction : BitVec 32) : BitVec 2 := if (decode_v7404 instruction) = 1 then (decode_v32 instruction) else (decode_v8236 instruction)
def decode_v8238 (instruction : BitVec 32) : BitVec 2 := if (decode_v7401 instruction) = 1 then (decode_v32 instruction) else (decode_v8237 instruction)
def decode_v8239 (instruction : BitVec 32) : BitVec 2 := if (decode_v7398 instruction) = 1 then (decode_v32 instruction) else (decode_v8238 instruction)
def decode_v8240 (instruction : BitVec 32) : BitVec 2 := if (decode_v7395 instruction) = 1 then (decode_v32 instruction) else (decode_v8239 instruction)
def decode_v8241 (instruction : BitVec 32) : BitVec 2 := if (decode_v7391 instruction) = 1 then (decode_v32 instruction) else (decode_v8240 instruction)
def decode_v8242 (instruction : BitVec 32) : BitVec 2 := if (decode_v7387 instruction) = 1 then (decode_v32 instruction) else (decode_v8241 instruction)
def decode_v8243 (instruction : BitVec 32) : BitVec 2 := if (decode_v7383 instruction) = 1 then (decode_v32 instruction) else (decode_v8242 instruction)
def decode_v8244 (instruction : BitVec 32) : BitVec 2 := if (decode_v7379 instruction) = 1 then (decode_v32 instruction) else (decode_v8243 instruction)
def decode_v8245 (instruction : BitVec 32) : BitVec 2 := if (decode_v7375 instruction) = 1 then (decode_v32 instruction) else (decode_v8244 instruction)
def decode_v8246 (instruction : BitVec 32) : BitVec 2 := if (decode_v7371 instruction) = 1 then (decode_v32 instruction) else (decode_v8245 instruction)
def decode_v8247 (instruction : BitVec 32) : BitVec 2 := if (decode_v7367 instruction) = 1 then (decode_v32 instruction) else (decode_v8246 instruction)
def decode_v8248 (instruction : BitVec 32) : BitVec 2 := if (decode_v7363 instruction) = 1 then (decode_v32 instruction) else (decode_v8247 instruction)
def decode_v8249 (instruction : BitVec 32) : BitVec 2 := if (decode_v7359 instruction) = 1 then (decode_v42 instruction) else (decode_v8248 instruction)
def decode_v8250 (instruction : BitVec 32) : BitVec 2 := if (decode_v7355 instruction) = 1 then (decode_v42 instruction) else (decode_v8249 instruction)
def decode_v8251 (instruction : BitVec 32) : BitVec 2 := if (decode_v7351 instruction) = 1 then (decode_v42 instruction) else (decode_v8250 instruction)
def decode_v8252 (instruction : BitVec 32) : BitVec 2 := if (decode_v7347 instruction) = 1 then (decode_v42 instruction) else (decode_v8251 instruction)
def decode_v8253 (instruction : BitVec 32) : BitVec 2 := if (decode_v7343 instruction) = 1 then (decode_v42 instruction) else (decode_v8252 instruction)
def decode_v8254 (instruction : BitVec 32) : BitVec 2 := if (decode_v7339 instruction) = 1 then (decode_v32 instruction) else (decode_v8253 instruction)
def decode_v8255 (instruction : BitVec 32) : BitVec 2 := if (decode_v7335 instruction) = 1 then (decode_v32 instruction) else (decode_v8254 instruction)
def decode_v8256 (instruction : BitVec 32) : BitVec 2 := if (decode_v7331 instruction) = 1 then (decode_v32 instruction) else (decode_v8255 instruction)
def decode_v8257 (instruction : BitVec 32) : BitVec 2 := if (decode_v7327 instruction) = 1 then (decode_v32 instruction) else (decode_v8256 instruction)
def decode_v8258 (instruction : BitVec 32) : BitVec 2 := if (decode_v7323 instruction) = 1 then (decode_v32 instruction) else (decode_v8257 instruction)
def decode_v8259 (instruction : BitVec 32) : BitVec 2 := if (decode_v7319 instruction) = 1 then (decode_v32 instruction) else (decode_v8258 instruction)
def decode_v8260 (instruction : BitVec 32) : BitVec 2 := if (decode_v7315 instruction) = 1 then (decode_v38 instruction) else (decode_v8259 instruction)
def decode_v8261 (instruction : BitVec 32) : BitVec 2 := if (decode_v7311 instruction) = 1 then (decode_v38 instruction) else (decode_v8260 instruction)
def decode_v8262 (instruction : BitVec 32) : BitVec 2 := if (decode_v7307 instruction) = 1 then (decode_v32 instruction) else (decode_v8261 instruction)
def decode_v8263 (instruction : BitVec 32) : BitVec 2 := if (decode_v7303 instruction) = 1 then (decode_v32 instruction) else (decode_v8262 instruction)
def decode_v8264 (instruction : BitVec 32) : BitVec 2 := (decode_v8263 instruction)
def decode_v8265 (instruction : BitVec 32) : BitVec 2 := (decode_v8264 instruction)
def decode_v512 (instruction : BitVec 32) : BitVec 1 := BitVec.ofNat 1 1
def decode_v4 (instruction : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def decode_v8268 (instruction : BitVec 32) : BitVec 1 := if (decode_v7460 instruction) = 1 then (decode_v512 instruction) else (decode_v7464 instruction)
def decode_v8269 (instruction : BitVec 32) : BitVec 1 := if (decode_v7456 instruction) = 1 then (decode_v512 instruction) else (decode_v8268 instruction)
def decode_v8270 (instruction : BitVec 32) : BitVec 1 := if (decode_v7452 instruction) = 1 then (decode_v512 instruction) else (decode_v8269 instruction)
def decode_v8271 (instruction : BitVec 32) : BitVec 1 := if (decode_v7448 instruction) = 1 then (decode_v512 instruction) else (decode_v8270 instruction)
def decode_v8272 (instruction : BitVec 32) : BitVec 1 := if (decode_v7444 instruction) = 1 then (decode_v512 instruction) else (decode_v8271 instruction)
def decode_v8273 (instruction : BitVec 32) : BitVec 1 := if (decode_v7440 instruction) = 1 then (decode_v4 instruction) else (decode_v8272 instruction)
def decode_v8274 (instruction : BitVec 32) : BitVec 1 := if (decode_v7438 instruction) = 1 then (decode_v4 instruction) else (decode_v8273 instruction)
def decode_v8275 (instruction : BitVec 32) : BitVec 1 := if (decode_v7434 instruction) = 1 then (decode_v512 instruction) else (decode_v8274 instruction)
def decode_v8276 (instruction : BitVec 32) : BitVec 1 := if (decode_v7431 instruction) = 1 then (decode_v512 instruction) else (decode_v8275 instruction)
def decode_v8277 (instruction : BitVec 32) : BitVec 1 := if (decode_v7428 instruction) = 1 then (decode_v512 instruction) else (decode_v8276 instruction)
def decode_v8278 (instruction : BitVec 32) : BitVec 1 := if (decode_v7425 instruction) = 1 then (decode_v512 instruction) else (decode_v8277 instruction)
def decode_v8279 (instruction : BitVec 32) : BitVec 1 := if (decode_v7422 instruction) = 1 then (decode_v512 instruction) else (decode_v8278 instruction)
def decode_v8280 (instruction : BitVec 32) : BitVec 1 := if (decode_v7419 instruction) = 1 then (decode_v512 instruction) else (decode_v8279 instruction)
def decode_v8281 (instruction : BitVec 32) : BitVec 1 := if (decode_v7416 instruction) = 1 then (decode_v512 instruction) else (decode_v8280 instruction)
def decode_v8282 (instruction : BitVec 32) : BitVec 1 := if (decode_v7413 instruction) = 1 then (decode_v512 instruction) else (decode_v8281 instruction)
def decode_v8283 (instruction : BitVec 32) : BitVec 1 := if (decode_v7410 instruction) = 1 then (decode_v512 instruction) else (decode_v8282 instruction)
def decode_v8284 (instruction : BitVec 32) : BitVec 1 := if (decode_v7407 instruction) = 1 then (decode_v512 instruction) else (decode_v8283 instruction)
def decode_v8285 (instruction : BitVec 32) : BitVec 1 := if (decode_v7404 instruction) = 1 then (decode_v512 instruction) else (decode_v8284 instruction)
def decode_v8286 (instruction : BitVec 32) : BitVec 1 := if (decode_v7401 instruction) = 1 then (decode_v512 instruction) else (decode_v8285 instruction)
def decode_v8287 (instruction : BitVec 32) : BitVec 1 := if (decode_v7398 instruction) = 1 then (decode_v512 instruction) else (decode_v8286 instruction)
def decode_v8288 (instruction : BitVec 32) : BitVec 1 := if (decode_v7395 instruction) = 1 then (decode_v512 instruction) else (decode_v8287 instruction)
def decode_v8289 (instruction : BitVec 32) : BitVec 1 := if (decode_v7391 instruction) = 1 then (decode_v512 instruction) else (decode_v8288 instruction)
def decode_v8290 (instruction : BitVec 32) : BitVec 1 := if (decode_v7387 instruction) = 1 then (decode_v512 instruction) else (decode_v8289 instruction)
def decode_v8291 (instruction : BitVec 32) : BitVec 1 := if (decode_v7383 instruction) = 1 then (decode_v512 instruction) else (decode_v8290 instruction)
def decode_v8292 (instruction : BitVec 32) : BitVec 1 := if (decode_v7379 instruction) = 1 then (decode_v512 instruction) else (decode_v8291 instruction)
def decode_v8293 (instruction : BitVec 32) : BitVec 1 := if (decode_v7375 instruction) = 1 then (decode_v512 instruction) else (decode_v8292 instruction)
def decode_v8294 (instruction : BitVec 32) : BitVec 1 := if (decode_v7371 instruction) = 1 then (decode_v4 instruction) else (decode_v8293 instruction)
def decode_v8295 (instruction : BitVec 32) : BitVec 1 := if (decode_v7367 instruction) = 1 then (decode_v4 instruction) else (decode_v8294 instruction)
def decode_v8296 (instruction : BitVec 32) : BitVec 1 := if (decode_v7363 instruction) = 1 then (decode_v4 instruction) else (decode_v8295 instruction)
def decode_v8297 (instruction : BitVec 32) : BitVec 1 := if (decode_v7359 instruction) = 1 then (decode_v512 instruction) else (decode_v8296 instruction)
def decode_v8298 (instruction : BitVec 32) : BitVec 1 := if (decode_v7355 instruction) = 1 then (decode_v512 instruction) else (decode_v8297 instruction)
def decode_v8299 (instruction : BitVec 32) : BitVec 1 := if (decode_v7351 instruction) = 1 then (decode_v512 instruction) else (decode_v8298 instruction)
def decode_v8300 (instruction : BitVec 32) : BitVec 1 := if (decode_v7347 instruction) = 1 then (decode_v512 instruction) else (decode_v8299 instruction)
def decode_v8301 (instruction : BitVec 32) : BitVec 1 := if (decode_v7343 instruction) = 1 then (decode_v512 instruction) else (decode_v8300 instruction)
def decode_v8302 (instruction : BitVec 32) : BitVec 1 := if (decode_v7339 instruction) = 1 then (decode_v4 instruction) else (decode_v8301 instruction)
def decode_v8303 (instruction : BitVec 32) : BitVec 1 := if (decode_v7335 instruction) = 1 then (decode_v4 instruction) else (decode_v8302 instruction)
def decode_v8304 (instruction : BitVec 32) : BitVec 1 := if (decode_v7331 instruction) = 1 then (decode_v4 instruction) else (decode_v8303 instruction)
def decode_v8305 (instruction : BitVec 32) : BitVec 1 := if (decode_v7327 instruction) = 1 then (decode_v4 instruction) else (decode_v8304 instruction)
def decode_v8306 (instruction : BitVec 32) : BitVec 1 := if (decode_v7323 instruction) = 1 then (decode_v4 instruction) else (decode_v8305 instruction)
def decode_v8307 (instruction : BitVec 32) : BitVec 1 := if (decode_v7319 instruction) = 1 then (decode_v4 instruction) else (decode_v8306 instruction)
def decode_v8308 (instruction : BitVec 32) : BitVec 1 := if (decode_v7315 instruction) = 1 then (decode_v512 instruction) else (decode_v8307 instruction)
def decode_v8309 (instruction : BitVec 32) : BitVec 1 := if (decode_v7311 instruction) = 1 then (decode_v512 instruction) else (decode_v8308 instruction)
def decode_v8310 (instruction : BitVec 32) : BitVec 1 := if (decode_v7307 instruction) = 1 then (decode_v512 instruction) else (decode_v8309 instruction)
def decode_v8311 (instruction : BitVec 32) : BitVec 1 := if (decode_v7303 instruction) = 1 then (decode_v512 instruction) else (decode_v8310 instruction)
def decode_v8312 (instruction : BitVec 32) : BitVec 1 := (decode_v8311 instruction)
def decode_v8313 (instruction : BitVec 32) : BitVec 1 := (decode_v8312 instruction)
def decode_v8317 (instruction : BitVec 32) : BitVec 3 := if (decode_v7470 instruction) = 1 then (decode_v22 instruction) else (decode_v261 instruction)
def decode_v8318 (instruction : BitVec 32) : BitVec 3 := if (decode_v7468 instruction) = 1 then (decode_v22 instruction) else (decode_v8317 instruction)
def decode_v8319 (instruction : BitVec 32) : BitVec 3 := if (decode_v7466 instruction) = 1 then (decode_v22 instruction) else (decode_v8318 instruction)
def decode_v8320 (instruction : BitVec 32) : BitVec 3 := if (decode_v7464 instruction) = 1 then (decode_v200 instruction) else (decode_v8319 instruction)
def decode_v8321 (instruction : BitVec 32) : BitVec 3 := if (decode_v7460 instruction) = 1 then (decode_v26 instruction) else (decode_v8320 instruction)
def decode_v8322 (instruction : BitVec 32) : BitVec 3 := if (decode_v7456 instruction) = 1 then (decode_v29 instruction) else (decode_v8321 instruction)
def decode_v8323 (instruction : BitVec 32) : BitVec 3 := if (decode_v7452 instruction) = 1 then (decode_v200 instruction) else (decode_v8322 instruction)
def decode_v8324 (instruction : BitVec 32) : BitVec 3 := if (decode_v7448 instruction) = 1 then (decode_v26 instruction) else (decode_v8323 instruction)
def decode_v8325 (instruction : BitVec 32) : BitVec 3 := if (decode_v7444 instruction) = 1 then (decode_v29 instruction) else (decode_v8324 instruction)
def decode_v8326 (instruction : BitVec 32) : BitVec 3 := if (decode_v7440 instruction) = 1 then (decode_v261 instruction) else (decode_v8325 instruction)
def decode_v8327 (instruction : BitVec 32) : BitVec 3 := if (decode_v7438 instruction) = 1 then (decode_v261 instruction) else (decode_v8326 instruction)
def decode_v8328 (instruction : BitVec 32) : BitVec 3 := if (decode_v7434 instruction) = 1 then (decode_v261 instruction) else (decode_v8327 instruction)
def decode_v8329 (instruction : BitVec 32) : BitVec 3 := if (decode_v7431 instruction) = 1 then (decode_v261 instruction) else (decode_v8328 instruction)
def decode_v8330 (instruction : BitVec 32) : BitVec 3 := if (decode_v7428 instruction) = 1 then (decode_v261 instruction) else (decode_v8329 instruction)
def decode_v8331 (instruction : BitVec 32) : BitVec 3 := if (decode_v7425 instruction) = 1 then (decode_v261 instruction) else (decode_v8330 instruction)
def decode_v8332 (instruction : BitVec 32) : BitVec 3 := if (decode_v7422 instruction) = 1 then (decode_v261 instruction) else (decode_v8331 instruction)
def decode_v8333 (instruction : BitVec 32) : BitVec 3 := if (decode_v7419 instruction) = 1 then (decode_v261 instruction) else (decode_v8332 instruction)
def decode_v8334 (instruction : BitVec 32) : BitVec 3 := if (decode_v7416 instruction) = 1 then (decode_v261 instruction) else (decode_v8333 instruction)
def decode_v8335 (instruction : BitVec 32) : BitVec 3 := if (decode_v7413 instruction) = 1 then (decode_v261 instruction) else (decode_v8334 instruction)
def decode_v8336 (instruction : BitVec 32) : BitVec 3 := if (decode_v7410 instruction) = 1 then (decode_v261 instruction) else (decode_v8335 instruction)
def decode_v8337 (instruction : BitVec 32) : BitVec 3 := if (decode_v7407 instruction) = 1 then (decode_v261 instruction) else (decode_v8336 instruction)
def decode_v8338 (instruction : BitVec 32) : BitVec 3 := if (decode_v7404 instruction) = 1 then (decode_v261 instruction) else (decode_v8337 instruction)
def decode_v8339 (instruction : BitVec 32) : BitVec 3 := if (decode_v7401 instruction) = 1 then (decode_v261 instruction) else (decode_v8338 instruction)
def decode_v8340 (instruction : BitVec 32) : BitVec 3 := if (decode_v7398 instruction) = 1 then (decode_v261 instruction) else (decode_v8339 instruction)
def decode_v8341 (instruction : BitVec 32) : BitVec 3 := if (decode_v7395 instruction) = 1 then (decode_v261 instruction) else (decode_v8340 instruction)
def decode_v8342 (instruction : BitVec 32) : BitVec 3 := if (decode_v7391 instruction) = 1 then (decode_v261 instruction) else (decode_v8341 instruction)
def decode_v8343 (instruction : BitVec 32) : BitVec 3 := if (decode_v7387 instruction) = 1 then (decode_v261 instruction) else (decode_v8342 instruction)
def decode_v8344 (instruction : BitVec 32) : BitVec 3 := if (decode_v7383 instruction) = 1 then (decode_v261 instruction) else (decode_v8343 instruction)
def decode_v8345 (instruction : BitVec 32) : BitVec 3 := if (decode_v7379 instruction) = 1 then (decode_v261 instruction) else (decode_v8344 instruction)
def decode_v8346 (instruction : BitVec 32) : BitVec 3 := if (decode_v7375 instruction) = 1 then (decode_v261 instruction) else (decode_v8345 instruction)
def decode_v8347 (instruction : BitVec 32) : BitVec 3 := if (decode_v7371 instruction) = 1 then (decode_v261 instruction) else (decode_v8346 instruction)
def decode_v8348 (instruction : BitVec 32) : BitVec 3 := if (decode_v7367 instruction) = 1 then (decode_v261 instruction) else (decode_v8347 instruction)
def decode_v8349 (instruction : BitVec 32) : BitVec 3 := if (decode_v7363 instruction) = 1 then (decode_v261 instruction) else (decode_v8348 instruction)
def decode_v8350 (instruction : BitVec 32) : BitVec 3 := if (decode_v7359 instruction) = 1 then (decode_v261 instruction) else (decode_v8349 instruction)
def decode_v8351 (instruction : BitVec 32) : BitVec 3 := if (decode_v7355 instruction) = 1 then (decode_v261 instruction) else (decode_v8350 instruction)
def decode_v8352 (instruction : BitVec 32) : BitVec 3 := if (decode_v7351 instruction) = 1 then (decode_v261 instruction) else (decode_v8351 instruction)
def decode_v8353 (instruction : BitVec 32) : BitVec 3 := if (decode_v7347 instruction) = 1 then (decode_v261 instruction) else (decode_v8352 instruction)
def decode_v8354 (instruction : BitVec 32) : BitVec 3 := if (decode_v7343 instruction) = 1 then (decode_v261 instruction) else (decode_v8353 instruction)
def decode_v8355 (instruction : BitVec 32) : BitVec 3 := if (decode_v7339 instruction) = 1 then (decode_v261 instruction) else (decode_v8354 instruction)
def decode_v8356 (instruction : BitVec 32) : BitVec 3 := if (decode_v7335 instruction) = 1 then (decode_v261 instruction) else (decode_v8355 instruction)
def decode_v8357 (instruction : BitVec 32) : BitVec 3 := if (decode_v7331 instruction) = 1 then (decode_v261 instruction) else (decode_v8356 instruction)
def decode_v8358 (instruction : BitVec 32) : BitVec 3 := if (decode_v7327 instruction) = 1 then (decode_v261 instruction) else (decode_v8357 instruction)
def decode_v8359 (instruction : BitVec 32) : BitVec 3 := if (decode_v7323 instruction) = 1 then (decode_v261 instruction) else (decode_v8358 instruction)
def decode_v8360 (instruction : BitVec 32) : BitVec 3 := if (decode_v7319 instruction) = 1 then (decode_v261 instruction) else (decode_v8359 instruction)
def decode_v8361 (instruction : BitVec 32) : BitVec 3 := if (decode_v7315 instruction) = 1 then (decode_v261 instruction) else (decode_v8360 instruction)
def decode_v8362 (instruction : BitVec 32) : BitVec 3 := if (decode_v7311 instruction) = 1 then (decode_v261 instruction) else (decode_v8361 instruction)
def decode_v8363 (instruction : BitVec 32) : BitVec 3 := if (decode_v7307 instruction) = 1 then (decode_v261 instruction) else (decode_v8362 instruction)
def decode_v8364 (instruction : BitVec 32) : BitVec 3 := if (decode_v7303 instruction) = 1 then (decode_v261 instruction) else (decode_v8363 instruction)
def decode_v8365 (instruction : BitVec 32) : BitVec 3 := (decode_v8364 instruction)
def decode_v8366 (instruction : BitVec 32) : BitVec 3 := (decode_v8365 instruction)
def decode_v8369 (instruction : BitVec 32) : BitVec 32 := BitVec.ofNat 32 270532723
def decode_v8370 (instruction : BitVec 32) : BitVec 1 := if (decode_v8369 instruction) = (decode_v7300 instruction) then 1 else 0
def decode_v8371 (instruction : BitVec 32) : BitVec 1 := if (decode_v8370 instruction) = 1 then (decode_v4 instruction) else (decode_v512 instruction)
def decode_v8372 (instruction : BitVec 32) : BitVec 1 := if (decode_v7470 instruction) = 1 then (decode_v4 instruction) else (decode_v8371 instruction)
def decode_v8373 (instruction : BitVec 32) : BitVec 1 := if (decode_v7468 instruction) = 1 then (decode_v4 instruction) else (decode_v8372 instruction)
def decode_v8374 (instruction : BitVec 32) : BitVec 1 := if (decode_v7466 instruction) = 1 then (decode_v4 instruction) else (decode_v8373 instruction)
def decode_v8375 (instruction : BitVec 32) : BitVec 1 := if (decode_v7464 instruction) = 1 then (decode_v4 instruction) else (decode_v8374 instruction)
def decode_v8376 (instruction : BitVec 32) : BitVec 1 := if (decode_v7460 instruction) = 1 then (decode_v4 instruction) else (decode_v8375 instruction)
def decode_v8377 (instruction : BitVec 32) : BitVec 1 := if (decode_v7456 instruction) = 1 then (decode_v4 instruction) else (decode_v8376 instruction)
def decode_v8378 (instruction : BitVec 32) : BitVec 1 := if (decode_v7452 instruction) = 1 then (decode_v4 instruction) else (decode_v8377 instruction)
def decode_v8379 (instruction : BitVec 32) : BitVec 1 := if (decode_v7448 instruction) = 1 then (decode_v4 instruction) else (decode_v8378 instruction)
def decode_v8380 (instruction : BitVec 32) : BitVec 1 := if (decode_v7444 instruction) = 1 then (decode_v4 instruction) else (decode_v8379 instruction)
def decode_v8381 (instruction : BitVec 32) : BitVec 1 := if (decode_v7440 instruction) = 1 then (decode_v4 instruction) else (decode_v8380 instruction)
def decode_v8382 (instruction : BitVec 32) : BitVec 1 := if (decode_v7438 instruction) = 1 then (decode_v4 instruction) else (decode_v8381 instruction)
def decode_v8383 (instruction : BitVec 32) : BitVec 1 := if (decode_v7434 instruction) = 1 then (decode_v4 instruction) else (decode_v8382 instruction)
def decode_v8384 (instruction : BitVec 32) : BitVec 1 := if (decode_v7431 instruction) = 1 then (decode_v4 instruction) else (decode_v8383 instruction)
def decode_v8385 (instruction : BitVec 32) : BitVec 1 := if (decode_v7428 instruction) = 1 then (decode_v4 instruction) else (decode_v8384 instruction)
def decode_v8386 (instruction : BitVec 32) : BitVec 1 := if (decode_v7425 instruction) = 1 then (decode_v4 instruction) else (decode_v8385 instruction)
def decode_v8387 (instruction : BitVec 32) : BitVec 1 := if (decode_v7422 instruction) = 1 then (decode_v4 instruction) else (decode_v8386 instruction)
def decode_v8388 (instruction : BitVec 32) : BitVec 1 := if (decode_v7419 instruction) = 1 then (decode_v4 instruction) else (decode_v8387 instruction)
def decode_v8389 (instruction : BitVec 32) : BitVec 1 := if (decode_v7416 instruction) = 1 then (decode_v4 instruction) else (decode_v8388 instruction)
def decode_v8390 (instruction : BitVec 32) : BitVec 1 := if (decode_v7413 instruction) = 1 then (decode_v4 instruction) else (decode_v8389 instruction)
def decode_v8391 (instruction : BitVec 32) : BitVec 1 := if (decode_v7410 instruction) = 1 then (decode_v4 instruction) else (decode_v8390 instruction)
def decode_v8392 (instruction : BitVec 32) : BitVec 1 := if (decode_v7407 instruction) = 1 then (decode_v4 instruction) else (decode_v8391 instruction)
def decode_v8393 (instruction : BitVec 32) : BitVec 1 := if (decode_v7404 instruction) = 1 then (decode_v4 instruction) else (decode_v8392 instruction)
def decode_v8394 (instruction : BitVec 32) : BitVec 1 := if (decode_v7401 instruction) = 1 then (decode_v4 instruction) else (decode_v8393 instruction)
def decode_v8395 (instruction : BitVec 32) : BitVec 1 := if (decode_v7398 instruction) = 1 then (decode_v4 instruction) else (decode_v8394 instruction)
def decode_v8396 (instruction : BitVec 32) : BitVec 1 := if (decode_v7395 instruction) = 1 then (decode_v4 instruction) else (decode_v8395 instruction)
def decode_v8397 (instruction : BitVec 32) : BitVec 1 := if (decode_v7391 instruction) = 1 then (decode_v4 instruction) else (decode_v8396 instruction)
def decode_v8398 (instruction : BitVec 32) : BitVec 1 := if (decode_v7387 instruction) = 1 then (decode_v4 instruction) else (decode_v8397 instruction)
def decode_v8399 (instruction : BitVec 32) : BitVec 1 := if (decode_v7383 instruction) = 1 then (decode_v4 instruction) else (decode_v8398 instruction)
def decode_v8400 (instruction : BitVec 32) : BitVec 1 := if (decode_v7379 instruction) = 1 then (decode_v4 instruction) else (decode_v8399 instruction)
def decode_v8401 (instruction : BitVec 32) : BitVec 1 := if (decode_v7375 instruction) = 1 then (decode_v4 instruction) else (decode_v8400 instruction)
def decode_v8402 (instruction : BitVec 32) : BitVec 1 := if (decode_v7371 instruction) = 1 then (decode_v4 instruction) else (decode_v8401 instruction)
def decode_v8403 (instruction : BitVec 32) : BitVec 1 := if (decode_v7367 instruction) = 1 then (decode_v4 instruction) else (decode_v8402 instruction)
def decode_v8404 (instruction : BitVec 32) : BitVec 1 := if (decode_v7363 instruction) = 1 then (decode_v4 instruction) else (decode_v8403 instruction)
def decode_v8405 (instruction : BitVec 32) : BitVec 1 := if (decode_v7359 instruction) = 1 then (decode_v4 instruction) else (decode_v8404 instruction)
def decode_v8406 (instruction : BitVec 32) : BitVec 1 := if (decode_v7355 instruction) = 1 then (decode_v4 instruction) else (decode_v8405 instruction)
def decode_v8407 (instruction : BitVec 32) : BitVec 1 := if (decode_v7351 instruction) = 1 then (decode_v4 instruction) else (decode_v8406 instruction)
def decode_v8408 (instruction : BitVec 32) : BitVec 1 := if (decode_v7347 instruction) = 1 then (decode_v4 instruction) else (decode_v8407 instruction)
def decode_v8409 (instruction : BitVec 32) : BitVec 1 := if (decode_v7343 instruction) = 1 then (decode_v4 instruction) else (decode_v8408 instruction)
def decode_v8410 (instruction : BitVec 32) : BitVec 1 := if (decode_v7339 instruction) = 1 then (decode_v4 instruction) else (decode_v8409 instruction)
def decode_v8411 (instruction : BitVec 32) : BitVec 1 := if (decode_v7335 instruction) = 1 then (decode_v4 instruction) else (decode_v8410 instruction)
def decode_v8412 (instruction : BitVec 32) : BitVec 1 := if (decode_v7331 instruction) = 1 then (decode_v4 instruction) else (decode_v8411 instruction)
def decode_v8413 (instruction : BitVec 32) : BitVec 1 := if (decode_v7327 instruction) = 1 then (decode_v4 instruction) else (decode_v8412 instruction)
def decode_v8414 (instruction : BitVec 32) : BitVec 1 := if (decode_v7323 instruction) = 1 then (decode_v4 instruction) else (decode_v8413 instruction)
def decode_v8415 (instruction : BitVec 32) : BitVec 1 := if (decode_v7319 instruction) = 1 then (decode_v4 instruction) else (decode_v8414 instruction)
def decode_v8416 (instruction : BitVec 32) : BitVec 1 := if (decode_v7315 instruction) = 1 then (decode_v4 instruction) else (decode_v8415 instruction)
def decode_v8417 (instruction : BitVec 32) : BitVec 1 := if (decode_v7311 instruction) = 1 then (decode_v4 instruction) else (decode_v8416 instruction)
def decode_v8418 (instruction : BitVec 32) : BitVec 1 := if (decode_v7307 instruction) = 1 then (decode_v4 instruction) else (decode_v8417 instruction)
def decode_v8419 (instruction : BitVec 32) : BitVec 1 := if (decode_v7303 instruction) = 1 then (decode_v4 instruction) else (decode_v8418 instruction)
def decode_v8420 (instruction : BitVec 32) : BitVec 1 := (decode_v8419 instruction)
def decode_v8421 (instruction : BitVec 32) : BitVec 1 := (decode_v8420 instruction)
abbrev decode_store := decode_v8193
theorem decode_store_eq (s : State) (i : Inputs) :
    v8193 s i = decode_store (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl
abbrev decode_load := decode_v8213
theorem decode_load_eq (s : State) (i : Inputs) :
    v8213 s i = decode_load (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl
abbrev decode_write_select := decode_v8265
theorem decode_write_select_eq (s : State) (i : Inputs) :
    v8265 s i = decode_write_select (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl
abbrev decode_write_enable := decode_v8313
theorem decode_write_enable_eq (s : State) (i : Inputs) :
    v8313 s i = decode_write_enable (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl
abbrev decode_csr_command := decode_v8366
theorem decode_csr_command_eq (s : State) (i : Inputs) :
    v8366 s i = decode_csr_command (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl
abbrev decode_illegal := decode_v8421
theorem decode_illegal_eq (s : State) (i : Inputs) :
    v8421 s i = decode_illegal (s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst) := by rfl

def decode_store_width (instruction : BitVec 32) : BitVec 6 :=
  if decode_store instruction = 1 then 32 else
  if decode_store instruction = 2 then 16 else
  if decode_store instruction = 3 then 8 else 0
def decode_store_valid (instruction : BitVec 32) : BitVec 1 :=
  if 0 < (decode_store_width instruction).toNat then 1 else 0

structure ControlValues (s : State) : Prop where
  store : s.g4.r129_ndut_5Fdpath_5Fst_5Ftype = decode_store (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  load : s.g4.r130_ndut_5Fdpath_5Fld_5Ftype = decode_load (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  write_select : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = decode_write_select (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  write_enable : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = decode_write_enable (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  csr_command : s.g4.r133_ndut_5Fdpath_5Fcsr_5Fcmd = decode_csr_command (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  illegal : s.g4.r134_ndut_5Fdpath_5Fillegal = decode_illegal (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  store_width : s.g4.r158_ndut_5Fdpath_5Fmem_5Fwrite_5FmemWidth_5FREG = decode_store_width (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
  store_valid : s.g4.r157_ndut_5Fdpath_5Fmem_5Fwrite_5Fvalid_5FREG = decode_store_valid (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)

def ControlAligned (s : State) : Prop :=
  s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 → ControlValues s

theorem control_alignment_reset (s : State) (i : Inputs)
    (reset : i.nreset = 1) : ControlAligned (step s i) := by
  intro valid
  change v8567 s i = 0 at valid
  simp [v8567, v1, v0, reset, v512] at valid

theorem control_values_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0) :
    ControlValues (step s i) := by
  have stall := no_stall_after_reset s i reset
  have advance : v7777 s i = 1 := by
    simp [v7777, v7775, v7776, stall, trap, v4]
  have keep : v7774 s i = 0 := by
    simp [v7774, v7773, v7772, stall, trap, v1, v0, reset, v4]
  have instruction : v7780 s i = s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst := by
    simp [v7780, v7779, v7778, keep, advance, v1, v0, reset]
  constructor
  · change v8195 s i = decode_store (v7780 s i)
    simp [v8195, v8194, keep, advance, instruction, decode_store_eq]
  · change v8215 s i = decode_load (v7780 s i)
    simp [v8215, v8214, keep, advance, instruction, decode_load_eq]
  · change v8267 s i = decode_write_select (v7780 s i)
    simp [v8267, v8266, keep, advance, instruction, decode_write_select_eq]
  · change v8315 s i = decode_write_enable (v7780 s i)
    simp [v8315, v8314, keep, advance, instruction, decode_write_enable_eq]
  · change v8368 s i = decode_csr_command (v7780 s i)
    simp [v8368, v8367, keep, advance, instruction, decode_csr_command_eq]
  · change v8423 s i = decode_illegal (v7780 s i)
    simp [v8423, v8422, keep, advance, instruction, decode_illegal_eq]
  · change v8622 s i = decode_store_width (v7780 s i)
    simp [v8622, v8612, v8611, v8610, v8608, v8606, v8604, v8603, v8605, v8607, v8609, v42, v38, v155, v1941, v1, v0, stall, reset, instruction, decode_store_eq,
      decode_store_width, eq_comm]
  · change v8620 s i = decode_store_valid (v7780 s i)
    simp [v8620, v8619, v8618, v8612, v8611, v8610, v8608, v8606, v8604, v8603, v8605, v8607, v8609, v42, v38, v155, v1941, v1, v0, stall, reset, instruction, decode_store_eq,
      decode_store_valid, decode_store_width, eq_comm]

-- No instruction-set restriction: this holds even for arbitrary instruction words.
theorem control_alignment_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    ControlAligned (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases hn : cycles ≤ n
    · intro _
      exact control_values_step _ _ (reset.2.2 n hn)
        (environment_no_trap _ _ (reset.2.2 n hn) (env n))
    · exact control_alignment_reset _ _ (reset.2.1 n (by omega))

theorem control_values_at_commit (s : State) (i : Inputs)
    (aligned : ControlAligned s) (reset : i.nreset = 0)
    (commit : v964 s i = 1) : ControlValues s := by
  by_cases hz : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1.toNat = 0
  · exact aligned (BitVec.eq_of_toNat_eq hz)
  · have ho : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      have := s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1.isLt
      change s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1.toNat = 1
      omega
    have stall := no_stall_after_reset s i reset
    simp [v964, v963, v962, v961, v960, v959, ho, stall, v1, v0, reset, v4] at commit
#print axioms control_alignment_reachable
#print axioms control_values_at_commit
end RiscvMiniProofs
