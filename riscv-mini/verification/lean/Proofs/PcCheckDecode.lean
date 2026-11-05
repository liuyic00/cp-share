import Proofs.ExecuteTransfer
namespace RiscvMiniProofs
open nCoreSoc
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def check_v7298 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 55
def check_v7299 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := instruction
def check_v7300 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := (check_v7299 instruction rs1 rs2)
def check_v7301 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def check_v7302 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7301 instruction rs1 rs2))
def check_v7303 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7298 instruction rs1 rs2) = (check_v7302 instruction rs1 rs2) then 1 else 0
def check_v32 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := BitVec.ofNat 2 0
def check_v7304 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 23
def check_v7305 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def check_v7306 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7305 instruction rs1 rs2))
def check_v7307 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7304 instruction rs1 rs2) = (check_v7306 instruction rs1 rs2) then 1 else 0
def check_v7308 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 111
def check_v7309 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def check_v7310 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7309 instruction rs1 rs2))
def check_v7311 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7308 instruction rs1 rs2) = (check_v7310 instruction rs1 rs2) then 1 else 0
def check_v42 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := BitVec.ofNat 2 1
def check_v7312 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 103
def check_v7313 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7314 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7313 instruction rs1 rs2))
def check_v7315 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7312 instruction rs1 rs2) = (check_v7314 instruction rs1 rs2) then 1 else 0
def check_v7316 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 99
def check_v7317 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7318 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7317 instruction rs1 rs2))
def check_v7319 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7316 instruction rs1 rs2) = (check_v7318 instruction rs1 rs2) then 1 else 0
def check_v7320 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4195
def check_v7321 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7322 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7321 instruction rs1 rs2))
def check_v7323 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7320 instruction rs1 rs2) = (check_v7322 instruction rs1 rs2) then 1 else 0
def check_v7324 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16483
def check_v7325 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7326 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7325 instruction rs1 rs2))
def check_v7327 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7324 instruction rs1 rs2) = (check_v7326 instruction rs1 rs2) then 1 else 0
def check_v7328 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20579
def check_v7329 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7330 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7329 instruction rs1 rs2))
def check_v7331 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7328 instruction rs1 rs2) = (check_v7330 instruction rs1 rs2) then 1 else 0
def check_v7332 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24675
def check_v7333 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7334 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7333 instruction rs1 rs2))
def check_v7335 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7332 instruction rs1 rs2) = (check_v7334 instruction rs1 rs2) then 1 else 0
def check_v7336 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28771
def check_v7337 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7338 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7337 instruction rs1 rs2))
def check_v7339 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7336 instruction rs1 rs2) = (check_v7338 instruction rs1 rs2) then 1 else 0
def check_v7340 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 3
def check_v7341 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7342 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7341 instruction rs1 rs2))
def check_v7343 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7340 instruction rs1 rs2) = (check_v7342 instruction rs1 rs2) then 1 else 0
def check_v38 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := BitVec.ofNat 2 2
def check_v7344 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4099
def check_v7345 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7346 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7345 instruction rs1 rs2))
def check_v7347 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7344 instruction rs1 rs2) = (check_v7346 instruction rs1 rs2) then 1 else 0
def check_v7348 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8195
def check_v7349 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7350 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7349 instruction rs1 rs2))
def check_v7351 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7348 instruction rs1 rs2) = (check_v7350 instruction rs1 rs2) then 1 else 0
def check_v7352 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16387
def check_v7353 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7354 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7353 instruction rs1 rs2))
def check_v7355 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7352 instruction rs1 rs2) = (check_v7354 instruction rs1 rs2) then 1 else 0
def check_v7356 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20483
def check_v7357 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7358 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7357 instruction rs1 rs2))
def check_v7359 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7356 instruction rs1 rs2) = (check_v7358 instruction rs1 rs2) then 1 else 0
def check_v7360 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 35
def check_v7361 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7362 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7361 instruction rs1 rs2))
def check_v7363 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7360 instruction rs1 rs2) = (check_v7362 instruction rs1 rs2) then 1 else 0
def check_v7364 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4131
def check_v7365 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7366 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7365 instruction rs1 rs2))
def check_v7367 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7364 instruction rs1 rs2) = (check_v7366 instruction rs1 rs2) then 1 else 0
def check_v7368 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8227
def check_v7369 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7370 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7369 instruction rs1 rs2))
def check_v7371 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7368 instruction rs1 rs2) = (check_v7370 instruction rs1 rs2) then 1 else 0
def check_v7372 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 19
def check_v7373 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7374 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7373 instruction rs1 rs2))
def check_v7375 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7372 instruction rs1 rs2) = (check_v7374 instruction rs1 rs2) then 1 else 0
def check_v7376 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8211
def check_v7377 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7378 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7377 instruction rs1 rs2))
def check_v7379 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7376 instruction rs1 rs2) = (check_v7378 instruction rs1 rs2) then 1 else 0
def check_v7380 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12307
def check_v7381 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7382 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7381 instruction rs1 rs2))
def check_v7383 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7380 instruction rs1 rs2) = (check_v7382 instruction rs1 rs2) then 1 else 0
def check_v7384 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16403
def check_v7385 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7386 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7385 instruction rs1 rs2))
def check_v7387 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7384 instruction rs1 rs2) = (check_v7386 instruction rs1 rs2) then 1 else 0
def check_v7388 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24595
def check_v7389 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7390 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7389 instruction rs1 rs2))
def check_v7391 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7388 instruction rs1 rs2) = (check_v7390 instruction rs1 rs2) then 1 else 0
def check_v7392 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28691
def check_v7393 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7394 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7393 instruction rs1 rs2))
def check_v7395 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7392 instruction rs1 rs2) = (check_v7394 instruction rs1 rs2) then 1 else 0
def check_v7396 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4115
def check_v978 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4261441663
def check_v7397 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7398 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7396 instruction rs1 rs2) = (check_v7397 instruction rs1 rs2) then 1 else 0
def check_v7399 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20499
def check_v7400 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7401 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7399 instruction rs1 rs2) = (check_v7400 instruction rs1 rs2) then 1 else 0
def check_v7402 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762323
def check_v7403 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7404 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7402 instruction rs1 rs2) = (check_v7403 instruction rs1 rs2) then 1 else 0
def check_v7405 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 51
def check_v7406 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7407 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7405 instruction rs1 rs2) = (check_v7406 instruction rs1 rs2) then 1 else 0
def check_v7408 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073741875
def check_v7409 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7410 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7408 instruction rs1 rs2) = (check_v7409 instruction rs1 rs2) then 1 else 0
def check_v7411 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4147
def check_v7412 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7413 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7411 instruction rs1 rs2) = (check_v7412 instruction rs1 rs2) then 1 else 0
def check_v7414 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8243
def check_v7415 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7416 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7414 instruction rs1 rs2) = (check_v7415 instruction rs1 rs2) then 1 else 0
def check_v7417 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12339
def check_v7418 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7419 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7417 instruction rs1 rs2) = (check_v7418 instruction rs1 rs2) then 1 else 0
def check_v7420 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16435
def check_v7421 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7422 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7420 instruction rs1 rs2) = (check_v7421 instruction rs1 rs2) then 1 else 0
def check_v7423 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20531
def check_v7424 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7425 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7423 instruction rs1 rs2) = (check_v7424 instruction rs1 rs2) then 1 else 0
def check_v7426 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762355
def check_v7427 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7428 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7426 instruction rs1 rs2) = (check_v7427 instruction rs1 rs2) then 1 else 0
def check_v7429 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24627
def check_v7430 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7431 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7429 instruction rs1 rs2) = (check_v7430 instruction rs1 rs2) then 1 else 0
def check_v7432 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28723
def check_v7433 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v978 instruction rs1 rs2))
def check_v7434 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7432 instruction rs1 rs2) = (check_v7433 instruction rs1 rs2) then 1 else 0
def check_v7435 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 15
def check_v7436 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4027580415
def check_v7437 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7436 instruction rs1 rs2))
def check_v7438 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7435 instruction rs1 rs2) = (check_v7437 instruction rs1 rs2) then 1 else 0
def check_v7439 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4111
def check_v7440 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7439 instruction rs1 rs2) = (check_v7300 instruction rs1 rs2) then 1 else 0
def check_v7441 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4211
def check_v7442 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7443 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7442 instruction rs1 rs2))
def check_v7444 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7441 instruction rs1 rs2) = (check_v7443 instruction rs1 rs2) then 1 else 0
def check_v7445 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8307
def check_v7446 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7447 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7446 instruction rs1 rs2))
def check_v7448 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7445 instruction rs1 rs2) = (check_v7447 instruction rs1 rs2) then 1 else 0
def check_v7449 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12403
def check_v7450 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7451 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7450 instruction rs1 rs2))
def check_v7452 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7449 instruction rs1 rs2) = (check_v7451 instruction rs1 rs2) then 1 else 0
def check_v7453 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20595
def check_v7454 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7455 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7454 instruction rs1 rs2))
def check_v7456 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7453 instruction rs1 rs2) = (check_v7455 instruction rs1 rs2) then 1 else 0
def check_v7457 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24691
def check_v7458 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7459 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7458 instruction rs1 rs2))
def check_v7460 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7457 instruction rs1 rs2) = (check_v7459 instruction rs1 rs2) then 1 else 0
def check_v7461 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28787
def check_v7462 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def check_v7463 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := ((check_v7300 instruction rs1 rs2) &&& (check_v7462 instruction rs1 rs2))
def check_v7464 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7461 instruction rs1 rs2) = (check_v7463 instruction rs1 rs2) then 1 else 0
def check_v7465 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 115
def check_v7466 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7465 instruction rs1 rs2) = (check_v7300 instruction rs1 rs2) then 1 else 0
def check_v7467 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1048691
def check_v7468 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7467 instruction rs1 rs2) = (check_v7300 instruction rs1 rs2) then 1 else 0
def check_v7469 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 268435571
def check_v7470 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7469 instruction rs1 rs2) = (check_v7300 instruction rs1 rs2) then 1 else 0
def check_v155 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := BitVec.ofNat 2 3
def check_v8424 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7470 instruction rs1 rs2) = 1 then (check_v155 instruction rs1 rs2) else (check_v32 instruction rs1 rs2)
def check_v8425 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7468 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8424 instruction rs1 rs2)
def check_v8426 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7466 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8425 instruction rs1 rs2)
def check_v8427 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7464 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8426 instruction rs1 rs2)
def check_v8428 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7460 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8427 instruction rs1 rs2)
def check_v8429 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7456 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8428 instruction rs1 rs2)
def check_v8430 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7452 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8429 instruction rs1 rs2)
def check_v8431 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7448 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8430 instruction rs1 rs2)
def check_v8432 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7444 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8431 instruction rs1 rs2)
def check_v8433 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7440 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8432 instruction rs1 rs2)
def check_v8434 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7438 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8433 instruction rs1 rs2)
def check_v8435 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7434 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8434 instruction rs1 rs2)
def check_v8436 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7431 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8435 instruction rs1 rs2)
def check_v8437 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7428 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8436 instruction rs1 rs2)
def check_v8438 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7425 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8437 instruction rs1 rs2)
def check_v8439 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7422 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8438 instruction rs1 rs2)
def check_v8440 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7419 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8439 instruction rs1 rs2)
def check_v8441 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7416 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8440 instruction rs1 rs2)
def check_v8442 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7413 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8441 instruction rs1 rs2)
def check_v8443 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7410 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8442 instruction rs1 rs2)
def check_v8444 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7407 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8443 instruction rs1 rs2)
def check_v8445 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7404 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8444 instruction rs1 rs2)
def check_v8446 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7401 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8445 instruction rs1 rs2)
def check_v8447 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7398 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8446 instruction rs1 rs2)
def check_v8448 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7395 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8447 instruction rs1 rs2)
def check_v8449 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7391 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8448 instruction rs1 rs2)
def check_v8450 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7387 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8449 instruction rs1 rs2)
def check_v8451 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7383 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8450 instruction rs1 rs2)
def check_v8452 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7379 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8451 instruction rs1 rs2)
def check_v8453 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7375 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8452 instruction rs1 rs2)
def check_v8454 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7371 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8453 instruction rs1 rs2)
def check_v8455 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7367 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8454 instruction rs1 rs2)
def check_v8456 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7363 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8455 instruction rs1 rs2)
def check_v8457 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7359 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8456 instruction rs1 rs2)
def check_v8458 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7355 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8457 instruction rs1 rs2)
def check_v8459 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7351 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8458 instruction rs1 rs2)
def check_v8460 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7347 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8459 instruction rs1 rs2)
def check_v8461 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7343 instruction rs1 rs2) = 1 then (check_v38 instruction rs1 rs2) else (check_v8460 instruction rs1 rs2)
def check_v8462 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7339 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8461 instruction rs1 rs2)
def check_v8463 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7335 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8462 instruction rs1 rs2)
def check_v8464 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7331 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8463 instruction rs1 rs2)
def check_v8465 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7327 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8464 instruction rs1 rs2)
def check_v8466 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7323 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8465 instruction rs1 rs2)
def check_v8467 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7319 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8466 instruction rs1 rs2)
def check_v8468 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7315 instruction rs1 rs2) = 1 then (check_v42 instruction rs1 rs2) else (check_v8467 instruction rs1 rs2)
def check_v8469 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7311 instruction rs1 rs2) = 1 then (check_v42 instruction rs1 rs2) else (check_v8468 instruction rs1 rs2)
def check_v8470 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7307 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8469 instruction rs1 rs2)
def check_v8471 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := if (check_v7303 instruction rs1 rs2) = 1 then (check_v32 instruction rs1 rs2) else (check_v8470 instruction rs1 rs2)
def check_v8472 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := (check_v8471 instruction rs1 rs2)
def check_v8473 (instruction rs1 rs2 : BitVec 32) : BitVec 2 := (check_v8472 instruction rs1 rs2)
def check_v8474 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v8473 instruction rs1 rs2) = (check_v42 instruction rs1 rs2) then 1 else 0
def check_v261 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 0
def check_v200 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 3
def check_v7521 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 6
def check_v26 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 2
def check_v716 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 5
def check_v29 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 1
def check_v22 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 4
def check_v7522 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7339 instruction rs1 rs2) = 1 then (check_v22 instruction rs1 rs2) else (check_v261 instruction rs1 rs2)
def check_v7523 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7335 instruction rs1 rs2) = 1 then (check_v29 instruction rs1 rs2) else (check_v7522 instruction rs1 rs2)
def check_v7524 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7331 instruction rs1 rs2) = 1 then (check_v716 instruction rs1 rs2) else (check_v7523 instruction rs1 rs2)
def check_v7525 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7327 instruction rs1 rs2) = 1 then (check_v26 instruction rs1 rs2) else (check_v7524 instruction rs1 rs2)
def check_v7526 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7323 instruction rs1 rs2) = 1 then (check_v7521 instruction rs1 rs2) else (check_v7525 instruction rs1 rs2)
def check_v7527 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7319 instruction rs1 rs2) = 1 then (check_v200 instruction rs1 rs2) else (check_v7526 instruction rs1 rs2)
def check_v7528 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7315 instruction rs1 rs2) = 1 then (check_v261 instruction rs1 rs2) else (check_v7527 instruction rs1 rs2)
def check_v7529 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7311 instruction rs1 rs2) = 1 then (check_v261 instruction rs1 rs2) else (check_v7528 instruction rs1 rs2)
def check_v7530 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7307 instruction rs1 rs2) = 1 then (check_v261 instruction rs1 rs2) else (check_v7529 instruction rs1 rs2)
def check_v7531 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := if (check_v7303 instruction rs1 rs2) = 1 then (check_v261 instruction rs1 rs2) else (check_v7530 instruction rs1 rs2)
def check_v7532 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := (check_v7531 instruction rs1 rs2)
def check_v7533 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := (check_v7532 instruction rs1 rs2)
def check_v7534 (instruction rs1 rs2 : BitVec 32) : BitVec 3 := (check_v7533 instruction rs1 rs2)
def check_v7535 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v200 instruction rs1 rs2) then 1 else 0
def check_v4 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def check_v7630 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := rs1
def check_v7631 (instruction rs1 rs2 : BitVec 32) : BitVec 33 := ((check_v4 instruction rs1 rs2) ++ (check_v7630 instruction rs1 rs2))
def check_v7726 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := rs2
def check_v7727 (instruction rs1 rs2 : BitVec 32) : BitVec 33 := ((check_v4 instruction rs1 rs2) ++ (check_v7726 instruction rs1 rs2))
def check_v7728 (instruction rs1 rs2 : BitVec 32) : BitVec 33 := ((check_v7631 instruction rs1 rs2) - (check_v7727 instruction rs1 rs2))
def check_v7729 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (check_v7728 instruction rs1 rs2)
def check_v3 (instruction rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 0
def check_v7730 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7729 instruction rs1 rs2) ≠ (check_v3 instruction rs1 rs2) then 1 else 0
def check_v7731 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7730 instruction rs1 rs2) = (check_v4 instruction rs1 rs2) then 1 else 0
def check_v7732 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7535 instruction rs1 rs2) &&& (check_v7731 instruction rs1 rs2))
def check_v7733 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v7521 instruction rs1 rs2) then 1 else 0
def check_v7734 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7733 instruction rs1 rs2) &&& (check_v7730 instruction rs1 rs2))
def check_v7735 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7732 instruction rs1 rs2) ||| (check_v7734 instruction rs1 rs2))
def check_v7736 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v26 instruction rs1 rs2) then 1 else 0
def check_v7737 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7630 instruction rs1 rs2)
def check_v7738 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7726 instruction rs1 rs2)
def check_v7739 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7737 instruction rs1 rs2) = (check_v7738 instruction rs1 rs2) then 1 else 0
def check_v7740 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7729 instruction rs1 rs2)
def check_v7741 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7630 instruction rs1 rs2)
def check_v7742 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7739 instruction rs1 rs2) = 1 then (check_v7740 instruction rs1 rs2) else (check_v7741 instruction rs1 rs2)
def check_v7743 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7736 instruction rs1 rs2) &&& (check_v7742 instruction rs1 rs2))
def check_v7744 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7735 instruction rs1 rs2) ||| (check_v7743 instruction rs1 rs2))
def check_v7745 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v716 instruction rs1 rs2) then 1 else 0
def check_v7746 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7742 instruction rs1 rs2) = (check_v4 instruction rs1 rs2) then 1 else 0
def check_v7747 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7745 instruction rs1 rs2) &&& (check_v7746 instruction rs1 rs2))
def check_v7748 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7744 instruction rs1 rs2) ||| (check_v7747 instruction rs1 rs2))
def check_v7749 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v29 instruction rs1 rs2) then 1 else 0
def check_v7750 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7729 instruction rs1 rs2)
def check_v7751 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (check_v7726 instruction rs1 rs2)
def check_v7752 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7739 instruction rs1 rs2) = 1 then (check_v7750 instruction rs1 rs2) else (check_v7751 instruction rs1 rs2)
def check_v7753 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7749 instruction rs1 rs2) &&& (check_v7752 instruction rs1 rs2))
def check_v7754 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7748 instruction rs1 rs2) ||| (check_v7753 instruction rs1 rs2))
def check_v7755 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7534 instruction rs1 rs2) = (check_v22 instruction rs1 rs2) then 1 else 0
def check_v7756 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := if (check_v7752 instruction rs1 rs2) = (check_v4 instruction rs1 rs2) then 1 else 0
def check_v7757 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7755 instruction rs1 rs2) &&& (check_v7756 instruction rs1 rs2))
def check_v7758 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v7754 instruction rs1 rs2) ||| (check_v7757 instruction rs1 rs2))
def check_v7759 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := (check_v7758 instruction rs1 rs2)
def check_v8475 (instruction rs1 rs2 : BitVec 32) : BitVec 1 := ((check_v8474 instruction rs1 rs2) ||| (check_v7759 instruction rs1 rs2))
def decodedPcCheck (instruction rs1 rs2 : BitVec 32) : BitVec 1 := check_v8475 instruction rs1 rs2
theorem decoded_pc_check_eq (s : State) (i : Inputs) :
    v8475 s i = decodedPcCheck s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst (v7629 s i) (v7725 s i) := by rfl
theorem decoded_pc_check_nop : decodedPcCheck 19 0 0 = 0 := by
  simp only [decodedPcCheck, check_v8475, check_v7759, check_v7758, check_v7757, check_v7756, check_v7755, check_v7754, check_v7753, check_v7752, check_v7751, check_v7750, check_v7749, check_v7748, check_v7747, check_v7746, check_v7745, check_v7744, check_v7743, check_v7742, check_v7741, check_v7740, check_v7739, check_v7738, check_v7737, check_v7736, check_v7735, check_v7734, check_v7733, check_v7732, check_v7731, check_v7730, check_v3, check_v7729, check_v7728, check_v7727, check_v7726, check_v7631, check_v7630, check_v4, check_v7535, check_v7534, check_v7533, check_v7532, check_v7531, check_v7530, check_v7529, check_v7528, check_v7527, check_v7526, check_v7525, check_v7524, check_v7523, check_v7522, check_v22, check_v29, check_v716, check_v26, check_v7521, check_v200, check_v261, check_v8474, check_v8473, check_v8472, check_v8471, check_v8470, check_v8469, check_v8468, check_v8467, check_v8466, check_v8465, check_v8464, check_v8463, check_v8462, check_v8461, check_v8460, check_v8459, check_v8458, check_v8457, check_v8456, check_v8455, check_v8454, check_v8453, check_v8452, check_v8451, check_v8450, check_v8449, check_v8448, check_v8447, check_v8446, check_v8445, check_v8444, check_v8443, check_v8442, check_v8441, check_v8440, check_v8439, check_v8438, check_v8437, check_v8436, check_v8435, check_v8434, check_v8433, check_v8432, check_v8431, check_v8430, check_v8429, check_v8428, check_v8427, check_v8426, check_v8425, check_v8424, check_v155, check_v7470, check_v7469, check_v7468, check_v7467, check_v7466, check_v7465, check_v7464, check_v7463, check_v7462, check_v7461, check_v7460, check_v7459, check_v7458, check_v7457, check_v7456, check_v7455, check_v7454, check_v7453, check_v7452, check_v7451, check_v7450, check_v7449, check_v7448, check_v7447, check_v7446, check_v7445, check_v7444, check_v7443, check_v7442, check_v7441, check_v7440, check_v7439, check_v7438, check_v7437, check_v7436, check_v7435, check_v7434, check_v7433, check_v7432, check_v7431, check_v7430, check_v7429, check_v7428, check_v7427, check_v7426, check_v7425, check_v7424, check_v7423, check_v7422, check_v7421, check_v7420, check_v7419, check_v7418, check_v7417, check_v7416, check_v7415, check_v7414, check_v7413, check_v7412, check_v7411, check_v7410, check_v7409, check_v7408, check_v7407, check_v7406, check_v7405, check_v7404, check_v7403, check_v7402, check_v7401, check_v7400, check_v7399, check_v7398, check_v7397, check_v978, check_v7396, check_v7395, check_v7394, check_v7393, check_v7392, check_v7391, check_v7390, check_v7389, check_v7388, check_v7387, check_v7386, check_v7385, check_v7384, check_v7383, check_v7382, check_v7381, check_v7380, check_v7379, check_v7378, check_v7377, check_v7376, check_v7375, check_v7374, check_v7373, check_v7372, check_v7371, check_v7370, check_v7369, check_v7368, check_v7367, check_v7366, check_v7365, check_v7364, check_v7363, check_v7362, check_v7361, check_v7360, check_v7359, check_v7358, check_v7357, check_v7356, check_v7355, check_v7354, check_v7353, check_v7352, check_v7351, check_v7350, check_v7349, check_v7348, check_v7347, check_v7346, check_v7345, check_v7344, check_v38, check_v7343, check_v7342, check_v7341, check_v7340, check_v7339, check_v7338, check_v7337, check_v7336, check_v7335, check_v7334, check_v7333, check_v7332, check_v7331, check_v7330, check_v7329, check_v7328, check_v7327, check_v7326, check_v7325, check_v7324, check_v7323, check_v7322, check_v7321, check_v7320, check_v7319, check_v7318, check_v7317, check_v7316, check_v7315, check_v7314, check_v7313, check_v7312, check_v42, check_v7311, check_v7310, check_v7309, check_v7308, check_v7307, check_v7306, check_v7305, check_v7304, check_v32, check_v7303, check_v7302, check_v7301, check_v7300, check_v7299, check_v7298]
  decide
#print axioms decoded_pc_check_eq
#print axioms decoded_pc_check_nop
end RiscvMiniProofs
