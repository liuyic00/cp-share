import Proofs.ExecuteTransfer
namespace RiscvMiniProofs
open nCoreSoc
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def exec_v7298 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 55
def exec_v7299 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := instruction
def exec_v7300 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := (exec_v7299 instruction pc rs1 rs2)
def exec_v7301 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def exec_v7302 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7301 instruction pc rs1 rs2))
def exec_v7303 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7298 instruction pc rs1 rs2) = (exec_v7302 instruction pc rs1 rs2) then 1 else 0
def exec_v7784 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 11
def exec_v7304 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 23
def exec_v7305 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def exec_v7306 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7305 instruction pc rs1 rs2))
def exec_v7307 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7304 instruction pc rs1 rs2) = (exec_v7306 instruction pc rs1 rs2) then 1 else 0
def exec_v725 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def exec_v7308 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 111
def exec_v7309 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def exec_v7310 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7309 instruction pc rs1 rs2))
def exec_v7311 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7308 instruction pc rs1 rs2) = (exec_v7310 instruction pc rs1 rs2) then 1 else 0
def exec_v7312 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 103
def exec_v7313 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7314 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7313 instruction pc rs1 rs2))
def exec_v7315 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7312 instruction pc rs1 rs2) = (exec_v7314 instruction pc rs1 rs2) then 1 else 0
def exec_v7316 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 99
def exec_v7317 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7318 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7317 instruction pc rs1 rs2))
def exec_v7319 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7316 instruction pc rs1 rs2) = (exec_v7318 instruction pc rs1 rs2) then 1 else 0
def exec_v7320 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4195
def exec_v7321 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7322 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7321 instruction pc rs1 rs2))
def exec_v7323 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7320 instruction pc rs1 rs2) = (exec_v7322 instruction pc rs1 rs2) then 1 else 0
def exec_v7324 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16483
def exec_v7325 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7326 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7325 instruction pc rs1 rs2))
def exec_v7327 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7324 instruction pc rs1 rs2) = (exec_v7326 instruction pc rs1 rs2) then 1 else 0
def exec_v7328 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20579
def exec_v7329 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7330 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7329 instruction pc rs1 rs2))
def exec_v7331 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7328 instruction pc rs1 rs2) = (exec_v7330 instruction pc rs1 rs2) then 1 else 0
def exec_v7332 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24675
def exec_v7333 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7334 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7333 instruction pc rs1 rs2))
def exec_v7335 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7332 instruction pc rs1 rs2) = (exec_v7334 instruction pc rs1 rs2) then 1 else 0
def exec_v7336 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28771
def exec_v7337 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7338 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7337 instruction pc rs1 rs2))
def exec_v7339 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7336 instruction pc rs1 rs2) = (exec_v7338 instruction pc rs1 rs2) then 1 else 0
def exec_v7340 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 3
def exec_v7341 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7342 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7341 instruction pc rs1 rs2))
def exec_v7343 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7340 instruction pc rs1 rs2) = (exec_v7342 instruction pc rs1 rs2) then 1 else 0
def exec_v7344 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4099
def exec_v7345 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7346 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7345 instruction pc rs1 rs2))
def exec_v7347 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7344 instruction pc rs1 rs2) = (exec_v7346 instruction pc rs1 rs2) then 1 else 0
def exec_v7348 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8195
def exec_v7349 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7350 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7349 instruction pc rs1 rs2))
def exec_v7351 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7348 instruction pc rs1 rs2) = (exec_v7350 instruction pc rs1 rs2) then 1 else 0
def exec_v7352 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16387
def exec_v7353 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7354 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7353 instruction pc rs1 rs2))
def exec_v7355 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7352 instruction pc rs1 rs2) = (exec_v7354 instruction pc rs1 rs2) then 1 else 0
def exec_v7356 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20483
def exec_v7357 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7358 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7357 instruction pc rs1 rs2))
def exec_v7359 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7356 instruction pc rs1 rs2) = (exec_v7358 instruction pc rs1 rs2) then 1 else 0
def exec_v7360 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 35
def exec_v7361 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7362 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7361 instruction pc rs1 rs2))
def exec_v7363 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7360 instruction pc rs1 rs2) = (exec_v7362 instruction pc rs1 rs2) then 1 else 0
def exec_v7364 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4131
def exec_v7365 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7366 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7365 instruction pc rs1 rs2))
def exec_v7367 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7364 instruction pc rs1 rs2) = (exec_v7366 instruction pc rs1 rs2) then 1 else 0
def exec_v7368 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8227
def exec_v7369 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7370 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7369 instruction pc rs1 rs2))
def exec_v7371 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7368 instruction pc rs1 rs2) = (exec_v7370 instruction pc rs1 rs2) then 1 else 0
def exec_v7372 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 19
def exec_v7373 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7374 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7373 instruction pc rs1 rs2))
def exec_v7375 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7372 instruction pc rs1 rs2) = (exec_v7374 instruction pc rs1 rs2) then 1 else 0
def exec_v7376 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8211
def exec_v7377 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7378 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7377 instruction pc rs1 rs2))
def exec_v7379 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7376 instruction pc rs1 rs2) = (exec_v7378 instruction pc rs1 rs2) then 1 else 0
def exec_v7785 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 5
def exec_v7380 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12307
def exec_v7381 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7382 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7381 instruction pc rs1 rs2))
def exec_v7383 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7380 instruction pc rs1 rs2) = (exec_v7382 instruction pc rs1 rs2) then 1 else 0
def exec_v7786 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 7
def exec_v7384 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16403
def exec_v7385 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7386 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7385 instruction pc rs1 rs2))
def exec_v7387 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7384 instruction pc rs1 rs2) = (exec_v7386 instruction pc rs1 rs2) then 1 else 0
def exec_v7787 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 4
def exec_v7388 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24595
def exec_v7389 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7390 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7389 instruction pc rs1 rs2))
def exec_v7391 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7388 instruction pc rs1 rs2) = (exec_v7390 instruction pc rs1 rs2) then 1 else 0
def exec_v7788 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 3
def exec_v7392 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28691
def exec_v7393 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7394 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7393 instruction pc rs1 rs2))
def exec_v7395 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7392 instruction pc rs1 rs2) = (exec_v7394 instruction pc rs1 rs2) then 1 else 0
def exec_v7789 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 2
def exec_v7396 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4115
def exec_v978 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4261441663
def exec_v7397 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7398 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7396 instruction pc rs1 rs2) = (exec_v7397 instruction pc rs1 rs2) then 1 else 0
def exec_v7790 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 6
def exec_v7399 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20499
def exec_v7400 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7401 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7399 instruction pc rs1 rs2) = (exec_v7400 instruction pc rs1 rs2) then 1 else 0
def exec_v7791 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 8
def exec_v7402 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762323
def exec_v7403 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7404 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7402 instruction pc rs1 rs2) = (exec_v7403 instruction pc rs1 rs2) then 1 else 0
def exec_v7792 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 9
def exec_v7405 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 51
def exec_v7406 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7407 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7405 instruction pc rs1 rs2) = (exec_v7406 instruction pc rs1 rs2) then 1 else 0
def exec_v7408 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073741875
def exec_v7409 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7410 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7408 instruction pc rs1 rs2) = (exec_v7409 instruction pc rs1 rs2) then 1 else 0
def exec_v7793 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 1
def exec_v7411 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4147
def exec_v7412 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7413 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7411 instruction pc rs1 rs2) = (exec_v7412 instruction pc rs1 rs2) then 1 else 0
def exec_v7414 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8243
def exec_v7415 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7416 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7414 instruction pc rs1 rs2) = (exec_v7415 instruction pc rs1 rs2) then 1 else 0
def exec_v7417 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12339
def exec_v7418 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7419 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7417 instruction pc rs1 rs2) = (exec_v7418 instruction pc rs1 rs2) then 1 else 0
def exec_v7420 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16435
def exec_v7421 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7422 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7420 instruction pc rs1 rs2) = (exec_v7421 instruction pc rs1 rs2) then 1 else 0
def exec_v7423 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20531
def exec_v7424 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7425 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7423 instruction pc rs1 rs2) = (exec_v7424 instruction pc rs1 rs2) then 1 else 0
def exec_v7426 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762355
def exec_v7427 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7428 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7426 instruction pc rs1 rs2) = (exec_v7427 instruction pc rs1 rs2) then 1 else 0
def exec_v7429 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24627
def exec_v7430 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7431 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7429 instruction pc rs1 rs2) = (exec_v7430 instruction pc rs1 rs2) then 1 else 0
def exec_v7432 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28723
def exec_v7433 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v978 instruction pc rs1 rs2))
def exec_v7434 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7432 instruction pc rs1 rs2) = (exec_v7433 instruction pc rs1 rs2) then 1 else 0
def exec_v7435 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 15
def exec_v7436 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4027580415
def exec_v7437 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7436 instruction pc rs1 rs2))
def exec_v7438 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7435 instruction pc rs1 rs2) = (exec_v7437 instruction pc rs1 rs2) then 1 else 0
def exec_v7794 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 15
def exec_v7439 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4111
def exec_v7440 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7439 instruction pc rs1 rs2) = (exec_v7300 instruction pc rs1 rs2) then 1 else 0
def exec_v7441 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4211
def exec_v7442 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7443 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7442 instruction pc rs1 rs2))
def exec_v7444 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7441 instruction pc rs1 rs2) = (exec_v7443 instruction pc rs1 rs2) then 1 else 0
def exec_v7795 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.ofNat 4 10
def exec_v7445 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8307
def exec_v7446 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7447 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7446 instruction pc rs1 rs2))
def exec_v7448 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7445 instruction pc rs1 rs2) = (exec_v7447 instruction pc rs1 rs2) then 1 else 0
def exec_v7449 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12403
def exec_v7450 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7451 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7450 instruction pc rs1 rs2))
def exec_v7452 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7449 instruction pc rs1 rs2) = (exec_v7451 instruction pc rs1 rs2) then 1 else 0
def exec_v7796 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7452 instruction pc rs1 rs2) = 1 then (exec_v7795 instruction pc rs1 rs2) else (exec_v7794 instruction pc rs1 rs2)
def exec_v7797 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7448 instruction pc rs1 rs2) = 1 then (exec_v7795 instruction pc rs1 rs2) else (exec_v7796 instruction pc rs1 rs2)
def exec_v7798 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7444 instruction pc rs1 rs2) = 1 then (exec_v7795 instruction pc rs1 rs2) else (exec_v7797 instruction pc rs1 rs2)
def exec_v7799 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7440 instruction pc rs1 rs2) = 1 then (exec_v7794 instruction pc rs1 rs2) else (exec_v7798 instruction pc rs1 rs2)
def exec_v7800 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7438 instruction pc rs1 rs2) = 1 then (exec_v7794 instruction pc rs1 rs2) else (exec_v7799 instruction pc rs1 rs2)
def exec_v7801 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7434 instruction pc rs1 rs2) = 1 then (exec_v7789 instruction pc rs1 rs2) else (exec_v7800 instruction pc rs1 rs2)
def exec_v7802 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7431 instruction pc rs1 rs2) = 1 then (exec_v7788 instruction pc rs1 rs2) else (exec_v7801 instruction pc rs1 rs2)
def exec_v7803 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7428 instruction pc rs1 rs2) = 1 then (exec_v7792 instruction pc rs1 rs2) else (exec_v7802 instruction pc rs1 rs2)
def exec_v7804 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7425 instruction pc rs1 rs2) = 1 then (exec_v7791 instruction pc rs1 rs2) else (exec_v7803 instruction pc rs1 rs2)
def exec_v7805 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7422 instruction pc rs1 rs2) = 1 then (exec_v7787 instruction pc rs1 rs2) else (exec_v7804 instruction pc rs1 rs2)
def exec_v7806 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7419 instruction pc rs1 rs2) = 1 then (exec_v7786 instruction pc rs1 rs2) else (exec_v7805 instruction pc rs1 rs2)
def exec_v7807 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7416 instruction pc rs1 rs2) = 1 then (exec_v7785 instruction pc rs1 rs2) else (exec_v7806 instruction pc rs1 rs2)
def exec_v7808 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7413 instruction pc rs1 rs2) = 1 then (exec_v7790 instruction pc rs1 rs2) else (exec_v7807 instruction pc rs1 rs2)
def exec_v7809 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7410 instruction pc rs1 rs2) = 1 then (exec_v7793 instruction pc rs1 rs2) else (exec_v7808 instruction pc rs1 rs2)
def exec_v7810 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7407 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7809 instruction pc rs1 rs2)
def exec_v7811 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7404 instruction pc rs1 rs2) = 1 then (exec_v7792 instruction pc rs1 rs2) else (exec_v7810 instruction pc rs1 rs2)
def exec_v7812 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7401 instruction pc rs1 rs2) = 1 then (exec_v7791 instruction pc rs1 rs2) else (exec_v7811 instruction pc rs1 rs2)
def exec_v7813 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7398 instruction pc rs1 rs2) = 1 then (exec_v7790 instruction pc rs1 rs2) else (exec_v7812 instruction pc rs1 rs2)
def exec_v7814 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7395 instruction pc rs1 rs2) = 1 then (exec_v7789 instruction pc rs1 rs2) else (exec_v7813 instruction pc rs1 rs2)
def exec_v7815 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7391 instruction pc rs1 rs2) = 1 then (exec_v7788 instruction pc rs1 rs2) else (exec_v7814 instruction pc rs1 rs2)
def exec_v7816 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7387 instruction pc rs1 rs2) = 1 then (exec_v7787 instruction pc rs1 rs2) else (exec_v7815 instruction pc rs1 rs2)
def exec_v7817 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7383 instruction pc rs1 rs2) = 1 then (exec_v7786 instruction pc rs1 rs2) else (exec_v7816 instruction pc rs1 rs2)
def exec_v7818 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7379 instruction pc rs1 rs2) = 1 then (exec_v7785 instruction pc rs1 rs2) else (exec_v7817 instruction pc rs1 rs2)
def exec_v7819 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7375 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7818 instruction pc rs1 rs2)
def exec_v7820 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7371 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7819 instruction pc rs1 rs2)
def exec_v7821 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7367 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7820 instruction pc rs1 rs2)
def exec_v7822 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7363 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7821 instruction pc rs1 rs2)
def exec_v7823 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7359 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7822 instruction pc rs1 rs2)
def exec_v7824 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7355 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7823 instruction pc rs1 rs2)
def exec_v7825 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7351 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7824 instruction pc rs1 rs2)
def exec_v7826 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7347 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7825 instruction pc rs1 rs2)
def exec_v7827 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7343 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7826 instruction pc rs1 rs2)
def exec_v7828 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7339 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7827 instruction pc rs1 rs2)
def exec_v7829 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7335 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7828 instruction pc rs1 rs2)
def exec_v7830 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7331 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7829 instruction pc rs1 rs2)
def exec_v7831 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7327 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7830 instruction pc rs1 rs2)
def exec_v7832 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7323 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7831 instruction pc rs1 rs2)
def exec_v7833 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7319 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7832 instruction pc rs1 rs2)
def exec_v7834 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7315 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7833 instruction pc rs1 rs2)
def exec_v7835 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7311 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7834 instruction pc rs1 rs2)
def exec_v7836 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7307 instruction pc rs1 rs2) = 1 then (exec_v725 instruction pc rs1 rs2) else (exec_v7835 instruction pc rs1 rs2)
def exec_v7837 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := if (exec_v7303 instruction pc rs1 rs2) = 1 then (exec_v7784 instruction pc rs1 rs2) else (exec_v7836 instruction pc rs1 rs2)
def exec_v7838 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := (exec_v7837 instruction pc rs1 rs2)
def exec_v7839 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := (exec_v7838 instruction pc rs1 rs2)
def exec_v7840 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := (exec_v7839 instruction pc rs1 rs2)
def exec_v4 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def exec_v512 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.ofNat 1 1
def exec_v7844 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7448 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7452 instruction pc rs1 rs2)
def exec_v7845 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7444 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7844 instruction pc rs1 rs2)
def exec_v7846 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7440 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7845 instruction pc rs1 rs2)
def exec_v7847 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7438 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7846 instruction pc rs1 rs2)
def exec_v7848 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7434 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7847 instruction pc rs1 rs2)
def exec_v7849 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7431 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7848 instruction pc rs1 rs2)
def exec_v7850 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7428 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7849 instruction pc rs1 rs2)
def exec_v7851 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7425 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7850 instruction pc rs1 rs2)
def exec_v7852 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7422 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7851 instruction pc rs1 rs2)
def exec_v7853 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7419 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7852 instruction pc rs1 rs2)
def exec_v7854 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7416 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7853 instruction pc rs1 rs2)
def exec_v7855 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7413 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7854 instruction pc rs1 rs2)
def exec_v7856 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7410 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7855 instruction pc rs1 rs2)
def exec_v7857 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7407 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7856 instruction pc rs1 rs2)
def exec_v7858 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7404 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7857 instruction pc rs1 rs2)
def exec_v7859 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7401 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7858 instruction pc rs1 rs2)
def exec_v7860 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7398 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7859 instruction pc rs1 rs2)
def exec_v7861 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7395 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7860 instruction pc rs1 rs2)
def exec_v7862 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7391 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7861 instruction pc rs1 rs2)
def exec_v7863 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7387 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7862 instruction pc rs1 rs2)
def exec_v7864 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7383 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7863 instruction pc rs1 rs2)
def exec_v7865 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7379 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7864 instruction pc rs1 rs2)
def exec_v7866 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7375 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7865 instruction pc rs1 rs2)
def exec_v7867 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7371 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7866 instruction pc rs1 rs2)
def exec_v7868 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7367 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7867 instruction pc rs1 rs2)
def exec_v7869 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7363 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7868 instruction pc rs1 rs2)
def exec_v7870 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7359 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7869 instruction pc rs1 rs2)
def exec_v7871 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7355 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7870 instruction pc rs1 rs2)
def exec_v7872 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7351 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7871 instruction pc rs1 rs2)
def exec_v7873 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7347 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7872 instruction pc rs1 rs2)
def exec_v7874 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7343 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7873 instruction pc rs1 rs2)
def exec_v7875 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7339 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7874 instruction pc rs1 rs2)
def exec_v7876 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7335 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7875 instruction pc rs1 rs2)
def exec_v7877 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7331 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7876 instruction pc rs1 rs2)
def exec_v7878 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7327 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7877 instruction pc rs1 rs2)
def exec_v7879 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7323 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7878 instruction pc rs1 rs2)
def exec_v7880 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7319 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7879 instruction pc rs1 rs2)
def exec_v7881 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7315 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7880 instruction pc rs1 rs2)
def exec_v7882 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7311 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7881 instruction pc rs1 rs2)
def exec_v7883 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7307 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7882 instruction pc rs1 rs2)
def exec_v7884 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7303 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7883 instruction pc rs1 rs2)
def exec_v7885 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := (exec_v7884 instruction pc rs1 rs2)
def exec_v7886 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := (exec_v7885 instruction pc rs1 rs2)
def exec_v7887 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7886 instruction pc rs1 rs2) = (exec_v512 instruction pc rs1 rs2) then 1 else 0
def exec_v7888 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := if (exec_v7887 instruction pc rs1 rs2) = 1 then rs1 else pc
def exec_v7889 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := (exec_v7888 instruction pc rs1 rs2)
def exec_v7893 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7431 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7434 instruction pc rs1 rs2)
def exec_v7894 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7428 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7893 instruction pc rs1 rs2)
def exec_v7895 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7425 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7894 instruction pc rs1 rs2)
def exec_v7896 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7422 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7895 instruction pc rs1 rs2)
def exec_v7897 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7419 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7896 instruction pc rs1 rs2)
def exec_v7898 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7416 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7897 instruction pc rs1 rs2)
def exec_v7899 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7413 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7898 instruction pc rs1 rs2)
def exec_v7900 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7410 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7899 instruction pc rs1 rs2)
def exec_v7901 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7407 instruction pc rs1 rs2) = 1 then (exec_v512 instruction pc rs1 rs2) else (exec_v7900 instruction pc rs1 rs2)
def exec_v7902 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7404 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7901 instruction pc rs1 rs2)
def exec_v7903 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7401 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7902 instruction pc rs1 rs2)
def exec_v7904 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7398 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7903 instruction pc rs1 rs2)
def exec_v7905 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7395 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7904 instruction pc rs1 rs2)
def exec_v7906 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7391 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7905 instruction pc rs1 rs2)
def exec_v7907 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7387 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7906 instruction pc rs1 rs2)
def exec_v7908 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7383 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7907 instruction pc rs1 rs2)
def exec_v7909 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7379 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7908 instruction pc rs1 rs2)
def exec_v7910 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7375 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7909 instruction pc rs1 rs2)
def exec_v7911 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7371 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7910 instruction pc rs1 rs2)
def exec_v7912 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7367 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7911 instruction pc rs1 rs2)
def exec_v7913 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7363 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7912 instruction pc rs1 rs2)
def exec_v7914 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7359 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7913 instruction pc rs1 rs2)
def exec_v7915 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7355 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7914 instruction pc rs1 rs2)
def exec_v7916 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7351 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7915 instruction pc rs1 rs2)
def exec_v7917 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7347 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7916 instruction pc rs1 rs2)
def exec_v7918 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7343 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7917 instruction pc rs1 rs2)
def exec_v7919 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7339 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7918 instruction pc rs1 rs2)
def exec_v7920 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7335 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7919 instruction pc rs1 rs2)
def exec_v7921 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7331 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7920 instruction pc rs1 rs2)
def exec_v7922 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7327 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7921 instruction pc rs1 rs2)
def exec_v7923 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7323 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7922 instruction pc rs1 rs2)
def exec_v7924 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7319 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7923 instruction pc rs1 rs2)
def exec_v7925 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7315 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7924 instruction pc rs1 rs2)
def exec_v7926 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7311 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7925 instruction pc rs1 rs2)
def exec_v7927 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7307 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7926 instruction pc rs1 rs2)
def exec_v7928 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7303 instruction pc rs1 rs2) = 1 then (exec_v4 instruction pc rs1 rs2) else (exec_v7927 instruction pc rs1 rs2)
def exec_v7929 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := (exec_v7928 instruction pc rs1 rs2)
def exec_v7930 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := (exec_v7929 instruction pc rs1 rs2)
def exec_v7931 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7930 instruction pc rs1 rs2) = (exec_v512 instruction pc rs1 rs2) then 1 else 0
def exec_v7521 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 6
def exec_v200 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 3
def exec_v22 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 4
def exec_v29 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 1
def exec_v716 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 5
def exec_v26 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 2
def exec_v261 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := BitVec.ofNat 3 0
def exec_v7453 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20595
def exec_v7454 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7455 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7454 instruction pc rs1 rs2))
def exec_v7456 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7453 instruction pc rs1 rs2) = (exec_v7455 instruction pc rs1 rs2) then 1 else 0
def exec_v7457 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24691
def exec_v7458 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7459 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7458 instruction pc rs1 rs2))
def exec_v7460 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7457 instruction pc rs1 rs2) = (exec_v7459 instruction pc rs1 rs2) then 1 else 0
def exec_v7461 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28787
def exec_v7462 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def exec_v7463 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7300 instruction pc rs1 rs2) &&& (exec_v7462 instruction pc rs1 rs2))
def exec_v7464 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7461 instruction pc rs1 rs2) = (exec_v7463 instruction pc rs1 rs2) then 1 else 0
def exec_v7932 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7464 instruction pc rs1 rs2) = 1 then (exec_v7521 instruction pc rs1 rs2) else (exec_v261 instruction pc rs1 rs2)
def exec_v7933 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7460 instruction pc rs1 rs2) = 1 then (exec_v7521 instruction pc rs1 rs2) else (exec_v7932 instruction pc rs1 rs2)
def exec_v7934 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7456 instruction pc rs1 rs2) = 1 then (exec_v7521 instruction pc rs1 rs2) else (exec_v7933 instruction pc rs1 rs2)
def exec_v7935 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7452 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7934 instruction pc rs1 rs2)
def exec_v7936 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7448 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7935 instruction pc rs1 rs2)
def exec_v7937 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7444 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7936 instruction pc rs1 rs2)
def exec_v7938 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7440 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7937 instruction pc rs1 rs2)
def exec_v7939 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7438 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7938 instruction pc rs1 rs2)
def exec_v7940 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7434 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7939 instruction pc rs1 rs2)
def exec_v7941 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7431 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7940 instruction pc rs1 rs2)
def exec_v7942 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7428 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7941 instruction pc rs1 rs2)
def exec_v7943 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7425 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7942 instruction pc rs1 rs2)
def exec_v7944 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7422 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7943 instruction pc rs1 rs2)
def exec_v7945 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7419 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7944 instruction pc rs1 rs2)
def exec_v7946 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7416 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7945 instruction pc rs1 rs2)
def exec_v7947 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7413 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7946 instruction pc rs1 rs2)
def exec_v7948 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7410 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7947 instruction pc rs1 rs2)
def exec_v7949 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7407 instruction pc rs1 rs2) = 1 then (exec_v261 instruction pc rs1 rs2) else (exec_v7948 instruction pc rs1 rs2)
def exec_v7950 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7404 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7949 instruction pc rs1 rs2)
def exec_v7951 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7401 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7950 instruction pc rs1 rs2)
def exec_v7952 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7398 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7951 instruction pc rs1 rs2)
def exec_v7953 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7395 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7952 instruction pc rs1 rs2)
def exec_v7954 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7391 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7953 instruction pc rs1 rs2)
def exec_v7955 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7387 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7954 instruction pc rs1 rs2)
def exec_v7956 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7383 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7955 instruction pc rs1 rs2)
def exec_v7957 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7379 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7956 instruction pc rs1 rs2)
def exec_v7958 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7375 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7957 instruction pc rs1 rs2)
def exec_v7959 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7371 instruction pc rs1 rs2) = 1 then (exec_v26 instruction pc rs1 rs2) else (exec_v7958 instruction pc rs1 rs2)
def exec_v7960 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7367 instruction pc rs1 rs2) = 1 then (exec_v26 instruction pc rs1 rs2) else (exec_v7959 instruction pc rs1 rs2)
def exec_v7961 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7363 instruction pc rs1 rs2) = 1 then (exec_v26 instruction pc rs1 rs2) else (exec_v7960 instruction pc rs1 rs2)
def exec_v7962 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7359 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7961 instruction pc rs1 rs2)
def exec_v7963 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7355 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7962 instruction pc rs1 rs2)
def exec_v7964 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7351 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7963 instruction pc rs1 rs2)
def exec_v7965 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7347 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7964 instruction pc rs1 rs2)
def exec_v7966 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7343 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7965 instruction pc rs1 rs2)
def exec_v7967 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7339 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7966 instruction pc rs1 rs2)
def exec_v7968 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7335 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7967 instruction pc rs1 rs2)
def exec_v7969 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7331 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7968 instruction pc rs1 rs2)
def exec_v7970 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7327 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7969 instruction pc rs1 rs2)
def exec_v7971 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7323 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7970 instruction pc rs1 rs2)
def exec_v7972 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7319 instruction pc rs1 rs2) = 1 then (exec_v716 instruction pc rs1 rs2) else (exec_v7971 instruction pc rs1 rs2)
def exec_v7973 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7315 instruction pc rs1 rs2) = 1 then (exec_v29 instruction pc rs1 rs2) else (exec_v7972 instruction pc rs1 rs2)
def exec_v7974 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7311 instruction pc rs1 rs2) = 1 then (exec_v22 instruction pc rs1 rs2) else (exec_v7973 instruction pc rs1 rs2)
def exec_v7975 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7307 instruction pc rs1 rs2) = 1 then (exec_v200 instruction pc rs1 rs2) else (exec_v7974 instruction pc rs1 rs2)
def exec_v7976 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := if (exec_v7303 instruction pc rs1 rs2) = 1 then (exec_v200 instruction pc rs1 rs2) else (exec_v7975 instruction pc rs1 rs2)
def exec_v7977 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := (exec_v7976 instruction pc rs1 rs2)
def exec_v7978 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := (exec_v7977 instruction pc rs1 rs2)
def exec_v7979 (instruction pc rs1 rs2 : BitVec 32) : BitVec 3 := (exec_v7978 instruction pc rs1 rs2)
def exec_v7980 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v7521 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v7981 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := instruction
def exec_v7982 (instruction pc rs1 rs2 : BitVec 32) : BitVec 5 := BitVec.extractLsb' 15 5 (exec_v7981 instruction pc rs1 rs2)
def exec_v7983 (instruction pc rs1 rs2 : BitVec 32) : BitVec 6 := ((exec_v4 instruction pc rs1 rs2) ++ (exec_v7982 instruction pc rs1 rs2))
def exec_v7984 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 5 1 (exec_v7983 instruction pc rs1 rs2)
def exec_v7985 (instruction pc rs1 rs2 : BitVec 32) : BitVec 26 := BitVec.replicate 26 (exec_v7984 instruction pc rs1 rs2)
def exec_v7986 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7985 instruction pc rs1 rs2) ++ (exec_v7983 instruction pc rs1 rs2))
def exec_v7987 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v22 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v7988 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (exec_v7981 instruction pc rs1 rs2)
def exec_v7989 (instruction pc rs1 rs2 : BitVec 32) : BitVec 8 := BitVec.extractLsb' 12 8 (exec_v7981 instruction pc rs1 rs2)
def exec_v7990 (instruction pc rs1 rs2 : BitVec 32) : BitVec 9 := ((exec_v7988 instruction pc rs1 rs2) ++ (exec_v7989 instruction pc rs1 rs2))
def exec_v7991 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 20 1 (exec_v7981 instruction pc rs1 rs2)
def exec_v7992 (instruction pc rs1 rs2 : BitVec 32) : BitVec 10 := ((exec_v7990 instruction pc rs1 rs2) ++ (exec_v7991 instruction pc rs1 rs2))
def exec_v7993 (instruction pc rs1 rs2 : BitVec 32) : BitVec 6 := BitVec.extractLsb' 25 6 (exec_v7981 instruction pc rs1 rs2)
def exec_v7994 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.extractLsb' 21 4 (exec_v7981 instruction pc rs1 rs2)
def exec_v7995 (instruction pc rs1 rs2 : BitVec 32) : BitVec 10 := ((exec_v7993 instruction pc rs1 rs2) ++ (exec_v7994 instruction pc rs1 rs2))
def exec_v7996 (instruction pc rs1 rs2 : BitVec 32) : BitVec 11 := ((exec_v7995 instruction pc rs1 rs2) ++ (exec_v4 instruction pc rs1 rs2))
def exec_v7997 (instruction pc rs1 rs2 : BitVec 32) : BitVec 21 := ((exec_v7992 instruction pc rs1 rs2) ++ (exec_v7996 instruction pc rs1 rs2))
def exec_v7998 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 20 1 (exec_v7997 instruction pc rs1 rs2)
def exec_v7999 (instruction pc rs1 rs2 : BitVec 32) : BitVec 11 := BitVec.replicate 11 (exec_v7998 instruction pc rs1 rs2)
def exec_v8000 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v7999 instruction pc rs1 rs2) ++ (exec_v7997 instruction pc rs1 rs2))
def exec_v8001 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v200 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v8002 (instruction pc rs1 rs2 : BitVec 32) : BitVec 20 := BitVec.extractLsb' 12 20 (exec_v7981 instruction pc rs1 rs2)
def exec_v1810 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := BitVec.ofNat 12 0
def exec_v8003 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v8002 instruction pc rs1 rs2) ++ (exec_v1810 instruction pc rs1 rs2))
def exec_v8004 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v716 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v8005 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (exec_v7981 instruction pc rs1 rs2)
def exec_v8006 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 7 1 (exec_v7981 instruction pc rs1 rs2)
def exec_v8007 (instruction pc rs1 rs2 : BitVec 32) : BitVec 2 := ((exec_v8005 instruction pc rs1 rs2) ++ (exec_v8006 instruction pc rs1 rs2))
def exec_v8008 (instruction pc rs1 rs2 : BitVec 32) : BitVec 6 := BitVec.extractLsb' 25 6 (exec_v7981 instruction pc rs1 rs2)
def exec_v8009 (instruction pc rs1 rs2 : BitVec 32) : BitVec 8 := ((exec_v8007 instruction pc rs1 rs2) ++ (exec_v8008 instruction pc rs1 rs2))
def exec_v8010 (instruction pc rs1 rs2 : BitVec 32) : BitVec 4 := BitVec.extractLsb' 8 4 (exec_v7981 instruction pc rs1 rs2)
def exec_v8011 (instruction pc rs1 rs2 : BitVec 32) : BitVec 5 := ((exec_v8010 instruction pc rs1 rs2) ++ (exec_v4 instruction pc rs1 rs2))
def exec_v8012 (instruction pc rs1 rs2 : BitVec 32) : BitVec 13 := ((exec_v8009 instruction pc rs1 rs2) ++ (exec_v8011 instruction pc rs1 rs2))
def exec_v8013 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v26 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v8014 (instruction pc rs1 rs2 : BitVec 32) : BitVec 7 := BitVec.extractLsb' 25 7 (exec_v7981 instruction pc rs1 rs2)
def exec_v8015 (instruction pc rs1 rs2 : BitVec 32) : BitVec 5 := BitVec.extractLsb' 7 5 (exec_v7981 instruction pc rs1 rs2)
def exec_v8016 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := ((exec_v8014 instruction pc rs1 rs2) ++ (exec_v8015 instruction pc rs1 rs2))
def exec_v8017 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := if (exec_v29 instruction pc rs1 rs2) = (exec_v7979 instruction pc rs1 rs2) then 1 else 0
def exec_v8018 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := BitVec.extractLsb' 20 12 (exec_v7981 instruction pc rs1 rs2)
def exec_v8019 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := BitVec.ofNat 12 4094
def exec_v8020 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := ((exec_v8018 instruction pc rs1 rs2) &&& (exec_v8019 instruction pc rs1 rs2))
def exec_v8021 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := if (exec_v8017 instruction pc rs1 rs2) = 1 then (exec_v8018 instruction pc rs1 rs2) else (exec_v8020 instruction pc rs1 rs2)
def exec_v8022 (instruction pc rs1 rs2 : BitVec 32) : BitVec 12 := if (exec_v8013 instruction pc rs1 rs2) = 1 then (exec_v8016 instruction pc rs1 rs2) else (exec_v8021 instruction pc rs1 rs2)
def exec_v8023 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 11 1 (exec_v8022 instruction pc rs1 rs2)
def exec_v8024 (instruction pc rs1 rs2 : BitVec 32) : BitVec 13 := ((exec_v8023 instruction pc rs1 rs2) ++ (exec_v8022 instruction pc rs1 rs2))
def exec_v8025 (instruction pc rs1 rs2 : BitVec 32) : BitVec 13 := if (exec_v8004 instruction pc rs1 rs2) = 1 then (exec_v8012 instruction pc rs1 rs2) else (exec_v8024 instruction pc rs1 rs2)
def exec_v8026 (instruction pc rs1 rs2 : BitVec 32) : BitVec 1 := BitVec.extractLsb' 12 1 (exec_v8025 instruction pc rs1 rs2)
def exec_v8027 (instruction pc rs1 rs2 : BitVec 32) : BitVec 19 := BitVec.replicate 19 (exec_v8026 instruction pc rs1 rs2)
def exec_v8028 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := ((exec_v8027 instruction pc rs1 rs2) ++ (exec_v8025 instruction pc rs1 rs2))
def exec_v8029 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := if (exec_v8001 instruction pc rs1 rs2) = 1 then (exec_v8003 instruction pc rs1 rs2) else (exec_v8028 instruction pc rs1 rs2)
def exec_v8030 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := if (exec_v7987 instruction pc rs1 rs2) = 1 then (exec_v8000 instruction pc rs1 rs2) else (exec_v8029 instruction pc rs1 rs2)
def exec_v8031 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := if (exec_v7980 instruction pc rs1 rs2) = 1 then (exec_v7986 instruction pc rs1 rs2) else (exec_v8030 instruction pc rs1 rs2)
def exec_v8032 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := (exec_v8031 instruction pc rs1 rs2)
def exec_v8033 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := if (exec_v7931 instruction pc rs1 rs2) = 1 then rs2 else (exec_v8032 instruction pc rs1 rs2)
def exec_v8034 (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 := (exec_v8033 instruction pc rs1 rs2)
-- This uses the exact DUT decoder; ISA/reference equivalence is separate.
def decodedExecution (instruction pc rs1 rs2 : BitVec 32) : BitVec 32 :=
  aluSpec (exec_v7840 instruction pc rs1 rs2) (exec_v7889 instruction pc rs1 rs2) (exec_v8034 instruction pc rs1 rs2)
theorem decoded_execution_eq (s : State) (i : Inputs) :
    aluSpec (v7840 s i) (v7889 s i) (v8034 s i) =
      decodedExecution s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst
        s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc (v7629 s i) (v7725 s i) := by rfl
theorem decoded_execution_nop (pc : BitVec 32) :
    decodedExecution 19 pc 0 0 = 0 := by
  simp only [decodedExecution, exec_v8034, exec_v8033, exec_v8032, exec_v8031, exec_v8030, exec_v8029, exec_v8028, exec_v8027, exec_v8026, exec_v8025, exec_v8024, exec_v8023, exec_v8022, exec_v8021, exec_v8020, exec_v8019, exec_v8018, exec_v8017, exec_v8016, exec_v8015, exec_v8014, exec_v8013, exec_v8012, exec_v8011, exec_v8010, exec_v8009, exec_v8008, exec_v8007, exec_v8006, exec_v8005, exec_v8004, exec_v8003, exec_v1810, exec_v8002, exec_v8001, exec_v8000, exec_v7999, exec_v7998, exec_v7997, exec_v7996, exec_v7995, exec_v7994, exec_v7993, exec_v7992, exec_v7991, exec_v7990, exec_v7989, exec_v7988, exec_v7987, exec_v7986, exec_v7985, exec_v7984, exec_v7983, exec_v7982, exec_v7981, exec_v7980, exec_v7979, exec_v7978, exec_v7977, exec_v7976, exec_v7975, exec_v7974, exec_v7973, exec_v7972, exec_v7971, exec_v7970, exec_v7969, exec_v7968, exec_v7967, exec_v7966, exec_v7965, exec_v7964, exec_v7963, exec_v7962, exec_v7961, exec_v7960, exec_v7959, exec_v7958, exec_v7957, exec_v7956, exec_v7955, exec_v7954, exec_v7953, exec_v7952, exec_v7951, exec_v7950, exec_v7949, exec_v7948, exec_v7947, exec_v7946, exec_v7945, exec_v7944, exec_v7943, exec_v7942, exec_v7941, exec_v7940, exec_v7939, exec_v7938, exec_v7937, exec_v7936, exec_v7935, exec_v7934, exec_v7933, exec_v7932, exec_v7464, exec_v7463, exec_v7462, exec_v7461, exec_v7460, exec_v7459, exec_v7458, exec_v7457, exec_v7456, exec_v7455, exec_v7454, exec_v7453, exec_v261, exec_v26, exec_v716, exec_v29, exec_v22, exec_v200, exec_v7521, exec_v7931, exec_v7930, exec_v7929, exec_v7928, exec_v7927, exec_v7926, exec_v7925, exec_v7924, exec_v7923, exec_v7922, exec_v7921, exec_v7920, exec_v7919, exec_v7918, exec_v7917, exec_v7916, exec_v7915, exec_v7914, exec_v7913, exec_v7912, exec_v7911, exec_v7910, exec_v7909, exec_v7908, exec_v7907, exec_v7906, exec_v7905, exec_v7904, exec_v7903, exec_v7902, exec_v7901, exec_v7900, exec_v7899, exec_v7898, exec_v7897, exec_v7896, exec_v7895, exec_v7894, exec_v7893, exec_v7889, exec_v7888, exec_v7887, exec_v7886, exec_v7885, exec_v7884, exec_v7883, exec_v7882, exec_v7881, exec_v7880, exec_v7879, exec_v7878, exec_v7877, exec_v7876, exec_v7875, exec_v7874, exec_v7873, exec_v7872, exec_v7871, exec_v7870, exec_v7869, exec_v7868, exec_v7867, exec_v7866, exec_v7865, exec_v7864, exec_v7863, exec_v7862, exec_v7861, exec_v7860, exec_v7859, exec_v7858, exec_v7857, exec_v7856, exec_v7855, exec_v7854, exec_v7853, exec_v7852, exec_v7851, exec_v7850, exec_v7849, exec_v7848, exec_v7847, exec_v7846, exec_v7845, exec_v7844, exec_v512, exec_v4, exec_v7840, exec_v7839, exec_v7838, exec_v7837, exec_v7836, exec_v7835, exec_v7834, exec_v7833, exec_v7832, exec_v7831, exec_v7830, exec_v7829, exec_v7828, exec_v7827, exec_v7826, exec_v7825, exec_v7824, exec_v7823, exec_v7822, exec_v7821, exec_v7820, exec_v7819, exec_v7818, exec_v7817, exec_v7816, exec_v7815, exec_v7814, exec_v7813, exec_v7812, exec_v7811, exec_v7810, exec_v7809, exec_v7808, exec_v7807, exec_v7806, exec_v7805, exec_v7804, exec_v7803, exec_v7802, exec_v7801, exec_v7800, exec_v7799, exec_v7798, exec_v7797, exec_v7796, exec_v7452, exec_v7451, exec_v7450, exec_v7449, exec_v7448, exec_v7447, exec_v7446, exec_v7445, exec_v7795, exec_v7444, exec_v7443, exec_v7442, exec_v7441, exec_v7440, exec_v7439, exec_v7794, exec_v7438, exec_v7437, exec_v7436, exec_v7435, exec_v7434, exec_v7433, exec_v7432, exec_v7431, exec_v7430, exec_v7429, exec_v7428, exec_v7427, exec_v7426, exec_v7425, exec_v7424, exec_v7423, exec_v7422, exec_v7421, exec_v7420, exec_v7419, exec_v7418, exec_v7417, exec_v7416, exec_v7415, exec_v7414, exec_v7413, exec_v7412, exec_v7411, exec_v7793, exec_v7410, exec_v7409, exec_v7408, exec_v7407, exec_v7406, exec_v7405, exec_v7792, exec_v7404, exec_v7403, exec_v7402, exec_v7791, exec_v7401, exec_v7400, exec_v7399, exec_v7790, exec_v7398, exec_v7397, exec_v978, exec_v7396, exec_v7789, exec_v7395, exec_v7394, exec_v7393, exec_v7392, exec_v7788, exec_v7391, exec_v7390, exec_v7389, exec_v7388, exec_v7787, exec_v7387, exec_v7386, exec_v7385, exec_v7384, exec_v7786, exec_v7383, exec_v7382, exec_v7381, exec_v7380, exec_v7785, exec_v7379, exec_v7378, exec_v7377, exec_v7376, exec_v7375, exec_v7374, exec_v7373, exec_v7372, exec_v7371, exec_v7370, exec_v7369, exec_v7368, exec_v7367, exec_v7366, exec_v7365, exec_v7364, exec_v7363, exec_v7362, exec_v7361, exec_v7360, exec_v7359, exec_v7358, exec_v7357, exec_v7356, exec_v7355, exec_v7354, exec_v7353, exec_v7352, exec_v7351, exec_v7350, exec_v7349, exec_v7348, exec_v7347, exec_v7346, exec_v7345, exec_v7344, exec_v7343, exec_v7342, exec_v7341, exec_v7340, exec_v7339, exec_v7338, exec_v7337, exec_v7336, exec_v7335, exec_v7334, exec_v7333, exec_v7332, exec_v7331, exec_v7330, exec_v7329, exec_v7328, exec_v7327, exec_v7326, exec_v7325, exec_v7324, exec_v7323, exec_v7322, exec_v7321, exec_v7320, exec_v7319, exec_v7318, exec_v7317, exec_v7316, exec_v7315, exec_v7314, exec_v7313, exec_v7312, exec_v7311, exec_v7310, exec_v7309, exec_v7308, exec_v725, exec_v7307, exec_v7306, exec_v7305, exec_v7304, exec_v7784, exec_v7303, exec_v7302, exec_v7301, exec_v7300, exec_v7299, exec_v7298]
  simp [aluSpec]
#print axioms decoded_execution_eq
#print axioms decoded_execution_nop
end RiscvMiniProofs
