import Proofs.LoadDataFormat
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem load_byte_offset_0 (s : State) (i : Inputs)
    (offset : v12359 s i = 0) :
    v12412 s i = s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_0
theorem load_byte_offset_1 (s : State) (i : Inputs)
    (offset : v12359 s i = 1) :
    v12412 s i = ((0 : BitVec 8) ++ BitVec.extractLsb' 8 56 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_1
theorem load_byte_offset_2 (s : State) (i : Inputs)
    (offset : v12359 s i = 2) :
    v12412 s i = ((0 : BitVec 16) ++ BitVec.extractLsb' 16 48 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_2
theorem load_byte_offset_3 (s : State) (i : Inputs)
    (offset : v12359 s i = 3) :
    v12412 s i = ((0 : BitVec 24) ++ BitVec.extractLsb' 24 40 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_3
theorem load_byte_offset_4 (s : State) (i : Inputs)
    (offset : v12359 s i = 4) :
    v12412 s i = ((0 : BitVec 32) ++ BitVec.extractLsb' 32 32 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_4
theorem load_byte_offset_5 (s : State) (i : Inputs)
    (offset : v12359 s i = 5) :
    v12412 s i = ((0 : BitVec 40) ++ BitVec.extractLsb' 40 24 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_5
theorem load_byte_offset_6 (s : State) (i : Inputs)
    (offset : v12359 s i = 6) :
    v12412 s i = ((0 : BitVec 48) ++ BitVec.extractLsb' 48 16 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_6
theorem load_byte_offset_7 (s : State) (i : Inputs)
    (offset : v12359 s i = 7) :
    v12412 s i = ((0 : BitVec 56) ++ BitVec.extractLsb' 56 8 s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) := by
  unfold v12412 v12405 v12398 v12391 v12385 v12377 v12370 v12362 v12360 v12358 v12361 v12369 v12363 v12368 v12365 v12364 v12366 v12367 v12376 v9740 v12375 v12372 v12371 v12373 v12374 v12384 v12378 v12383 v12380 v12379 v12381 v12382 v12390 v11103 v12389 v12386 v4 v12387 v12388 v12397 v12392 v12396 v12393 v9701 v12394 v12395 v12404 v12399 v12403 v12400 v97 v12401 v12402 v12411 v12406 v12410 v12407 v11535 v12408 v12409
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [offset]
#print axioms load_byte_offset_7
end NutShellProofs
