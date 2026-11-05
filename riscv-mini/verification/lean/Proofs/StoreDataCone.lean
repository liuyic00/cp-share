import Proofs.ExecutionAlignment
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedVariables false
def storePack_v155 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.ofNat 2 3
def storePack_v8523 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := if (storePack_v155 kind address source) = kind then 1 else 0
def storePack_v4 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def storePack_v8524 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.ofNat 4 1
def storePack_v32 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.ofNat 2 0
def storePack_v8525 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def storePack_v8526 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := ((storePack_v32 kind address source) ++ (storePack_v8525 kind address source))
def storePack_v8527 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.shiftLeft (storePack_v8524 kind address source) (storePack_v8526 kind address source).toNat
def storePack_v8528 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := ((storePack_v4 kind address source) ++ (storePack_v8527 kind address source))
def storePack_v38 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.ofNat 2 2
def storePack_v8529 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := if (storePack_v38 kind address source) = kind then 1 else 0
def storePack_v8530 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := BitVec.ofNat 5 3
def storePack_v261 (kind : BitVec 2) (address source : BitVec 32) : BitVec 3 := BitVec.ofNat 3 0
def storePack_v8531 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def storePack_v8532 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := ((storePack_v261 kind address source) ++ (storePack_v8531 kind address source))
def storePack_v8533 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := BitVec.shiftLeft (storePack_v8530 kind address source) (storePack_v8532 kind address source).toNat
def storePack_v42 (kind : BitVec 2) (address source : BitVec 32) : BitVec 2 := BitVec.ofNat 2 1
def storePack_v8534 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := if (storePack_v42 kind address source) = kind then 1 else 0
def storePack_v7794 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.ofNat 4 15
def storePack_v8535 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def storePack_v8536 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := if (storePack_v8534 kind address source) = 1 then (storePack_v7794 kind address source) else (storePack_v8535 kind address source)
def storePack_v8537 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := ((storePack_v4 kind address source) ++ (storePack_v8536 kind address source))
def storePack_v8538 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := if (storePack_v8529 kind address source) = 1 then (storePack_v8533 kind address source) else (storePack_v8537 kind address source)
def storePack_v8539 (kind : BitVec 2) (address source : BitVec 32) : BitVec 5 := if (storePack_v8523 kind address source) = 1 then (storePack_v8528 kind address source) else (storePack_v8538 kind address source)
def storePack_v8540 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.extractLsb' 0 4 (storePack_v8539 kind address source)
def storePack_v8541 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := (storePack_v8540 kind address source)
def storePack_v8544 (kind : BitVec 2) (address source : BitVec 32) : BitVec 255 := BitVec.ofNat 255 0
def storePack_v8545 (kind : BitVec 2) (address source : BitVec 32) : BitVec 287 := ((storePack_v8544 kind address source) ++ source)
def storePack_v8546 (kind : BitVec 2) (address source : BitVec 32) : BitVec 279 := BitVec.ofNat 279 0
def storePack_v720 (kind : BitVec 2) (address source : BitVec 32) : BitVec 7 := BitVec.ofNat 7 0
def storePack_v8547 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := BitVec.extractLsb' 1 1 address
def storePack_v8548 (kind : BitVec 2) (address source : BitVec 32) : BitVec 8 := ((storePack_v720 kind address source) ++ (storePack_v8547 kind address source))
def storePack_v8549 (kind : BitVec 2) (address source : BitVec 32) : BitVec 8 := BitVec.ofNat 8 4
def storePack_v8550 (kind : BitVec 2) (address source : BitVec 32) : BitVec 8 := BitVec.shiftLeft (storePack_v8548 kind address source) (storePack_v8549 kind address source).toNat
def storePack_v725 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def storePack_v8551 (kind : BitVec 2) (address source : BitVec 32) : BitVec 1 := BitVec.extractLsb' 0 1 address
def storePack_v8552 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := ((storePack_v261 kind address source) ++ (storePack_v8551 kind address source))
def storePack_v8553 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.ofNat 4 3
def storePack_v8554 (kind : BitVec 2) (address source : BitVec 32) : BitVec 4 := BitVec.shiftLeft (storePack_v8552 kind address source) (storePack_v8553 kind address source).toNat
def storePack_v8555 (kind : BitVec 2) (address source : BitVec 32) : BitVec 8 := ((storePack_v725 kind address source) ++ (storePack_v8554 kind address source))
def storePack_v8556 (kind : BitVec 2) (address source : BitVec 32) : BitVec 8 := ((storePack_v8550 kind address source) ||| (storePack_v8555 kind address source))
def storePack_v8557 (kind : BitVec 2) (address source : BitVec 32) : BitVec 287 := ((storePack_v8546 kind address source) ++ (storePack_v8556 kind address source))
def storePack_v8558 (kind : BitVec 2) (address source : BitVec 32) : BitVec 287 := BitVec.shiftLeft (storePack_v8545 kind address source) (storePack_v8557 kind address source).toNat
def storePack_v8559 (kind : BitVec 2) (address source : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (storePack_v8558 kind address source)
def storePack_v8560 (kind : BitVec 2) (address source : BitVec 32) : BitVec 32 := (storePack_v8559 kind address source)
def storeUnpack_v9213 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := BitVec.extractLsb' 3 1 mask
def storeUnpack_v9214 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := BitVec.ofNat 8 255
def storeUnpack_v2012 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := BitVec.ofNat 8 0
def storeUnpack_v9215 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := if (storeUnpack_v9213 mask address data) = 1 then (storeUnpack_v9214 mask address data) else (storeUnpack_v2012 mask address data)
def storeUnpack_v9216 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := BitVec.extractLsb' 2 1 mask
def storeUnpack_v9217 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := if (storeUnpack_v9216 mask address data) = 1 then (storeUnpack_v9214 mask address data) else (storeUnpack_v2012 mask address data)
def storeUnpack_v9218 (mask : BitVec 4) (address data : BitVec 32) : BitVec 16 := ((storeUnpack_v9215 mask address data) ++ (storeUnpack_v9217 mask address data))
def storeUnpack_v9219 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := BitVec.extractLsb' 1 1 mask
def storeUnpack_v9220 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := if (storeUnpack_v9219 mask address data) = 1 then (storeUnpack_v9214 mask address data) else (storeUnpack_v2012 mask address data)
def storeUnpack_v9221 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := BitVec.extractLsb' 0 1 mask
def storeUnpack_v9222 (mask : BitVec 4) (address data : BitVec 32) : BitVec 8 := if (storeUnpack_v9221 mask address data) = 1 then (storeUnpack_v9214 mask address data) else (storeUnpack_v2012 mask address data)
def storeUnpack_v9223 (mask : BitVec 4) (address data : BitVec 32) : BitVec 16 := ((storeUnpack_v9220 mask address data) ++ (storeUnpack_v9222 mask address data))
def storeUnpack_v9224 (mask : BitVec 4) (address data : BitVec 32) : BitVec 32 := ((storeUnpack_v9218 mask address data) ++ (storeUnpack_v9223 mask address data))
def storeUnpack_v9225 (mask : BitVec 4) (address data : BitVec 32) : BitVec 32 := (data &&& (storeUnpack_v9224 mask address data))
def storeUnpack_v2104 (mask : BitVec 4) (address data : BitVec 32) : BitVec 27 := BitVec.ofNat 27 0
def storeUnpack_v155 (mask : BitVec 4) (address data : BitVec 32) : BitVec 2 := BitVec.ofNat 2 3
def storeUnpack_v9226 (mask : BitVec 4) (address data : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def storeUnpack_v9227 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := if (storeUnpack_v155 mask address data) = (storeUnpack_v9226 mask address data) then 1 else 0
def storeUnpack_v908 (mask : BitVec 4) (address data : BitVec 32) : BitVec 5 := BitVec.ofNat 5 24
def storeUnpack_v38 (mask : BitVec 4) (address data : BitVec 32) : BitVec 2 := BitVec.ofNat 2 2
def storeUnpack_v9228 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := if (storeUnpack_v38 mask address data) = (storeUnpack_v9226 mask address data) then 1 else 0
def storeUnpack_v860 (mask : BitVec 4) (address data : BitVec 32) : BitVec 5 := BitVec.ofNat 5 16
def storeUnpack_v4 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def storeUnpack_v9229 (mask : BitVec 4) (address data : BitVec 32) : BitVec 2 := BitVec.ofNat 2 1
def storeUnpack_v9230 (mask : BitVec 4) (address data : BitVec 32) : BitVec 1 := if (storeUnpack_v9229 mask address data) = (storeUnpack_v9226 mask address data) then 1 else 0
def storeUnpack_v7791 (mask : BitVec 4) (address data : BitVec 32) : BitVec 4 := BitVec.ofNat 4 8
def storeUnpack_v725 (mask : BitVec 4) (address data : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def storeUnpack_v9231 (mask : BitVec 4) (address data : BitVec 32) : BitVec 4 := if (storeUnpack_v9230 mask address data) = 1 then (storeUnpack_v7791 mask address data) else (storeUnpack_v725 mask address data)
def storeUnpack_v9232 (mask : BitVec 4) (address data : BitVec 32) : BitVec 5 := ((storeUnpack_v4 mask address data) ++ (storeUnpack_v9231 mask address data))
def storeUnpack_v9233 (mask : BitVec 4) (address data : BitVec 32) : BitVec 5 := if (storeUnpack_v9228 mask address data) = 1 then (storeUnpack_v860 mask address data) else (storeUnpack_v9232 mask address data)
def storeUnpack_v9234 (mask : BitVec 4) (address data : BitVec 32) : BitVec 5 := if (storeUnpack_v9227 mask address data) = 1 then (storeUnpack_v908 mask address data) else (storeUnpack_v9233 mask address data)
def storeUnpack_v9235 (mask : BitVec 4) (address data : BitVec 32) : BitVec 32 := ((storeUnpack_v2104 mask address data) ++ (storeUnpack_v9234 mask address data))
def storeUnpack_v9236 (mask : BitVec 4) (address data : BitVec 32) : BitVec 32 := BitVec.ushiftRight (storeUnpack_v9225 mask address data) (storeUnpack_v9235 mask address data).toNat
def storeUnpack_v9237 (mask : BitVec 4) (address data : BitVec 32) : BitVec 32 := (storeUnpack_v9236 mask address data)
abbrev storeMask := storePack_v8541
abbrev storeData := storePack_v8560
abbrev checkedStoreData := storeUnpack_v9237
theorem store_mask_cone (s : State) (i : Inputs) :
    v8541 s i = storeMask (v8522 s i) (v8492 s i) (v7725 s i) := rfl
theorem store_data_cone (s : State) (i : Inputs) :
    v8560 s i = storeData (v8522 s i) (v8492 s i) (v7725 s i) := rfl
theorem checked_store_data_cone (s : State) (i : Inputs) :
    v9237 s i = checkedStoreData s.g4.r141_ndut_5Fdpath_5Fmem_5Fwmask
      s.g4.r154_ndut_5Fdpath_5Freq_5Faddr s.g4.r142_ndut_5Fdpath_5Fmem_5Fwdata := rfl
#print axioms store_mask_cone
#print axioms store_data_cone
#print axioms checked_store_data_cone
end RiscvMiniProofs
