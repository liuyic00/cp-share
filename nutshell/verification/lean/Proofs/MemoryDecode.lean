import Proofs.WhitelistFamilies
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem idu_memory_0_lb_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lb (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 0 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 3 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 1 := by
    simp [v26534, v26531, v26533, v26532, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26535, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28108, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, format]
  have operation : v28643 s i = 0 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28479, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lb_decode

theorem idu_memory_0_lh_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lh (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 1 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 4099 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 1 := by
    simp [v26539, v26536, v26538, v26537, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26540, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28109, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, format]
  have operation : v28643 s i = 1 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28480, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lh_decode

theorem idu_memory_0_lw_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lw (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 2 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8195 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 1 := by
    simp [v26544, v26541, v26543, v26542, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26545, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28110, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, format]
  have operation : v28643 s i = 2 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28481, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lw_decode

theorem idu_memory_0_ld_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .ld (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 3 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12291 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v26576, v26578, v26577] using (show v26579 s i = 0 by unfold v26579; exact if_neg miss)
  have hv26584 : v26584 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v26581, v26583, v26582] using (show v26584 s i = 0 by unfold v26584; exact if_neg miss)
  have hv26589 : v26589 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v26586, v26588, v26587] using (show v26589 s i = 0 by unfold v26589; exact if_neg miss)
  have hv26594 : v26594 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v26591, v26593, v26592] using (show v26594 s i = 0 by unfold v26594; exact if_neg miss)
  have hv26599 : v26599 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v26596, v26598, v26597] using (show v26599 s i = 0 by unfold v26599; exact if_neg miss)
  have hv26604 : v26604 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v26601, v26603, v26602] using (show v26604 s i = 0 by unfold v26604; exact if_neg miss)
  have hv26609 : v26609 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v26606, v26608, v26607] using (show v26609 s i = 0 by unfold v26609; exact if_neg miss)
  have hv26614 : v26614 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v26611, v26613, v26612] using (show v26614 s i = 0 by unfold v26614; exact if_neg miss)
  have hv26619 : v26619 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24579) (by decide) matched
    simpa only [v26616, v26618, v26617] using (show v26619 s i = 0 by unfold v26619; exact if_neg miss)
  have hv26624 : v26624 s i = 1 := by
    simp [v26624, v26621, v26623, v26622, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26857, v26856, v26855, v26854, v26853, v26852, v26851, v26850, v26849, v26625, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28218, v28217, v28216, v28215, v28214, v28213, v28212, v28211, v28210, v28209, v28208, v28207, v28206, v28126, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, format]
  have operation : v28643 s i = 3 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28579, v28578, v28577, v28576, v28575, v28574, v28573, v28572, v28571, v28570, v28569, v28568, v28567, v28496, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_ld_decode

theorem idu_memory_0_lbu_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lbu (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 4 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 16387 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 1 := by
    simp [v26549, v26546, v26548, v26547, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26550, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28111, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, format]
  have operation : v28643 s i = 4 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28482, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lbu_decode

theorem idu_memory_0_lhu_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lhu (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 5 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 20483 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 1 := by
    simp [v26554, v26551, v26553, v26552, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26555, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28112, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, format]
  have operation : v28643 s i = 5 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28483, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lhu_decode

theorem idu_memory_0_lwu_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .lwu (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 6 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 24579 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v26576, v26578, v26577] using (show v26579 s i = 0 by unfold v26579; exact if_neg miss)
  have hv26584 : v26584 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v26581, v26583, v26582] using (show v26584 s i = 0 by unfold v26584; exact if_neg miss)
  have hv26589 : v26589 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v26586, v26588, v26587] using (show v26589 s i = 0 by unfold v26589; exact if_neg miss)
  have hv26594 : v26594 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v26591, v26593, v26592] using (show v26594 s i = 0 by unfold v26594; exact if_neg miss)
  have hv26599 : v26599 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v26596, v26598, v26597] using (show v26599 s i = 0 by unfold v26599; exact if_neg miss)
  have hv26604 : v26604 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v26601, v26603, v26602] using (show v26604 s i = 0 by unfold v26604; exact if_neg miss)
  have hv26609 : v26609 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v26606, v26608, v26607] using (show v26609 s i = 0 by unfold v26609; exact if_neg miss)
  have hv26614 : v26614 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v26611, v26613, v26612] using (show v26614 s i = 0 by unfold v26614; exact if_neg miss)
  have hv26619 : v26619 s i = 1 := by
    simp [v26619, v26616, v26618, v26617, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26857, v26856, v26855, v26854, v26853, v26852, v26851, v26850, v26620, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28218, v28217, v28216, v28215, v28214, v28213, v28212, v28211, v28210, v28209, v28208, v28207, v28125, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, format]
  have operation : v28643 s i = 6 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28579, v28578, v28577, v28576, v28575, v28574, v28573, v28572, v28571, v28570, v28569, v28568, v28495, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_memory_0_lwu_decode

theorem idu_memory_0_sb_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .sb (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 8 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v29154 s i = immediateS (v26210 s i) ∧ v28897 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 35 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 1 := by
    simp [v26559, v26556, v26558, v26557, matched]
  have format : v26897 s i = 2 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26560, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28113, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, format]
  have operation : v28643 s i = 8 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28484, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, format, unit, operation, kind1]
  have write : v28897 s i = 0 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_s s i format, write⟩
#print axioms idu_memory_0_sb_decode

theorem idu_memory_0_sh_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .sh (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 9 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v29154 s i = immediateS (v26210 s i) ∧ v28897 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 4131 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 1 := by
    simp [v26564, v26561, v26563, v26562, matched]
  have format : v26897 s i = 2 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26565, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28218, v28114, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, format]
  have operation : v28643 s i = 9 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28579, v28485, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, format, unit, operation, kind1]
  have write : v28897 s i = 0 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_s s i format, write⟩
#print axioms idu_memory_0_sh_decode

theorem idu_memory_0_sw_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .sw (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 10 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v29154 s i = immediateS (v26210 s i) ∧ v28897 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8227 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 1 := by
    simp [v26569, v26566, v26568, v26567, matched]
  have format : v26897 s i = 2 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26570, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28218, v28217, v28115, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, format]
  have operation : v28643 s i = 10 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28579, v28578, v28486, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, format, unit, operation, kind1]
  have write : v28897 s i = 0 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_s s i format, write⟩
#print axioms idu_memory_0_sw_decode

theorem idu_memory_0_sd_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsMemory .sd (v26210 s i)) :
    v28254 s i = 1 ∧ v28643 s i = 11 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v29154 s i = immediateS (v26210 s i) ∧ v28897 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12323 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v26576, v26578, v26577] using (show v26579 s i = 0 by unfold v26579; exact if_neg miss)
  have hv26584 : v26584 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v26581, v26583, v26582] using (show v26584 s i = 0 by unfold v26584; exact if_neg miss)
  have hv26589 : v26589 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v26586, v26588, v26587] using (show v26589 s i = 0 by unfold v26589; exact if_neg miss)
  have hv26594 : v26594 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v26591, v26593, v26592] using (show v26594 s i = 0 by unfold v26594; exact if_neg miss)
  have hv26599 : v26599 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v26596, v26598, v26597] using (show v26599 s i = 0 by unfold v26599; exact if_neg miss)
  have hv26604 : v26604 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v26601, v26603, v26602] using (show v26604 s i = 0 by unfold v26604; exact if_neg miss)
  have hv26609 : v26609 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v26606, v26608, v26607] using (show v26609 s i = 0 by unfold v26609; exact if_neg miss)
  have hv26614 : v26614 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v26611, v26613, v26612] using (show v26614 s i = 0 by unfold v26614; exact if_neg miss)
  have hv26619 : v26619 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24579) (by decide) matched
    simpa only [v26616, v26618, v26617] using (show v26619 s i = 0 by unfold v26619; exact if_neg miss)
  have hv26624 : v26624 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12291) (by decide) matched
    simpa only [v26621, v26623, v26622] using (show v26624 s i = 0 by unfold v26624; exact if_neg miss)
  have hv26629 : v26629 s i = 1 := by
    simp [v26629, v26626, v26628, v26627, matched]
  have format : v26897 s i = 2 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26857, v26856, v26855, v26854, v26853, v26852, v26851, v26850, v26849, v26848, v26630, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629]
  have unit : v28254 s i = 1 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28234, v28233, v28232, v28231, v28230, v28229, v28228, v28227, v28226, v28225, v28224, v28223, v28222, v28221, v28220, v28219, v28218, v28217, v28216, v28215, v28214, v28213, v28212, v28211, v28210, v28209, v28208, v28207, v28206, v28205, v28127, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629, format]
  have operation : v28643 s i = 11 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28595, v28594, v28593, v28592, v28591, v28590, v28589, v28588, v28587, v28586, v28585, v28584, v28583, v28582, v28581, v28580, v28579, v28578, v28577, v28576, v28575, v28574, v28573, v28572, v28571, v28570, v28569, v28568, v28567, v28566, v28497, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629, format, unit, operation, kind1]
  have write : v28897 s i = 0 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, hv26594, hv26599, hv26604, hv26609, hv26614, hv26619, hv26624, hv26629, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_s s i format, write⟩
#print axioms idu_memory_0_sd_decode

theorem idu_memory_1_lb_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lb (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 0 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 3 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 1 := by
    simp [v27061, v27058, v27060, v27059, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27062, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28292, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, format]
  have operation : v28836 s i = 0 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28674, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lb_decode

theorem idu_memory_1_lh_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lh (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 1 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 4099 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4099) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 1 := by
    simp [v27066, v27063, v27065, v27064, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27067, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28293, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, format]
  have operation : v28836 s i = 1 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28675, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lh_decode

theorem idu_memory_1_lw_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lw (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 2 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8195 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8195) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 1 := by
    simp [v27071, v27068, v27070, v27069, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27072, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28294, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, format]
  have operation : v28836 s i = 2 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28676, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lw_decode

theorem idu_memory_1_ld_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .ld (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 3 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12291 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v27103, v27105, v27104] using (show v27106 s i = 0 by unfold v27106; exact if_neg miss)
  have hv27111 : v27111 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v27108, v27110, v27109] using (show v27111 s i = 0 by unfold v27111; exact if_neg miss)
  have hv27116 : v27116 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v27113, v27115, v27114] using (show v27116 s i = 0 by unfold v27116; exact if_neg miss)
  have hv27121 : v27121 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v27118, v27120, v27119] using (show v27121 s i = 0 by unfold v27121; exact if_neg miss)
  have hv27126 : v27126 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v27123, v27125, v27124] using (show v27126 s i = 0 by unfold v27126; exact if_neg miss)
  have hv27131 : v27131 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v27128, v27130, v27129] using (show v27131 s i = 0 by unfold v27131; exact if_neg miss)
  have hv27136 : v27136 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v27133, v27135, v27134] using (show v27136 s i = 0 by unfold v27136; exact if_neg miss)
  have hv27141 : v27141 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v27138, v27140, v27139] using (show v27141 s i = 0 by unfold v27141; exact if_neg miss)
  have hv27146 : v27146 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12291) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24579) (by decide) matched
    simpa only [v27143, v27145, v27144] using (show v27146 s i = 0 by unfold v27146; exact if_neg miss)
  have hv27151 : v27151 s i = 1 := by
    simp [v27151, v27148, v27150, v27149, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27384, v27383, v27382, v27381, v27380, v27379, v27378, v27377, v27376, v27152, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28402, v28401, v28400, v28399, v28398, v28397, v28396, v28395, v28394, v28393, v28392, v28391, v28390, v28310, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, format]
  have operation : v28836 s i = 3 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28772, v28771, v28770, v28769, v28768, v28767, v28766, v28765, v28764, v28763, v28762, v28761, v28760, v28690, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_ld_decode

theorem idu_memory_1_lbu_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lbu (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 4 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 16387 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16387) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 1 := by
    simp [v27076, v27073, v27075, v27074, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27077, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28295, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, format]
  have operation : v28836 s i = 4 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28677, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lbu_decode

theorem idu_memory_1_lhu_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lhu (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 5 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 20483 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 20483) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 1 := by
    simp [v27081, v27078, v27080, v27079, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27082, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28296, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, format]
  have operation : v28836 s i = 5 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28678, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lhu_decode

theorem idu_memory_1_lwu_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .lwu (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 6 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 24579 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v27103, v27105, v27104] using (show v27106 s i = 0 by unfold v27106; exact if_neg miss)
  have hv27111 : v27111 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v27108, v27110, v27109] using (show v27111 s i = 0 by unfold v27111; exact if_neg miss)
  have hv27116 : v27116 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v27113, v27115, v27114] using (show v27116 s i = 0 by unfold v27116; exact if_neg miss)
  have hv27121 : v27121 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v27118, v27120, v27119] using (show v27121 s i = 0 by unfold v27121; exact if_neg miss)
  have hv27126 : v27126 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v27123, v27125, v27124] using (show v27126 s i = 0 by unfold v27126; exact if_neg miss)
  have hv27131 : v27131 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v27128, v27130, v27129] using (show v27131 s i = 0 by unfold v27131; exact if_neg miss)
  have hv27136 : v27136 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v27133, v27135, v27134] using (show v27136 s i = 0 by unfold v27136; exact if_neg miss)
  have hv27141 : v27141 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24579) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v27138, v27140, v27139] using (show v27141 s i = 0 by unfold v27141; exact if_neg miss)
  have hv27146 : v27146 s i = 1 := by
    simp [v27146, v27143, v27145, v27144, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27384, v27383, v27382, v27381, v27380, v27379, v27378, v27377, v27147, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28402, v28401, v28400, v28399, v28398, v28397, v28396, v28395, v28394, v28393, v28392, v28391, v28309, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, format]
  have operation : v28836 s i = 6 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28772, v28771, v28770, v28769, v28768, v28767, v28766, v28765, v28764, v28763, v28762, v28761, v28689, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_memory_1_lwu_decode

theorem idu_memory_1_sb_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .sb (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 8 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v29230 s i = immediateS (v26223 s i) ∧ v28903 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 35 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 35) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 1 := by
    simp [v27086, v27083, v27085, v27084, matched]
  have format : v27424 s i = 2 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27087, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28297, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, format]
  have operation : v28836 s i = 8 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28679, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, format, unit, operation, kind1]
  have write : v28903 s i = 0 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_s s i format, write⟩
#print axioms idu_memory_1_sb_decode

theorem idu_memory_1_sh_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .sh (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 9 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v29230 s i = immediateS (v26223 s i) ∧ v28903 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 4131 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 4131) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 1 := by
    simp [v27091, v27088, v27090, v27089, matched]
  have format : v27424 s i = 2 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27092, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28402, v28298, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, format]
  have operation : v28836 s i = 9 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28772, v28680, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, format, unit, operation, kind1]
  have write : v28903 s i = 0 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_s s i format, write⟩
#print axioms idu_memory_1_sh_decode

theorem idu_memory_1_sw_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .sw (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 10 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v29230 s i = immediateS (v26223 s i) ∧ v28903 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8227 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8227) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 1 := by
    simp [v27096, v27093, v27095, v27094, matched]
  have format : v27424 s i = 2 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27097, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28402, v28401, v28299, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, format]
  have operation : v28836 s i = 10 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28772, v28771, v28681, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, format, unit, operation, kind1]
  have write : v28903 s i = 0 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_s s i format, write⟩
#print axioms idu_memory_1_sw_decode

theorem idu_memory_1_sd_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsMemory .sd (v26223 s i)) :
    v28438 s i = 1 ∧ v28836 s i = 11 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v29230 s i = immediateS (v26223 s i) ∧ v28903 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12323 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v27103, v27105, v27104] using (show v27106 s i = 0 by unfold v27106; exact if_neg miss)
  have hv27111 : v27111 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v27108, v27110, v27109] using (show v27111 s i = 0 by unfold v27111; exact if_neg miss)
  have hv27116 : v27116 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762331) (by decide) matched
    simpa only [v27113, v27115, v27114] using (show v27116 s i = 0 by unfold v27116; exact if_neg miss)
  have hv27121 : v27121 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4155) (by decide) matched
    simpa only [v27118, v27120, v27119] using (show v27121 s i = 0 by unfold v27121; exact if_neg miss)
  have hv27126 : v27126 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20539) (by decide) matched
    simpa only [v27123, v27125, v27124] using (show v27126 s i = 0 by unfold v27126; exact if_neg miss)
  have hv27131 : v27131 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762363) (by decide) matched
    simpa only [v27128, v27130, v27129] using (show v27131 s i = 0 by unfold v27131; exact if_neg miss)
  have hv27136 : v27136 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 59) (by decide) matched
    simpa only [v27133, v27135, v27134] using (show v27136 s i = 0 by unfold v27136; exact if_neg miss)
  have hv27141 : v27141 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741883) (by decide) matched
    simpa only [v27138, v27140, v27139] using (show v27141 s i = 0 by unfold v27141; exact if_neg miss)
  have hv27146 : v27146 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24579) (by decide) matched
    simpa only [v27143, v27145, v27144] using (show v27146 s i = 0 by unfold v27146; exact if_neg miss)
  have hv27151 : v27151 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12291) (by decide) matched
    simpa only [v27148, v27150, v27149] using (show v27151 s i = 0 by unfold v27151; exact if_neg miss)
  have hv27156 : v27156 s i = 1 := by
    simp [v27156, v27153, v27155, v27154, matched]
  have format : v27424 s i = 2 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27384, v27383, v27382, v27381, v27380, v27379, v27378, v27377, v27376, v27375, v27157, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156]
  have unit : v28438 s i = 1 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28418, v28417, v28416, v28415, v28414, v28413, v28412, v28411, v28410, v28409, v28408, v28407, v28406, v28405, v28404, v28403, v28402, v28401, v28400, v28399, v28398, v28397, v28396, v28395, v28394, v28393, v28392, v28391, v28390, v28389, v28311, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156, format]
  have operation : v28836 s i = 11 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28788, v28787, v28786, v28785, v28784, v28783, v28782, v28781, v28780, v28779, v28778, v28777, v28776, v28775, v28774, v28773, v28772, v28771, v28770, v28769, v28768, v28767, v28766, v28765, v28764, v28763, v28762, v28761, v28760, v28759, v28691, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156, format, unit, operation, kind1]
  have write : v28903 s i = 0 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, hv27121, hv27126, hv27131, hv27136, hv27141, hv27146, hv27151, hv27156, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_s s i format, write⟩
#print axioms idu_memory_1_sd_decode

end NutShellProofs
