import Proofs.ImmediateEncoding
import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive RegisterALUOp where
  | add | sub | slt | sltu | xor | or | and | sll | srl | sra
  deriving DecidableEq

def RegisterALUOp.encoding : RegisterALUOp → BitVec 64
  | .add => 51
  | .sub => 1073741875
  | .slt => 8243
  | .sltu => 12339
  | .xor => 16435
  | .or => 24627
  | .and => 28723
  | .sll => 4147
  | .srl => 20531
  | .sra => 1073762355

def RegisterALUOp.control : RegisterALUOp → BitVec 7
  | .add => 64
  | .sub => 8
  | .slt => 2
  | .sltu => 3
  | .xor => 4
  | .or => 6
  | .and => 7
  | .sll => 1
  | .srl => 5
  | .sra => 13

def RegisterALUOp.mask (_ : RegisterALUOp) : BitVec 64 := 4261441663

def IsRegisterALU (op : RegisterALUOp) (instr : BitVec 64) : Prop :=
  instr &&& op.mask = op.encoding

theorem idu_register_alu_0_add_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .add (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 64 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 51 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 1 := by
    simp [v26434, v26431, v26433, v26432, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26435, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28088, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, format]
  have operation : v28643 s i = 64 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v12968, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_add_decode

theorem idu_register_alu_0_sub_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .sub (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 8 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073741875 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 1 := by
    simp [v26474, v26471, v26473, v26472, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26475, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28096, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, format]
  have operation : v28643 s i = 8 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28471, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_sub_decode

theorem idu_register_alu_0_slt_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .slt (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 2 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 8243 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 1 := by
    simp [v26444, v26441, v26443, v26442, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26445, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28090, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, format]
  have operation : v28643 s i = 2 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28465, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_slt_decode

theorem idu_register_alu_0_sltu_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .sltu (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 3 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 12339 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 1 := by
    simp [v26449, v26446, v26448, v26447, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26450, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28091, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, format]
  have operation : v28643 s i = 3 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28466, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_sltu_decode

theorem idu_register_alu_0_xor_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .xor (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 4 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 16435 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 1 := by
    simp [v26454, v26451, v26453, v26452, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26455, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28092, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, format]
  have operation : v28643 s i = 4 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28467, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_xor_decode

theorem idu_register_alu_0_or_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .or (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 6 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 24627 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 1 := by
    simp [v26464, v26461, v26463, v26462, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26465, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28094, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, format]
  have operation : v28643 s i = 6 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28469, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_or_decode

theorem idu_register_alu_0_and_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .and (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 7 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 28723 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 1 := by
    simp [v26469, v26466, v26468, v26467, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26470, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28095, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, format]
  have operation : v28643 s i = 7 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28470, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_and_decode

theorem idu_register_alu_0_sll_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .sll (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 1 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 4147 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 1 := by
    simp [v26439, v26436, v26438, v26437, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26440, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28089, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, format]
  have operation : v28643 s i = 1 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28464, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_sll_decode

theorem idu_register_alu_0_srl_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .srl (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 5 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 20531 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 1 := by
    simp [v26459, v26456, v26458, v26457, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26460, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28093, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, format]
  have operation : v28643 s i = 5 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28468, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_srl_decode

theorem idu_register_alu_0_sra_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsRegisterALU .sra (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 13 ∧ v28010 s i = 0 ∧ v28050 s i = 0 ∧
      v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073762355 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 1 := by
    simp [v26479, v26476, v26478, v26477, matched]
  have format : v26897 s i = 5 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26480, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28245, v28244, v28243, v28242, v28241, v28240, v28239, v28238, v28237, v28236, v28235, v28097, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, format]
  have operation : v28643 s i = 13 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28606, v28605, v28604, v28603, v28602, v28601, v28600, v28599, v28598, v28597, v28596, v28472, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, format, unit, operation]
  have kind2 : v28050 s i = 0 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_0_sra_decode

theorem idu_register_alu_1_add_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .add (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 64 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 51 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 51) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 1 := by
    simp [v26961, v26958, v26960, v26959, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v26962, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28272, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, format]
  have operation : v28836 s i = 64 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v12968, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_add_decode

theorem idu_register_alu_1_sub_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .sub (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 8 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073741875 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073741875) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 1 := by
    simp [v27001, v26998, v27000, v26999, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27002, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28280, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, format]
  have operation : v28836 s i = 8 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28666, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_sub_decode

theorem idu_register_alu_1_slt_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .slt (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 2 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 8243 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 8243) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 1 := by
    simp [v26971, v26968, v26970, v26969, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v26972, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28274, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, format]
  have operation : v28836 s i = 2 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28660, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_slt_decode

theorem idu_register_alu_1_sltu_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .sltu (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 3 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 12339 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 12339) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 1 := by
    simp [v26976, v26973, v26975, v26974, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v26977, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28275, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, format]
  have operation : v28836 s i = 3 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28661, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_sltu_decode

theorem idu_register_alu_1_xor_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .xor (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 4 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 16435 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 16435) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 1 := by
    simp [v26981, v26978, v26980, v26979, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v26982, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28276, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, format]
  have operation : v28836 s i = 4 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28662, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_xor_decode

theorem idu_register_alu_1_or_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .or (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 6 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 24627 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 24627) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 1 := by
    simp [v26991, v26988, v26990, v26989, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v26992, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28278, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, format]
  have operation : v28836 s i = 6 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28664, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_or_decode

theorem idu_register_alu_1_and_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .and (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 7 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 28723 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 28723) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 1 := by
    simp [v26996, v26993, v26995, v26994, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v26997, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28279, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, format]
  have operation : v28836 s i = 7 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28665, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_and_decode

theorem idu_register_alu_1_sll_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .sll (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 1 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 4147 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4147) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 1 := by
    simp [v26966, v26963, v26965, v26964, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v26967, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28273, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, format]
  have operation : v28836 s i = 1 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28659, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_sll_decode

theorem idu_register_alu_1_srl_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .srl (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 5 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 20531 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20531) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 1 := by
    simp [v26986, v26983, v26985, v26984, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v26987, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28277, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, format]
  have operation : v28836 s i = 5 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28663, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_srl_decode

theorem idu_register_alu_1_sra_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsRegisterALU .sra (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 13 ∧ v28027 s i = 0 ∧ v28066 s i = 0 ∧
      v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073762355 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762355) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 1 := by
    simp [v27006, v27003, v27005, v27004, matched]
  have format : v27424 s i = 5 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27007, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28429, v28428, v28427, v28426, v28425, v28424, v28423, v28422, v28421, v28420, v28419, v28281, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, format]
  have operation : v28836 s i = 13 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28799, v28798, v28797, v28796, v28795, v28794, v28793, v28792, v28791, v28790, v28789, v28667, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, format, unit, operation]
  have kind2 : v28066 s i = 0 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, write⟩
#print axioms idu_register_alu_1_sra_decode

end NutShellProofs
