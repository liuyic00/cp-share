import Proofs.ImmediateEncoding
import Proofs.DecodeBits
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

inductive ImmediateALUOp where
  | add | slt | sltu | xor | or | and
  deriving DecidableEq

def ImmediateALUOp.encoding : ImmediateALUOp → BitVec 64
  | .add => 19 | .slt => 8211 | .sltu => 12307
  | .xor => 16403 | .or => 24595 | .and => 28691

def ImmediateALUOp.control : ImmediateALUOp → BitVec 7
  | .add => 64 | .slt => 2 | .sltu => 3
  | .xor => 4 | .or => 6 | .and => 7

def IsImmediateALU (op : ImmediateALUOp) (instr : BitVec 64) : Prop :=
  instr &&& BitVec.ofNat 64 28799 = op.encoding

theorem idu_immediate_0_add_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .add (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 64 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 19 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 1 := by
    simp [v26389, v26386, v26388, v26387, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26390, normal, unitOverride, opOverride, hv26389]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28079, normal, unitOverride, opOverride, hv26389, format]
  have operation : v28643 s i = 64 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v12968, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_add_decode

theorem idu_immediate_0_slt_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .slt (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 2 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8211 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8211) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8211) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 1 := by
    simp [v26399, v26396, v26398, v26397, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26400, normal, unitOverride, opOverride, hv26389, hv26394, hv26399]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28081, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, format]
  have operation : v28643 s i = 2 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28457, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_slt_decode

theorem idu_immediate_0_sltu_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .sltu (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 3 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12307 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 1 := by
    simp [v26404, v26401, v26403, v26402, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26405, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28082, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, format]
  have operation : v28643 s i = 3 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28458, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_sltu_decode

theorem idu_immediate_0_xor_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .xor (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 4 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 16403 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 1 := by
    simp [v26409, v26406, v26408, v26407, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26410, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28083, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, format]
  have operation : v28643 s i = 4 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28459, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_xor_decode

theorem idu_immediate_0_or_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .or (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 6 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 24595 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 1 := by
    simp [v26419, v26416, v26418, v26417, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26420, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28085, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, format]
  have operation : v28643 s i = 6 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28461, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_or_decode

theorem idu_immediate_0_and_decode (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsImmediateALU .and (v26210 s i)) :
    v28254 s i = 0 ∧ v28643 s i = 7 ∧ v28010 s i = 0 ∧ v28050 s i = 1 ∧
      v29154 s i = immediateI (v26210 s i) ∧ v28897 s i = 1 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 28691 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 1 := by
    simp [v26424, v26421, v26423, v26422, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26425, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424]
  have unit : v28254 s i = 0 := by
    simp [v28254, v28078, v28253, v28252, v28251, v28250, v28249, v28248, v28247, v28246, v28086, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, format]
  have operation : v28643 s i = 7 := by
    simp [v28643, v28642, v28641, v28640, v28452, v28451, v28639, v28616, v28615, v28455, v28614, v28613, v28612, v28611, v28610, v28609, v28608, v28607, v28462, v12229, v28638, v28622, v28619, v28617, v28618, v28621, v28620, v8207, v28637, v28628, v28625, v28623, v28624, v28627, v28626, v8322, v28636, v28635, v28633, v28630, v28629, v28632, v28631, v28634, v12225, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, format, unit]
  have kind1 : v28010 s i = 0 := by
    simp [v28010, v28009, v28008, v28007, v27998, v27996, v27997, v24, v28006, v28003, v28000, v27999, v28002, v28001, v28005, v28004, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, format, unit, operation]
  have kind2 : v28050 s i = 1 := by
    simp [v28050, v28049, v28048, v28047, v28044, v28041, v28038, v28037, v28040, v28039, v28043, v28042, v28046, v28045, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, format, unit, operation, kind1]
  have write : v28897 s i = 1 := by
    simp [v28897, v28896, v28895, v28894, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_0_i s i format, write⟩
#print axioms idu_immediate_0_and_decode

theorem idu_immediate_1_add_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .add (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 64 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 19 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 1 := by
    simp [v26916, v26913, v26915, v26914, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v26917, normal, unitOverride, opOverride, hv26916]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28263, normal, unitOverride, opOverride, hv26916, format]
  have operation : v28836 s i = 64 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v12968, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_add_decode

theorem idu_immediate_1_slt_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .slt (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 2 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 8211 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8211) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 8211) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 1 := by
    simp [v26926, v26923, v26925, v26924, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v26927, normal, unitOverride, opOverride, hv26916, hv26921, hv26926]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28265, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, format]
  have operation : v28836 s i = 2 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28652, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_slt_decode

theorem idu_immediate_1_sltu_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .sltu (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 3 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 12307 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 12307) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 1 := by
    simp [v26931, v26928, v26930, v26929, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v26932, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28266, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, format]
  have operation : v28836 s i = 3 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28653, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_sltu_decode

theorem idu_immediate_1_xor_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .xor (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 4 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 16403 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 16403) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 1 := by
    simp [v26936, v26933, v26935, v26934, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v26937, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28267, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, format]
  have operation : v28836 s i = 4 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28654, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_xor_decode

theorem idu_immediate_1_or_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .or (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 6 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 24595 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 24595) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 1 := by
    simp [v26946, v26943, v26945, v26944, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v26947, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28269, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, format]
  have operation : v28836 s i = 6 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28656, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_or_decode

theorem idu_immediate_1_and_decode (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsImmediateALU .and (v26223 s i)) :
    v28438 s i = 0 ∧ v28836 s i = 7 ∧ v28027 s i = 0 ∧ v28066 s i = 1 ∧
      v29230 s i = immediateI (v26223 s i) ∧ v28903 s i = 1 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 28691 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 28691) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 1 := by
    simp [v26951, v26948, v26950, v26949, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v26952, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951]
  have unit : v28438 s i = 0 := by
    simp [v28438, v28262, v28437, v28436, v28435, v28434, v28433, v28432, v28431, v28430, v28270, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, format]
  have operation : v28836 s i = 7 := by
    simp [v28836, v28835, v28834, v28833, v28647, v28646, v28832, v28809, v28808, v28650, v28807, v28806, v28805, v28804, v28803, v28802, v28801, v28800, v28657, v12229, v28831, v28815, v28812, v28810, v28811, v28814, v28813, v8207, v28830, v28821, v28818, v28816, v28817, v28820, v28819, v8322, v28829, v28828, v28826, v28823, v28822, v28825, v28824, v28827, v12225, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, format, unit]
  have kind1 : v28027 s i = 0 := by
    simp [v28027, v28026, v28025, v28024, v28015, v28013, v28014, v24, v28023, v28020, v28017, v28016, v28019, v28018, v28022, v28021, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, format, unit, operation]
  have kind2 : v28066 s i = 1 := by
    simp [v28066, v28065, v28064, v28063, v28060, v28057, v28054, v28053, v28056, v28055, v28059, v28058, v28062, v28061, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, format, unit, operation, kind1]
  have write : v28903 s i = 1 := by
    simp [v28903, v28902, v28901, v28900, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, format, unit, operation, kind1, kind2]
  exact ⟨unit, operation, kind1, kind2, idu_immediate_1_i s i format, write⟩
#print axioms idu_immediate_1_and_decode

end NutShellProofs
