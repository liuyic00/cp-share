import Proofs.LoadAddress
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedVariables false
def loadData_v716 (kind : BitVec 3) (address response : BitVec 32) : BitVec 3 := BitVec.ofNat 3 5
def loadData_v717 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := if (loadData_v716 kind address response) = kind then 1 else 0
def loadData_v4 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def loadData_v225 (kind : BitVec 3) (address response : BitVec 32) : BitVec 24 := BitVec.ofNat 24 0
def loadData_v720 (kind : BitVec 3) (address response : BitVec 32) : BitVec 7 := BitVec.ofNat 7 0
def loadData_v721 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 1 1 address
def loadData_v722 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := ((loadData_v720 kind address response) ++ (loadData_v721 kind address response))
def loadData_v723 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.ofNat 8 4
def loadData_v724 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.shiftLeft (loadData_v722 kind address response) (loadData_v723 kind address response).toNat
def loadData_v725 (kind : BitVec 3) (address response : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def loadData_v261 (kind : BitVec 3) (address response : BitVec 32) : BitVec 3 := BitVec.ofNat 3 0
def loadData_v726 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 0 1 address
def loadData_v727 (kind : BitVec 3) (address response : BitVec 32) : BitVec 4 := ((loadData_v261 kind address response) ++ (loadData_v726 kind address response))
def loadData_v728 (kind : BitVec 3) (address response : BitVec 32) : BitVec 4 := BitVec.ofNat 4 3
def loadData_v729 (kind : BitVec 3) (address response : BitVec 32) : BitVec 4 := BitVec.shiftLeft (loadData_v727 kind address response) (loadData_v728 kind address response).toNat
def loadData_v730 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := ((loadData_v725 kind address response) ++ (loadData_v729 kind address response))
def loadData_v731 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := ((loadData_v724 kind address response) ||| (loadData_v730 kind address response))
def loadData_v732 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v225 kind address response) ++ (loadData_v731 kind address response))
def loadData_v733 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v732 kind address response).toNat
def loadData_v734 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.extractLsb' 0 8 (loadData_v733 kind address response)
def loadData_v735 (kind : BitVec 3) (address response : BitVec 32) : BitVec 9 := ((loadData_v4 kind address response) ++ (loadData_v734 kind address response))
def loadData_v736 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 8 1 (loadData_v735 kind address response)
def loadData_v737 (kind : BitVec 3) (address response : BitVec 32) : BitVec 24 := BitVec.replicate 24 (loadData_v736 kind address response)
def loadData_v738 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := ((loadData_v737 kind address response) ++ (loadData_v735 kind address response))
def loadData_v22 (kind : BitVec 3) (address response : BitVec 32) : BitVec 3 := BitVec.ofNat 3 4
def loadData_v739 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := if (loadData_v22 kind address response) = kind then 1 else 0
def loadData_v740 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 (loadData_v733 kind address response)
def loadData_v741 (kind : BitVec 3) (address response : BitVec 32) : BitVec 17 := ((loadData_v4 kind address response) ++ (loadData_v740 kind address response))
def loadData_v742 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 16 1 (loadData_v741 kind address response)
def loadData_v743 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.replicate 16 (loadData_v742 kind address response)
def loadData_v744 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := ((loadData_v743 kind address response) ++ (loadData_v741 kind address response))
def loadData_v200 (kind : BitVec 3) (address response : BitVec 32) : BitVec 3 := BitVec.ofNat 3 3
def loadData_v745 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := if (loadData_v200 kind address response) = kind then 1 else 0
def loadData_v746 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.extractLsb' 0 8 (loadData_v733 kind address response)
def loadData_v747 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 7 1 (loadData_v746 kind address response)
def loadData_v748 (kind : BitVec 3) (address response : BitVec 32) : BitVec 25 := BitVec.replicate 25 (loadData_v747 kind address response)
def loadData_v749 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := ((loadData_v748 kind address response) ++ (loadData_v746 kind address response))
def loadData_v26 (kind : BitVec 3) (address response : BitVec 32) : BitVec 3 := BitVec.ofNat 3 2
def loadData_v750 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := if (loadData_v26 kind address response) = kind then 1 else 0
def loadData_v751 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 (loadData_v733 kind address response)
def loadData_v752 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 15 1 (loadData_v751 kind address response)
def loadData_v753 (kind : BitVec 3) (address response : BitVec 32) : BitVec 17 := BitVec.replicate 17 (loadData_v752 kind address response)
def loadData_v754 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := ((loadData_v753 kind address response) ++ (loadData_v751 kind address response))
def loadData_v755 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := ((loadData_v4 kind address response) ++ response)
def loadData_v756 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := if (loadData_v750 kind address response) = 1 then (loadData_v754 kind address response) else (loadData_v755 kind address response)
def loadData_v757 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := if (loadData_v745 kind address response) = 1 then (loadData_v749 kind address response) else (loadData_v756 kind address response)
def loadData_v758 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := if (loadData_v739 kind address response) = 1 then (loadData_v744 kind address response) else (loadData_v757 kind address response)
def loadData_v759 (kind : BitVec 3) (address response : BitVec 32) : BitVec 33 := if (loadData_v717 kind address response) = 1 then (loadData_v738 kind address response) else (loadData_v758 kind address response)
def loadData_v3 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ofNat 32 0
def loadData_v2104 (kind : BitVec 3) (address response : BitVec 32) : BitVec 27 := BitVec.ofNat 27 0
def loadData_v2183 (kind : BitVec 3) (address response : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def loadData_v2184 (kind : BitVec 3) (address response : BitVec 32) : BitVec 5 := ((loadData_v2183 kind address response) ++ (loadData_v261 kind address response))
def loadData_v2185 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2104 kind address response) ++ (loadData_v2184 kind address response))
def loadData_v2186 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v2185 kind address response).toNat
def loadData_v2187 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v3 kind address response) ++ (loadData_v2186 kind address response))
def loadData_v2129 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := BitVec.ofNat 64 255
def loadData_v2188 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v2187 kind address response) &&& (loadData_v2129 kind address response))
def loadData_v2189 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.extractLsb' 0 8 (loadData_v2188 kind address response)
def loadData_v2190 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 7 1 (loadData_v2189 kind address response)
def loadData_v2191 (kind : BitVec 3) (address response : BitVec 32) : BitVec 24 := BitVec.ofNat 24 16777215
def loadData_v2192 (kind : BitVec 3) (address response : BitVec 32) : BitVec 24 := if (loadData_v2190 kind address response) = 1 then (loadData_v2191 kind address response) else (loadData_v225 kind address response)
def loadData_v2193 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2192 kind address response) ++ (loadData_v2189 kind address response))
def loadData_v2166 (kind : BitVec 3) (address response : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def loadData_v2167 (kind : BitVec 3) (address response : BitVec 32) : BitVec 5 := ((loadData_v2166 kind address response) ++ (loadData_v261 kind address response))
def loadData_v2168 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2104 kind address response) ++ (loadData_v2167 kind address response))
def loadData_v2169 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v2168 kind address response).toNat
def loadData_v2170 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v3 kind address response) ++ (loadData_v2169 kind address response))
def loadData_v2114 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := BitVec.ofNat 64 65535
def loadData_v2171 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v2170 kind address response) &&& (loadData_v2114 kind address response))
def loadData_v2172 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 (loadData_v2171 kind address response)
def loadData_v2173 (kind : BitVec 3) (address response : BitVec 32) : BitVec 1 := BitVec.extractLsb' 15 1 (loadData_v2172 kind address response)
def loadData_v2174 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.ofNat 16 65535
def loadData_v2100 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.ofNat 16 0
def loadData_v2175 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := if (loadData_v2173 kind address response) = 1 then (loadData_v2174 kind address response) else (loadData_v2100 kind address response)
def loadData_v2176 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2175 kind address response) ++ (loadData_v2172 kind address response))
def loadData_v2146 (kind : BitVec 3) (address response : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def loadData_v2147 (kind : BitVec 3) (address response : BitVec 32) : BitVec 5 := ((loadData_v2146 kind address response) ++ (loadData_v261 kind address response))
def loadData_v2148 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2104 kind address response) ++ (loadData_v2147 kind address response))
def loadData_v2149 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v2148 kind address response).toNat
def loadData_v2150 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v3 kind address response) ++ (loadData_v2149 kind address response))
def loadData_v2151 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := BitVec.ofNat 64 4294967295
def loadData_v2152 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v2150 kind address response) &&& (loadData_v2151 kind address response))
def loadData_v2153 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (loadData_v2152 kind address response)
def loadData_v2124 (kind : BitVec 3) (address response : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def loadData_v2125 (kind : BitVec 3) (address response : BitVec 32) : BitVec 5 := ((loadData_v2124 kind address response) ++ (loadData_v261 kind address response))
def loadData_v2126 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2104 kind address response) ++ (loadData_v2125 kind address response))
def loadData_v2127 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v2126 kind address response).toNat
def loadData_v2128 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v3 kind address response) ++ (loadData_v2127 kind address response))
def loadData_v2130 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v2128 kind address response) &&& (loadData_v2129 kind address response))
def loadData_v2131 (kind : BitVec 3) (address response : BitVec 32) : BitVec 8 := BitVec.extractLsb' 0 8 (loadData_v2130 kind address response)
def loadData_v2132 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v225 kind address response) ++ (loadData_v2131 kind address response))
def loadData_v2109 (kind : BitVec 3) (address response : BitVec 32) : BitVec 2 := BitVec.extractLsb' 0 2 address
def loadData_v2110 (kind : BitVec 3) (address response : BitVec 32) : BitVec 5 := ((loadData_v2109 kind address response) ++ (loadData_v261 kind address response))
def loadData_v2111 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2104 kind address response) ++ (loadData_v2110 kind address response))
def loadData_v2112 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := BitVec.ushiftRight response (loadData_v2111 kind address response).toNat
def loadData_v2113 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v3 kind address response) ++ (loadData_v2112 kind address response))
def loadData_v2115 (kind : BitVec 3) (address response : BitVec 32) : BitVec 64 := ((loadData_v2113 kind address response) &&& (loadData_v2114 kind address response))
def loadData_v2116 (kind : BitVec 3) (address response : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 (loadData_v2115 kind address response)
def loadData_v2117 (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 := ((loadData_v2100 kind address response) ++ (loadData_v2116 kind address response))
def dutLoadData (kind : BitVec 3) (address response : BitVec 32) : BitVec 32 :=
  BitVec.extractLsb' 0 32 (loadData_v759 kind address response)

theorem dut_load_data_cone (s : State) (i : Inputs)
    (sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 1) :
    v765 s i = dutLoadData s.g4.r130_ndut_5Fdpath_5Fld_5Ftype
      s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu (v719 s i) := by
  change v765 s i = BitVec.extractLsb' 0 32 (v759 s i)
  simp [v765, v764, v763, v762, v761, v707, v709, v715, v155, v38, v42, sel]

theorem reference_load_lb_cone (s : State) (i : Inputs) :
    v2193 s i = loadData_v2193 0 (v2095 s i) (v719 s i) := rfl
#print axioms reference_load_lb_cone
theorem reference_load_lh_cone (s : State) (i : Inputs) :
    v2176 s i = loadData_v2176 0 (v2095 s i) (v719 s i) := rfl
#print axioms reference_load_lh_cone
theorem reference_load_lw_cone (s : State) (i : Inputs) :
    v2153 s i = loadData_v2153 0 (v2095 s i) (v719 s i) := rfl
#print axioms reference_load_lw_cone
theorem reference_load_lbu_cone (s : State) (i : Inputs) :
    v2132 s i = loadData_v2132 0 (v2095 s i) (v719 s i) := rfl
#print axioms reference_load_lbu_cone
theorem reference_load_lhu_cone (s : State) (i : Inputs) :
    v2117 s i = loadData_v2117 0 (v2095 s i) (v719 s i) := rfl
#print axioms reference_load_lhu_cone
#print axioms dut_load_data_cone
end RiscvMiniProofs
