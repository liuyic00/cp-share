import Proofs.Pipeline
set_option linter.unusedVariables false
namespace RiscvMiniProofs
open nCoreSoc
def alu_v725 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 0
def alu_v7841 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v725 op a b) then 1 else 0
def alu_v7793 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 1
def alu_v7842 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7793 op a b) then 1 else 0
def alu_v7843 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := ((alu_v7841 op a b) ||| (alu_v7842 op a b))
def alu_v4 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def alu_v7890 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v4 op a b) ++ a)
def alu_v7891 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 0 1 op
def alu_v7892 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := BitVec.ofNat 33 0
def alu_v8035 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v4 op a b) ++ b)
def alu_v8036 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v7892 op a b) - (alu_v8035 op a b))
def alu_v8037 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (alu_v8036 op a b)
def alu_v8038 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v7891 op a b) = 1 then (alu_v8037 op a b) else b
def alu_v8039 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v4 op a b) ++ (alu_v8038 op a b))
def alu_v8040 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v7890 op a b) + (alu_v8039 op a b))
def alu_v8041 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (alu_v8040 op a b)
def alu_v7785 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 5
def alu_v8042 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7785 op a b) then 1 else 0
def alu_v7786 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 7
def alu_v8043 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7786 op a b) then 1 else 0
def alu_v8044 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := ((alu_v8042 op a b) ||| (alu_v8043 op a b))
def alu_v2274 (op : BitVec 4) (a b : BitVec 32) : BitVec 31 := BitVec.ofNat 31 0
def alu_v8045 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 a
def alu_v8046 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 b
def alu_v8047 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if (alu_v8045 op a b) = (alu_v8046 op a b) then 1 else 0
def alu_v8048 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (alu_v8041 op a b)
def alu_v8049 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 1 1 op
def alu_v8050 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 b
def alu_v8051 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 a
def alu_v8052 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if (alu_v8049 op a b) = 1 then (alu_v8050 op a b) else (alu_v8051 op a b)
def alu_v8053 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if (alu_v8047 op a b) = 1 then (alu_v8048 op a b) else (alu_v8052 op a b)
def alu_v8054 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v2274 op a b) ++ (alu_v8053 op a b))
def alu_v7792 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 9
def alu_v8055 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7792 op a b) then 1 else 0
def alu_v7791 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 8
def alu_v8056 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7791 op a b) then 1 else 0
def alu_v8057 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := ((alu_v8055 op a b) ||| (alu_v8056 op a b))
def alu_v8058 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 0 1 op
def alu_v8059 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 3 1 op
def alu_v32 (op : BitVec 4) (a b : BitVec 32) : BitVec 2 := BitVec.ofNat 2 0
def alu_v2012 (op : BitVec 4) (a b : BitVec 32) : BitVec 8 := BitVec.ofNat 8 0
def alu_v2100 (op : BitVec 4) (a b : BitVec 32) : BitVec 16 := BitVec.ofNat 16 0
def alu_v8060 (op : BitVec 4) (a b : BitVec 32) : BitVec 16 := BitVec.extractLsb' 16 16 a
def alu_v8061 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v2100 op a b) ++ (alu_v8060 op a b))
def alu_v8062 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 65535
def alu_v8063 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8061 op a b) &&& (alu_v8062 op a b))
def alu_v8064 (op : BitVec 4) (a b : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 a
def alu_v8065 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8064 op a b) ++ (alu_v2100 op a b))
def alu_v8066 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4294901760
def alu_v8067 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8065 op a b) &&& (alu_v8066 op a b))
def alu_v8068 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8063 op a b) ||| (alu_v8067 op a b))
def alu_v8069 (op : BitVec 4) (a b : BitVec 32) : BitVec 24 := BitVec.extractLsb' 8 24 (alu_v8068 op a b)
def alu_v8070 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v2012 op a b) ++ (alu_v8069 op a b))
def alu_v8071 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16711935
def alu_v8072 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8070 op a b) &&& (alu_v8071 op a b))
def alu_v8073 (op : BitVec 4) (a b : BitVec 32) : BitVec 24 := BitVec.extractLsb' 0 24 (alu_v8068 op a b)
def alu_v8074 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8073 op a b) ++ (alu_v2012 op a b))
def alu_v8075 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4278255360
def alu_v8076 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8074 op a b) &&& (alu_v8075 op a b))
def alu_v8077 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8072 op a b) ||| (alu_v8076 op a b))
def alu_v8078 (op : BitVec 4) (a b : BitVec 32) : BitVec 28 := BitVec.extractLsb' 4 28 (alu_v8077 op a b)
def alu_v8079 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v725 op a b) ++ (alu_v8078 op a b))
def alu_v8080 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 252645135
def alu_v8081 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8079 op a b) &&& (alu_v8080 op a b))
def alu_v8082 (op : BitVec 4) (a b : BitVec 32) : BitVec 28 := BitVec.extractLsb' 0 28 (alu_v8077 op a b)
def alu_v8083 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8082 op a b) ++ (alu_v725 op a b))
def alu_v8084 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4042322160
def alu_v8085 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8083 op a b) &&& (alu_v8084 op a b))
def alu_v8086 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8081 op a b) ||| (alu_v8085 op a b))
def alu_v8087 (op : BitVec 4) (a b : BitVec 32) : BitVec 30 := BitVec.extractLsb' 2 30 (alu_v8086 op a b)
def alu_v8088 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v32 op a b) ++ (alu_v8087 op a b))
def alu_v8089 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 858993459
def alu_v8090 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8088 op a b) &&& (alu_v8089 op a b))
def alu_v8091 (op : BitVec 4) (a b : BitVec 32) : BitVec 30 := BitVec.extractLsb' 0 30 (alu_v8086 op a b)
def alu_v8092 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8091 op a b) ++ (alu_v32 op a b))
def alu_v8093 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 3435973836
def alu_v8094 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8092 op a b) &&& (alu_v8093 op a b))
def alu_v8095 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8090 op a b) ||| (alu_v8094 op a b))
def alu_v8096 (op : BitVec 4) (a b : BitVec 32) : BitVec 31 := BitVec.extractLsb' 1 31 (alu_v8095 op a b)
def alu_v8097 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v4 op a b) ++ (alu_v8096 op a b))
def alu_v8098 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1431655765
def alu_v8099 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8097 op a b) &&& (alu_v8098 op a b))
def alu_v8100 (op : BitVec 4) (a b : BitVec 32) : BitVec 31 := BitVec.extractLsb' 0 31 (alu_v8095 op a b)
def alu_v8101 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8100 op a b) ++ (alu_v4 op a b))
def alu_v8102 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 2863311530
def alu_v8103 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8101 op a b) &&& (alu_v8102 op a b))
def alu_v8104 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8099 op a b) ||| (alu_v8103 op a b))
def alu_v8105 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8059 op a b) = 1 then a else (alu_v8104 op a b)
def alu_v8106 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := BitVec.extractLsb' 31 1 (alu_v8105 op a b)
def alu_v8107 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := ((alu_v8058 op a b) &&& (alu_v8106 op a b))
def alu_v8108 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v8107 op a b) ++ (alu_v8105 op a b))
def alu_v608 (op : BitVec 4) (a b : BitVec 32) : BitVec 28 := BitVec.ofNat 28 0
def alu_v8109 (op : BitVec 4) (a b : BitVec 32) : BitVec 5 := BitVec.extractLsb' 0 5 b
def alu_v8110 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := ((alu_v608 op a b) ++ (alu_v8109 op a b))
def alu_v8111 (op : BitVec 4) (a b : BitVec 32) : BitVec 33 := BitVec.sshiftRight (alu_v8108 op a b) (alu_v8110 op a b).toNat
def alu_v8112 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (alu_v8111 op a b)
def alu_v7790 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 6
def alu_v8113 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7790 op a b) then 1 else 0
def alu_v8114 (op : BitVec 4) (a b : BitVec 32) : BitVec 16 := BitVec.extractLsb' 16 16 (alu_v8112 op a b)
def alu_v8115 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v2100 op a b) ++ (alu_v8114 op a b))
def alu_v8116 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8115 op a b) &&& (alu_v8062 op a b))
def alu_v8117 (op : BitVec 4) (a b : BitVec 32) : BitVec 16 := BitVec.extractLsb' 0 16 (alu_v8112 op a b)
def alu_v8118 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8117 op a b) ++ (alu_v2100 op a b))
def alu_v8119 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8118 op a b) &&& (alu_v8066 op a b))
def alu_v8120 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8116 op a b) ||| (alu_v8119 op a b))
def alu_v8121 (op : BitVec 4) (a b : BitVec 32) : BitVec 24 := BitVec.extractLsb' 8 24 (alu_v8120 op a b)
def alu_v8122 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v2012 op a b) ++ (alu_v8121 op a b))
def alu_v8123 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8122 op a b) &&& (alu_v8071 op a b))
def alu_v8124 (op : BitVec 4) (a b : BitVec 32) : BitVec 24 := BitVec.extractLsb' 0 24 (alu_v8120 op a b)
def alu_v8125 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8124 op a b) ++ (alu_v2012 op a b))
def alu_v8126 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8125 op a b) &&& (alu_v8075 op a b))
def alu_v8127 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8123 op a b) ||| (alu_v8126 op a b))
def alu_v8128 (op : BitVec 4) (a b : BitVec 32) : BitVec 28 := BitVec.extractLsb' 4 28 (alu_v8127 op a b)
def alu_v8129 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v725 op a b) ++ (alu_v8128 op a b))
def alu_v8130 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8129 op a b) &&& (alu_v8080 op a b))
def alu_v8131 (op : BitVec 4) (a b : BitVec 32) : BitVec 28 := BitVec.extractLsb' 0 28 (alu_v8127 op a b)
def alu_v8132 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8131 op a b) ++ (alu_v725 op a b))
def alu_v8133 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8132 op a b) &&& (alu_v8084 op a b))
def alu_v8134 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8130 op a b) ||| (alu_v8133 op a b))
def alu_v8135 (op : BitVec 4) (a b : BitVec 32) : BitVec 30 := BitVec.extractLsb' 2 30 (alu_v8134 op a b)
def alu_v8136 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v32 op a b) ++ (alu_v8135 op a b))
def alu_v8137 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8136 op a b) &&& (alu_v8089 op a b))
def alu_v8138 (op : BitVec 4) (a b : BitVec 32) : BitVec 30 := BitVec.extractLsb' 0 30 (alu_v8134 op a b)
def alu_v8139 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8138 op a b) ++ (alu_v32 op a b))
def alu_v8140 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8139 op a b) &&& (alu_v8093 op a b))
def alu_v8141 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8137 op a b) ||| (alu_v8140 op a b))
def alu_v8142 (op : BitVec 4) (a b : BitVec 32) : BitVec 31 := BitVec.extractLsb' 1 31 (alu_v8141 op a b)
def alu_v8143 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v4 op a b) ++ (alu_v8142 op a b))
def alu_v8144 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8143 op a b) &&& (alu_v8098 op a b))
def alu_v8145 (op : BitVec 4) (a b : BitVec 32) : BitVec 31 := BitVec.extractLsb' 0 31 (alu_v8141 op a b)
def alu_v8146 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8145 op a b) ++ (alu_v4 op a b))
def alu_v8147 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8146 op a b) &&& (alu_v8102 op a b))
def alu_v8148 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := ((alu_v8144 op a b) ||| (alu_v8147 op a b))
def alu_v7789 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 2
def alu_v8149 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7789 op a b) then 1 else 0
def alu_v8150 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := (a &&& b)
def alu_v7788 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 3
def alu_v8151 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7788 op a b) then 1 else 0
def alu_v8152 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := (a ||| b)
def alu_v7787 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 4
def alu_v8153 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7787 op a b) then 1 else 0
def alu_v8154 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := (a ^^^ b)
def alu_v7795 (op : BitVec 4) (a b : BitVec 32) : BitVec 4 := BitVec.ofNat 4 10
def alu_v8155 (op : BitVec 4) (a b : BitVec 32) : BitVec 1 := if op = (alu_v7795 op a b) then 1 else 0
def alu_v8156 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8155 op a b) = 1 then a else b
def alu_v8157 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8153 op a b) = 1 then (alu_v8154 op a b) else (alu_v8156 op a b)
def alu_v8158 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8151 op a b) = 1 then (alu_v8152 op a b) else (alu_v8157 op a b)
def alu_v8159 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8149 op a b) = 1 then (alu_v8150 op a b) else (alu_v8158 op a b)
def alu_v8160 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8113 op a b) = 1 then (alu_v8148 op a b) else (alu_v8159 op a b)
def alu_v8161 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8057 op a b) = 1 then (alu_v8112 op a b) else (alu_v8160 op a b)
def alu_v8162 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v8044 op a b) = 1 then (alu_v8054 op a b) else (alu_v8161 op a b)
def alu_v8163 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := if (alu_v7843 op a b) = 1 then (alu_v8041 op a b) else (alu_v8162 op a b)
def alu_v8164 (op : BitVec 4) (a b : BitVec 32) : BitVec 32 := (alu_v8163 op a b)
abbrev circuitAlu := alu_v8164
theorem circuit_alu_eq (s : State) (i : Inputs) :
    v8164 s i = circuitAlu (v7840 s i) (v7889 s i) (v8034 s i) := by rfl
#print axioms circuit_alu_eq
end RiscvMiniProofs
