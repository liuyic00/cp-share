From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_5 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 1000 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_1000 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1001 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1002 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1003 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1004 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1005 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1006 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1007 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1008 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1009 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1010 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1011 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1012 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1013 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1014 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1015 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1016 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1017 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1018 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1019 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1020 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1021 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1022 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1023 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1024 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1025 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1026 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1027 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1028 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1029 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1030 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1031 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1032 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1033 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1034 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1035 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1036 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1037 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1038 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1039 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1040 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1041 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1042 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1043 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1044 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1045 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1046 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1047 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1048 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1049 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1050 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1051 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1052 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1053 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1054 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1055 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1056 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1057 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1058 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1059 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1060 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1061 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1062 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1063 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1064 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1065 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1066 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1067 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1068 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1069 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1070 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1071 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1072 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1073 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1074 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1075 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1076 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1077 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1078 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1079 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1080 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1081 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1082 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1083 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1084 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1085 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1086 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1087 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1088 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1089 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1090 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1091 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1092 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1093 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1094 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1095 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1096 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1097 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1098 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1099 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1100 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1101 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1102 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1103 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1104 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1105 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1106 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1107 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1108 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1109 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1110 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1111 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1112 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1113 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1114 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1115 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1116 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1117 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1118 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1119 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1120 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1121 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1122 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1123 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1124 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1125 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1126 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1127 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1128 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1129 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1130 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1131 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1132 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1133 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1134 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1135 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1136 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1137 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1138 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1139 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1140 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1141 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1142 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1143 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1144 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1145 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1146 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1147 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1148 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1149 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1150 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1151 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1152 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1153 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1154 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1155 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1156 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1157 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1158 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1159 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1160 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1161 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1162 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1163 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1164 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1165 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1166 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1167 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1168 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1169 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1170 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1171 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1172 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1173 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1174 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1175 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1176 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1177 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1178 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1179 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1180 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1181 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1182 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1183 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1184 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1185 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1186 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1187 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1188 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1189 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1190 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1191 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1192 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1193 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1194 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1195 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1196 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1197 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1198 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1199 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_5 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 1000 200).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1003 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1007 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1010 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1013 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1021 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1025 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1028 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1031 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1039 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1043 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1046 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1049 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1057 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1061 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1064 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1067 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1070 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1081 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1085 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1088 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1091 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1094 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1105 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1109 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1112 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1115 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1123 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1127 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1130 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1133 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1141 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1145 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1148 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1151 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1159 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1163 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1166 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1169 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1177 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1181 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1184 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1187 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1190 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.
