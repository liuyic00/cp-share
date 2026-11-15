From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_0 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 0 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_0 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_3 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_4 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_5 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_6 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_7 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_8 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_9 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_10 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_11 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_12 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_13 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_14 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_15 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_16 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_17 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_18 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_19 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_20 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_21 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_22 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_23 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_24 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_25 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_26 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_27 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_28 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_29 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_30 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_31 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_32 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_33 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_34 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_35 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_36 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_37 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_38 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_39 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_40 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_41 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_42 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_43 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_44 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_45 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_46 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_47 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_48 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_49 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_50 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_51 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_52 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_53 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_54 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_55 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_56 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_57 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_58 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_59 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_60 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_61 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_62 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_63 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_64 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_65 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_66 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_67 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_68 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_69 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_70 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_71 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_72 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_73 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_74 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_75 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_76 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_77 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_78 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_79 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_80 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_81 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_82 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_83 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_84 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_85 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_86 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_87 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_88 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_89 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_90 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_91 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_92 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_93 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_94 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_95 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_96 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_97 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_98 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_99 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_100 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_101 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_102 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_103 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_104 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_105 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_106 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_107 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_108 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_109 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_110 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_111 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_112 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_113 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_114 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_115 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_116 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_117 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_118 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_119 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_120 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_121 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_122 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_123 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_124 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_125 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_126 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_127 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_128 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_129 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_130 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_131 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_132 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_133 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_134 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_135 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_136 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_137 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_138 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_139 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_140 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_141 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_142 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_143 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_144 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_145 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_146 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_147 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_148 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_149 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_150 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_151 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_152 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_153 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_154 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_155 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_156 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_157 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_158 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_159 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_160 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_161 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_162 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_163 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_164 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_165 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_166 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_167 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_168 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_169 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_170 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_171 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_172 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_173 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_174 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_175 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_176 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_177 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_178 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_179 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_180 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_181 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_182 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_183 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_184 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_185 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_186 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_187 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_188 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_189 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_190 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_191 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_192 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_193 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_194 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_195 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_196 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_197 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_198 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_199 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_0 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 0 200).
Proof.
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
Qed.
