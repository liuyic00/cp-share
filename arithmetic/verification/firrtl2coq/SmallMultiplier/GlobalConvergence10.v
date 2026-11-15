From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_10 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 2000 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_2000 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2001 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2002 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2003 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2004 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2005 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2006 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2007 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2008 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2009 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2010 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2011 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2012 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2013 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2014 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2015 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2016 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2017 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2018 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2019 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2020 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2021 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2022 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2023 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2024 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2025 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2026 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2027 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2028 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2029 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2030 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2031 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2032 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2033 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2034 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2035 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2036 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2037 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2038 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2039 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2040 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2041 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2042 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2043 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2044 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2045 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2046 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2047 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2048 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2049 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2050 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2051 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2052 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2053 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2054 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2055 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2056 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2057 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2058 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2059 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2060 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2061 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2062 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2063 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2064 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2065 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2066 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2067 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2068 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2069 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2070 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2071 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2072 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2073 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2074 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2075 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2076 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2077 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2078 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2079 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2080 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2081 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2082 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2083 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2084 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2085 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2086 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2087 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2088 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2089 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2090 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2091 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2092 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2093 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2094 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2095 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2096 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2097 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2098 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2099 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2100 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2101 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2102 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2103 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2104 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2105 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2106 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2107 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2108 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2109 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2110 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2111 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2112 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2113 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2114 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2115 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2116 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2117 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2118 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2119 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2120 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2121 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2122 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2123 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2124 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2125 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2126 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2127 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2128 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2129 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2130 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2131 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2132 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2133 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2134 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2135 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2136 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2137 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2138 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2139 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2140 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2141 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2142 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2143 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2144 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2145 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2146 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2147 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2148 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2149 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2150 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2151 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2152 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2153 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2154 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2155 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2156 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2157 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2158 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2159 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2160 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2161 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2162 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2163 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2164 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2165 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2166 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2167 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2168 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2169 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2170 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2171 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2172 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2173 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2174 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2175 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2176 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2177 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2178 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2179 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2180 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2181 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2182 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2183 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2184 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2185 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2186 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2187 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2188 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2189 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2190 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2191 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2192 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2193 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2194 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2195 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2196 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2197 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2198 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2199 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_10 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 2000 200).
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
