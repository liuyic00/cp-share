From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model NodeFacts.
Local Open Scope N_scope.
Fixpoint connect_expression (id : VarOrder.T) (stmts : hfstmt_seq VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Sfcnct (Eid n) e) rest => if n == id then Some e else connect_expression id rest
 | Qcons _ rest => connect_expression id rest end.
Record capture_entry := { register_id:N; mux_id:N; source_id:N; packed_id:N; bit_index:nat }.
Definition capture_entries := [::
 Build_capture_entry 201 202 72 71 0;
 Build_capture_entry 203 204 108 107 0;
 Build_capture_entry 205 206 73 71 1;
 Build_capture_entry 207 208 109 107 1;
 Build_capture_entry 209 210 74 71 2;
 Build_capture_entry 211 212 110 107 2;
 Build_capture_entry 213 214 145 144 0;
 Build_capture_entry 215 216 75 71 3;
 Build_capture_entry 217 218 111 107 3;
 Build_capture_entry 219 220 146 144 1;
 Build_capture_entry 221 222 76 71 4;
 Build_capture_entry 223 224 112 107 4;
 Build_capture_entry 225 226 147 144 2;
 Build_capture_entry 227 228 181 180 0;
 Build_capture_entry 229 230 77 71 5;
 Build_capture_entry 231 232 113 107 5;
 Build_capture_entry 233 234 148 144 3;
 Build_capture_entry 235 236 182 180 1;
 Build_capture_entry 237 238 78 71 6;
 Build_capture_entry 239 240 114 107 6;
 Build_capture_entry 241 242 149 144 4;
 Build_capture_entry 243 244 183 180 2;
 Build_capture_entry 245 246 199 198 0;
 Build_capture_entry 247 248 79 71 7;
 Build_capture_entry 249 250 115 107 7;
 Build_capture_entry 251 252 150 144 5;
 Build_capture_entry 253 254 184 180 3;
 Build_capture_entry 255 256 200 198 1;
 Build_capture_entry 257 258 80 71 8;
 Build_capture_entry 259 260 116 107 8;
 Build_capture_entry 261 262 151 144 6;
 Build_capture_entry 263 264 185 180 4;
 Build_capture_entry 265 266 81 71 9;
 Build_capture_entry 267 268 117 107 9;
 Build_capture_entry 269 270 152 144 7;
 Build_capture_entry 271 272 186 180 5;
 Build_capture_entry 273 274 82 71 10;
 Build_capture_entry 275 276 118 107 10;
 Build_capture_entry 277 278 153 144 8;
 Build_capture_entry 279 280 187 180 6;
 Build_capture_entry 281 282 83 71 11;
 Build_capture_entry 283 284 119 107 11;
 Build_capture_entry 285 286 154 144 9;
 Build_capture_entry 287 288 188 180 7;
 Build_capture_entry 289 290 120 107 12;
 Build_capture_entry 291 292 155 144 10;
 Build_capture_entry 293 294 189 180 8;
 Build_capture_entry 295 296 156 144 11;
 Build_capture_entry 297 298 190 180 9;
 Build_capture_entry 299 300 157 144 12;
 Build_capture_entry 301 302 191 180 10;
 Build_capture_entry 303 304 192 180 11].
Definition capture_shape e :=
 connect_expression (register_id e) generated_module_3_stmts_0 = Some (ref (mux_id e)) /\
 top_node (mux_id e) = Some (Emux (ref 4) (ref (source_id e)) (ref (register_id e))) /\
 top_node (source_id e) = Some (Eprim_unop (Uextr (bit_index e) (bit_index e)) (ref (packed_id e))).
Theorem capture_ast_certificate : List.Forall capture_shape capture_entries.
Proof. vm_compute. repeat constructor; reflexivity. Qed.
Lemma capture_mux_value e env enabled fresh old
 (Hshape : capture_shape e)
 (He : VM.find 4 env = Some (Gval (Fuint 1) [::enabled]))
 (Hfresh : VM.find (source_id e) env = Some (Gval (Fuint 1) [::fresh]))
 (Hold : VM.find (register_id e) env = Some (Gval (Fuint 1) [::old])) :
 eval_top_node (mux_id e) env = Some (Gval (Fuint 1) [::if enabled then fresh else old]).
Proof.
 destruct Hshape as [_ [Hmux _]]. unfold eval_top_node. rewrite Hmux.
 cbn [eval_hfexpr_with_memory eval_href_with_memory ref]. rewrite He.
 destruct enabled; change (is_zero [::true]) with false || change (is_zero [::false]) with true;
 cbn; unfold eval_type_of_expr, ref; cbn [type_of_expr' eval_type_of_ref];
 rewrite ?Hfresh ?Hold; cbn; destruct fresh, old; reflexivity.
Qed.
Print Assumptions capture_ast_certificate.
Print Assumptions capture_mux_value.
