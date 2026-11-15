#!/usr/bin/env python3
from pathlib import Path
import re
H=Path(__file__).resolve().parent
s=(H/'Model.v').read_text().split('Definition generated_module_3_stmts_0')[1].split('Definition generated_module_3 :')[0]
items=list(re.finditer(r'\(@(S\w+) VarOrder.T(?: (\d+))?',s))
out=['From Coq Require Import NArith.','From firrtl Require Import HiFirrtl_with_implicit_widths.','From ArithmeticCommon Require Import StatementFacts.','From SmallMultiplier Require Import Model Stable NodeCertificateCheck.']
for pos,m in enumerate(items):
 if m[1]!='Snode' or not 37<=int(m[2])<=198:continue
 n=int(m[2]);out += [f'Lemma pass_node_{n}_certificate : node_certificate {n}%N expr_word_{n} generated_module_3_stmts_0.','Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.']
(H/'PassCertificates.v').write_text('\n'.join(out)+'\n')
