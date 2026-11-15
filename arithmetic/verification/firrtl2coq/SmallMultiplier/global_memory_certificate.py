#!/usr/bin/env python3
from pathlib import Path
import json
H=Path(__file__).resolve().parent;g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
out=['From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.','From SmallMultiplier Require Import GlobalStable.']
for k in g['order']:
 if g['nodes'][k]['kind'].startswith('sync'):continue
 n=idx[k];out +=[f'Lemma global_memory_{n} old : eval_hfexpr_with_memory empty_memory_map global_expr_{n} old old = eval_hfexpr global_expr_{n} old old. Proof. reflexivity. Qed.']
(H/'GlobalMemory.v').write_text('\n'.join(out)+'\n')
