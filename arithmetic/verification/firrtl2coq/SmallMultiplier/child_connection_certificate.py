#!/usr/bin/env python3
from pathlib import Path
import re
H=Path(__file__).resolve().parent
p=H/'ChildConnections.v';s=p.read_text().split('(* Generated child output certificates. *)')[0]
s+='(* Generated child output certificates. *)\n'
model=(H/'Model.v').read_text()
for mid in range(3):
 body=model.split(f'Definition generated_module_{mid}_stmts_0')[1].split(f'Definition generated_module_{mid} :')[0]
 stmts=list(re.finditer(r'\(@(S\w+) VarOrder.T',body))
 for pos,m in enumerate(stmts):
  q=re.match(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T (\d+)\) \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',body[m.start():])
  if not q:continue
  target,source=map(int,q.groups());name=f'child{mid}_output{target}'
  s+=f'''Lemma {name}_certificate : framed_write_certificate {target}
 (@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source}))) generated_module_{mid}_stmts_0.
Proof. unfold generated_module_{mid}_stmts_0.
 do {pos} (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma {name}_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find {target} before = Some value)
 (source : VM.find {source} old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_{mid}_stmts_0 = Some after) :
 VM.find {target} after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact {name}_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
'''
p.write_text(s)
