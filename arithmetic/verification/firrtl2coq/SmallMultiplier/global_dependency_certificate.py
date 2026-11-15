#!/usr/bin/env python3
"""Proof dependency metadata over original instance paths; does not rewrite ASTs."""
from pathlib import Path
import re,json,runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'stable_certificate.py'));model=x['model'];form=x['form'];ports=x['ports']
nodes={};leaves=set();instances={};types={}
def key(path,id,field=None):return '/'.join(map(str,path))+':'+str(id)+(':'+str(field) if field is not None else '')
def refs(path,expr):
 return sorted(set(key(path,int(m[2])) if m[2] else key(path,int(m[3]),int(m[4])) for m in x['rf'].finditer(expr)))
def add(k,kind,deps,expr=None):
 if k in nodes:raise ValueError('duplicate writer '+k)
 nodes[k]={'kind':kind,'deps':deps}
 if expr is not None:nodes[k]['expr']=expr

def visit(path,mid):
 instances['/'.join(map(str,path))]=mid
 body=model.split(f'Definition generated_module_{mid}_stmts_0')[1].split(f'Definition generated_module_{mid} :')[0]
 regs=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+)',body)))
 leaves.update(key(path,i) for i in regs)
 for p,d,_,_ in ports[mid]:
  if d=='input' and not path:leaves.add(key(path,p))
 for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',body):
  f=form(body,m.start());expr=f[m.end()-m.start():-1];add(key(path,int(m[1])),'node',refs(path,expr),expr)
 for m in re.finditer(r'\(@Sfcnct VarOrder.T ',body):
  f=form(body,m.start());r=form(f,m.end()-m.start());expr=f[m.end()-m.start()+len(r)+1:-1]
  scalar=re.fullmatch(r'\(@Eid VarOrder.T (\d+)\)',r)
  port=re.fullmatch(r'\(@Esubfield VarOrder.T \(@Eid VarOrder.T (\d+)\) (\d+)\)',r)
  if scalar:
   if int(scalar[1]) not in regs:add(key(path,int(scalar[1])),'connect',refs(path,expr),expr)
  elif port:add(key(path,int(port[1]),int(port[2])),'portconnect',refs(path,expr),expr)
  else:raise ValueError(r)
 for inst,childmid in re.findall(r'\(@Sinst VarOrder.T (\d+) (\d+)\)',body):
  inst=int(inst);childmid=int(childmid);childpath=path+[inst]
  visit(childpath,childmid)
  for p,d,_,_ in ports[childmid]:
   if d=='input':add(key(childpath,p),'syncinput',[key(path,inst,p)])
   else:add(key(path,inst,p),'syncoutput',[key(childpath,p)])
visit([],3)
ranks={k:0 for k in leaves};ordered=[];active=set()
def rank(k):
 if k in ranks:return ranks[k]
 if k in active:raise ValueError('combinational cycle '+k)
 if k not in nodes:raise ValueError('missing writer '+k)
 active.add(k);ranks[k]=1+max((rank(d) for d in nodes[k]['deps']),default=0);active.remove(k);ordered.append(k);return ranks[k]
for k in nodes:rank(k)
out={'instances':instances,'leaves':sorted(leaves),'nodes':nodes,'ranks':ranks,'order':ordered}
(H/'global-dependencies.json').write_text(json.dumps(out,indent=2)+'\n')
print('global instances',len(instances),'scalar/field writes',len(nodes),'leaves',len(leaves),'max rank',max(ranks.values()))
print('result rank',ranks[':6'],'product assertion',ranks[':412'])
