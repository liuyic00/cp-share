from pathlib import Path
import re,json
from functools import lru_cache
R=Path(__file__).resolve().parents[3];data=json.loads((R/'verification/firrtl2coq/Divider/nodes.json').read_text());widths={int(k):v for k,v in data['widths'].items()}
def parse(s):
 toks=re.findall(r'\[::|[()\];]|[^\s()\[\];]+',s);pos=0
 def p():
  nonlocal pos
  t=toks[pos];pos+=1
  if t in ['(','[::']:
   end=')' if t=='(' else ']';r=[] if t=='(' else ['bits']
   while toks[pos]!=end:
    if toks[pos]==';':pos+=1
    else:r.append(p())
   pos+=1;return r
  return t
 out=p();assert pos==len(toks),(s,toks[pos:]);return out

def C(n):return ('c',int(n))
def norm(w,x):
 if x[0]=='c':return C(x[1]%(1<<w))
 if x[0]=='wrap':return norm(min(w,x[1]),x[2]) if w<x[1] else x
 if bound(x)<=w:return x
 return ('wrap',w,x)
@lru_cache(None)
def upper(x):
 if x[0]=='c':return x[1]
 if x[0]=='add':return upper(x[1])+upper(x[2])
 if x[0]=='shl' and x[2][0]=='c':return upper(x[1])<<x[2][1]
 return (1<<bound(x))-1
@lru_cache(None)
def bound(x):
 if x[0]=='c':return max(1,x[1].bit_length())
 if x[0]=='var':return widths[x[1]]
 if x[0]=='wrap':return x[1]
 if x[0]=='add' or (x[0]=='shl' and x[2][0]=='c'):return max(1,upper(x).bit_length())
 if x[0] in ['eq','lt','le','not']:return 1
 if x[0]=='if':return max(bound(x[2]),bound(x[3]))
 if x[0] in ['and','or','xor']:return max(map(bound,x[1:]))
 if x[0]=='shr' and x[2][0]=='c':return max(0,bound(x[1])-x[2][1])
 return 100000

def op(n,*xs):
 if n=='le' and xs[0][0]=='c' and xs[0][1]>0:return op('lt',C(xs[0][1]-1),xs[1])
 if n=='if':
  c,a,b=xs
  if a==b:return a
  if c[0]=='c':return b if c[1]==0 else a
  if a==C(1) and b==C(0):return c
  return (n,*xs)
 if n=='not':
  x=xs[0]
  if x[0]=='not':return x[1]
  if x[0]=='c':return C(1-x[1])
  return(n,x)
 if n in ['and','or','xor','add','eq']:
  xs=tuple(sorted(xs,key=repr))
 if n in ['and','or']:
  flat=[]
  for x in xs:flat+=list(x[1:]) if x[0]==n else [x]
  xs=tuple(sorted(set(flat),key=repr))
  if n=='and' and C(0) in xs:return C(0)
  if n=='or':xs=tuple(x for x in xs if x!=C(0))
  if n=='and' and all(bound(x)<=1 for x in xs):xs=tuple(x for x in xs if x!=C(1))
  if len(xs)==1:return xs[0]
 if n=='xor':
  a,b=xs
  if a==C(0):return b
  if a==b:return C(0)
  if a==C(1) and bound(b)<=1:return op('not',b)
 if n=='add' and xs[0]==C(0):return xs[1]
 if n=='sub' and xs[1]==C(0):return xs[0]
 if n in ['shl','shr']:
  a,b=xs
  if b==C(0) or a==C(0):return a
  if n=='shr' and b[0]=='c':
   if a[0]=='shr' and a[2][0]=='c':return op('shr',a[1],C(a[2][1]+b[1]))
   if a[0]=='wrap':return norm(max(0,a[1]-b[1]),op('shr',a[2],b))
 if n=='eq' and xs[0]==xs[1]:return C(1)
 if n=='eq':
  for c,x in [xs,xs[::-1]]:
   if c in [C(0),C(1)] and bound(x)<=1:return x if c==C(1) else op('not',x)
 if all(x[0]=='c' for x in xs):
  vs=[x[1] for x in xs]
  fn={'add':lambda a,b:a+b,'sub':lambda a,b:a-b,'shl':lambda a,b:a<<b,'shr':lambda a,b:a>>b,'eq':lambda a,b:int(a==b),'lt':lambda a,b:int(a<b),'le':lambda a,b:int(a<=b),'and':lambda a,b:a&b,'or':lambda a,b:a|b,'xor':lambda a,b:a^b,'mul':lambda a,b:a*b}
  if n in fn and len(vs)==2:return C(fn[n](*vs))
 return(n,*xs)
new={i:('var',i) for i in data['inputs']+data['registers']}
newtypes={i:widths[i] for i in new}
def newer(e):
 if e[0]=='@Eref':
  id=int(e[2][2]);return widths[id],new[id]
 if e[0]=='@Econst':
  w=int(e[2][1]);val=sum((x=='true')<<k for k,x in enumerate(e[3][1:]));return w,C(val)
 if e[0]=='@Ecast':return newer(e[3])
 if e[0]=='@Emux':
  _,c=newer(e[2]);wa,a=newer(e[3]);wb,b=newer(e[4]);return max(wa,wb),op('if',c,a,b)
 if e[0]=='@Eprim_unop':
  oper=e[2];w,a=newer(e[3]);n=oper[0] if isinstance(oper,list) else oper
  if n=='Uextr':h,l=map(int,oper[1:]);return h+1-l,norm(h+1-l,op('shr',a,C(l)))
  if n=='Utail':d=int(oper[1]);return w-d,norm(w-d,a)
  if n=='Upad':return max(w,int(oper[1])),a
  if n=='Uhead':d=int(oper[1]);return d,norm(d,op('shr',a,C(w-d)))
  if n=='Uorr':return 1,op('not',op('eq',a,C(0)))
  if n=='Uandr':return 1,op('eq',a,C((1<<w)-1))
  if n=='Unot':return w,op('not',a) if w==1 else op('xor',a,C((1<<w)-1))
  if n=='Uneg':return w+1,norm(w+1,op('sub',C(0),a))
  if n=='Ushr':d=int(oper[1]);return max(1,w-d),op('shr',a,C(d))
  raise ValueError(e)
 if e[0]=='@Eprim_binop':
  oper=e[2];wa,a=newer(e[3]);wb,b=newer(e[4]);n=oper[0] if isinstance(oper,list) else oper
  if n=='Bcomp':
   cmp=oper[1];n={'Beq':'eq','Bneq':'eq','Blt':'lt','Bleq':'le','Bgt':'lt','Bgeq':'le'}[cmp]
   if cmp in ['Bgt','Bgeq']:a,b=b,a
   v=op(n,a,b)
   return 1,op('not',v) if cmp=='Bneq' else v
  w={'Badd':max(wa,wb)+1,'Bsub':max(wa,wb)+1,'Bmul':wa+wb,'Bcat':wa+wb,'Bdshl':wa+(1<<wb)-1,'Bdshr':wa,'Band':max(wa,wb),'Bor':max(wa,wb),'Bxor':max(wa,wb)}[n]
  if n=='Bcat':return w,norm(w,op('add',op('shl',a,C(wb)),b))
  opname={'Badd':'add','Bsub':'sub','Bmul':'mul','Bdshl':'shl','Bdshr':'shr','Band':'and','Bor':'or','Bxor':'xor'}[n]
  return w,norm(w,op(opname,a,b))
 raise ValueError(e)
for id in data['order']:
 w,e=newer(parse(data['expressions'][str(id)]));new[id]=e
old={}
fields={f:('var',id) for id,f in [(13,'r0_nstate'),(18,'r1_ndivBy0Reg'),(20,'r2_nshiftReg'),(33,'r3_naSignReg'),(38,'r4_nqSignReg'),(40,'r5_nbReg'),(43,'r6_naValx2Reg'),(46,'r7_nctrlReg_5FisW'),(47,'r8_nctrlReg_5FisHi'),(51,'r9_ncnt_5Fvalue'),(445,'r10_nhistoryValid'),(446,'r11_npreviousState'),(447,'r12_npreviousCount'),(475,'r13_nwasStalled'),(476,'r14_npreviousOutput'),(1,'nreset'),(3,'nio_5Fin_5Fvalid'),(4,'nio_5Fin_5Fbits_5Fsrc_5F0'),(5,'nio_5Fin_5Fbits_5Fsrc_5F1'),(6,'nio_5Fin_5Fbits_5Fsrc_5F2'),(7,'nio_5Fout_5Fready'),(10,'nctrl_5Fsign'),(11,'nctrl_5FisW'),(12,'nctrl_5FisHi')]}
def older(e):
 if isinstance(e,str):return C(e)
 if len(e)==1:return older(e[0])
 if '+' in e:
  j=e.index('+');return op('add',older(e[:j]),older(e[j+1:]))
 n=e[0]
 if n=='word':return norm(int(e[1]),older(e[2]))
 if n in fields:return fields[n]
 if re.fullmatch(r'v\d+',n):return old[int(n[1:])]
 if n=='le' and xs[0][0]=='c' and xs[0][1]>0:return op('lt',C(xs[0][1]-1),xs[1])
 if n=='if':
  j=e.index('then');k=e.index('else');return op('if',older(e[1:j]),older(e[j+1:k]),older(e[k+1:]))
 if n=='repeatWord':return ('repeat',int(e[1].split('%')[0]),int(e[2]),older(e[3]))
 if n=='negb':return op('not',older(e[1]))
 opname={'Z.eqb':'eq','Z.ltb':'lt','Z.leb':'le','Z.land':'and','Z.lor':'or','Z.lxor':'xor','Z.add':'add','Z.sub':'sub','Z.mul':'mul','Z.shiftl':'shl','Z.shiftr':'shr'}[n]
 return op(opname,*map(older,e[1:]))
for line in (R/'verification/rocq/Generated/Radix2Divider.v').read_text().splitlines():
 m=re.match(r'Definition v(\d+).* := (.*)\.',line)
 if m:old[int(m[1])]=older(parse(m[2]))
lookup={}
for id,e in old.items():lookup.setdefault(e,[]).append(id)
matches={id:lookup[e] for id,e in new.items() if e in lookup}
print('MATCHES',len(matches),'/',len(data['order']))
# Candidate matches are checked by generated Coq proofs, never trusted.
(Path(__file__).resolve().parent/'node-matches.json').write_text(json.dumps(matches,indent=2))
