#!/usr/bin/env python3
"""Recheck completed multiplier proof components using the local Coq kernel."""
from pathlib import Path
import argparse,subprocess
H=Path(__file__).resolve().parent
R=H.parents[3]
p=argparse.ArgumentParser();p.add_argument('--firrtl',type=Path);a=p.parse_args()
flags=['opam','exec','--switch=firrtl2coq','--','coqc','-Q','tool/firrtl2coq/lib/simplssrlib','simplssrlib','-Q','tool/firrtl2coq/lib/nbits','nbits','-R','tool/firrtl2coq/src','firrtl','-Q','arithmetic/verification/firrtl2coq/Common','ArithmeticCommon','-Q',str(H),'SmallMultiplier']
def coq(name,log=None):
 print('Checking '+name,flush=True)
 with open(log or R/f'arithmetic/build/small-{name.lower()}.log','w') as f:subprocess.run(flags+[str(H/(name+'.v'))],cwd=R,stdout=f,stderr=f,check=True)
(R/'arithmetic/build').mkdir(exist_ok=True)
if a.firrtl:subprocess.run(['python3',str(H/'prepare.py'),'--firrtl',str(a.firrtl.resolve())],cwd=R,check=True)
coq('Model');coq('Widths',R/'arithmetic/build/small-widths.log')
for name in ['stable_certificate','congruence_certificate','memo_certificate','local_environment_certificate','pass_certificate','stable_front_certificate']:
 subprocess.run(['python3',str(H/(name+'.py'))],cwd=R,check=True)
for name in ['Booth8','Packing8','Compression8','CaptureWiring8','Invariant8','Compressors','WeightedCompressors','NodeFacts','CaptureAST','Stable','Congruence','Memo','LocalEnvironment','NodeCertificateCheck','PassCertificates','StableFront','FrontTable','FrontCheck','StableProduct']:
 coq(name)
print('Component checks passed; this is not yet an arbitrary-step trace theorem.')
