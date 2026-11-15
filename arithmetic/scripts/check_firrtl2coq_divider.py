#!/usr/bin/env python3
"""Build the exact generated divider obligations and independently check them."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'arithmetic/verification/firrtl2coq'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--switch', default='firrtl2coq')
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    opam = ['opam', 'exec', '--switch=' + args.switch, '--']
    mappings = {
        'simplssrlib': ROOT / 'tool/firrtl2coq/lib/simplssrlib',
        'nbits': ROOT / 'tool/firrtl2coq/lib/nbits',
        'firrtl': ROOT / 'tool/firrtl2coq/src',
        'ArithmeticCommon': BASE / 'Common',
        'Divider': BASE / 'Divider',
        'ArithmeticFIRRTL': BASE / 'Generated',
        'Generated': ROOT / 'arithmetic/verification/rocq/Generated',
        'Proofs': ROOT / 'arithmetic/verification/rocq/Proofs',
    }
    flags = []
    for name, path in mappings.items():
        flags += ['-R' if name == 'firrtl' else '-Q', str(path), name]
    sources = set()
    def visit(namespace, name):
        path = mappings[namespace] / (name.replace('.', '/') + '.v')
        if path in sources:
            return
        if not path.exists():
            raise SystemExit('Missing source: ' + str(path) + '; see firrtl2coq/README.md for generation commands.')
        sources.add(path)
        text = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
        if re.search(r'\b(Admitted|admit|Axiom|Parameter)\b', text):
            raise SystemExit('Unexpected admitted theorem/axiom: ' + str(path))
        for prefix, imports in re.findall(r'From\s+(\w+)\s+Require\s+(?:Import|Export)\s+([^.]*)\.', text):
            if prefix in mappings and prefix not in {'simplssrlib', 'nbits', 'firrtl'}:
                for imported in imports.split():
                    visit(prefix, imported)
    visit('Divider', 'Proof')
    build = ROOT / 'arithmetic/build/firrtl2coq-divider-proof'
    build.mkdir(parents=True, exist_ok=True)
    subprocess.run(opam + ['coq_makefile', *flags, *map(str, sorted(sources)), '-o', 'Makefile'], cwd=build, check=True)
    subprocess.run(opam + ['make', '-f', 'Makefile', '-j' + str(args.jobs), 'all'], cwd=build, check=True)
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (min(64 * 1024 * 1024, hard) if hard != resource.RLIM_INFINITY else 64 * 1024 * 1024, hard))
    subprocess.run(opam + ['coqchk', '-silent', *flags, 'Divider.Proof'], cwd=ROOT, check=True)
    result = {'target': 'Divider.Proof', 'obligations': 11, 'coqchk': 'passed',
              'upstream_axioms': ['ftype_eqn_eq', 'ffield_eqn_eq'],
              'sources_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(sources)}}
    (build / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All 11 exact generated divider obligations built and checked by coqchk.')

if __name__ == '__main__':
    main()
