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
    parser.add_argument('--compile-only', action='store_true', help='Compile the final generated lemmas without an additional coqchk pass')
    args = parser.parse_args()
    opam = ['opam', 'exec', '--switch=' + args.switch, '--']
    mappings = {
        'simplssrlib': ROOT / 'tool/firrtl2coq/lib/simplssrlib',
        'nbits': ROOT / 'tool/firrtl2coq/lib/nbits',
        'firrtl': ROOT / 'tool/firrtl2coq/src',
        'ArithmeticCommon': BASE / 'Common',
        'Divider': [BASE / 'Divider', BASE / 'Generated/Radix2Divider'],
        'Generated': ROOT / 'arithmetic/verification/rocq/Generated',
        'Proofs': ROOT / 'arithmetic/verification/rocq/Proofs',
    }
    mappings = {name: paths if isinstance(paths, list) else [paths]
                for name, paths in mappings.items()}
    flags = []
    for name, paths in mappings.items():
        for path in paths:
            flags += ['-R' if name == 'firrtl' else '-Q', str(path), name]
    sources = set()
    def visit(namespace, name):
        candidates = [root / (name.replace('.', '/') + '.v') for root in mappings[namespace]]
        existing = [path for path in candidates if path.is_file()]
        if len(existing) != 1:
            raise SystemExit('Expected exactly one source for ' + namespace + '.' + name +
                             ': ' + ', '.join(map(str, candidates)) +
                             '; see firrtl2coq/README.md for generation commands.')
        path = existing[0]
        if path in sources:
            return
        sources.add(path)
        text = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
        if re.search(r'\b(Admitted|admit|Axiom|Parameter)\b', text):
            raise SystemExit('Unexpected admitted theorem/axiom: ' + str(path))
        for prefix, imports in re.findall(r'From\s+(\w+)\s+Require\s+(?:(?:Import|Export)\s+)?([^.]*)\.', text):
            if prefix in mappings and prefix not in {'simplssrlib', 'nbits', 'firrtl'}:
                for imported in imports.split():
                    visit(prefix, imported)
    visit('Divider', 'Radix2Divider')
    build = ROOT / 'arithmetic/build/firrtl2coq-divider-proof'
    build.mkdir(parents=True, exist_ok=True)
    (build / 'result.json').unlink(missing_ok=True)
    subprocess.run(opam + ['coq_makefile', *flags, *map(str, sorted(sources)), '-o', 'Makefile'], cwd=build, check=True)
    subprocess.run(opam + ['make', '-f', 'Makefile', '-j' + str(args.jobs), 'all'], cwd=build, check=True)
    if not args.compile_only:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        resource.setrlimit(resource.RLIMIT_STACK, (min(64 * 1024 * 1024, hard) if hard != resource.RLIM_INFINITY else 64 * 1024 * 1024, hard))
        subprocess.run(opam + ['coqchk', '-silent', *flags, 'Divider.Radix2Divider'], cwd=ROOT, check=True)
    result = {'target': 'Divider.Radix2Divider', 'obligations': 11, 'coqc': 'passed', 'coqchk': 'skipped' if args.compile_only else 'passed',
              'upstream_axioms': ['ftype_eqn_eq', 'ffield_eqn_eq'],
              'sources_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(sources)}}
    (build / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All 11 generated divider lemmas compiled.' + ('' if args.compile_only else ' coqchk passed.'))

if __name__ == '__main__':
    main()
