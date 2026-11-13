"""Rebuild only the Lean proof files explicitly pinned as generated artifacts."""
from pathlib import Path
import shutil
import subprocess
import sys

ORDER = {
    'lean': ['array-rows', 'array-capture', 'array-padding', 'array-output',
             'array-compressors', 'array-tree', 'array-tree-input', 'array-tree-output', 'array-hold'],
    'lean-hierarchical': ['hierarchical-array-selectors', 'hierarchical-array-capture',
                         'hierarchical-array-children', 'hierarchical-array-tree'],
}


def generate(root, staging, backends, manifest):
    source = root / 'scripts/lean-proof-generators'
    scripts = staging / 'scripts/lean-proof-generators'
    shutil.copytree(source, scripts)
    (staging / 'verification/build/lean-hierarchical').mkdir(parents=True, exist_ok=True)
    outputs = []
    for backend in backends:
        if backend not in ORDER:
            continue
        prefix = f'verification/{backend}/Proofs/'
        # Generators read reusable/manual lemmas but never overwrite them in the checkout.
        for name in manifest['files']:
            if name.startswith(prefix):
                target = staging / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(root / name, target)
        (staging / prefix).mkdir(parents=True, exist_ok=True)
        for name in ORDER[backend]:
            subprocess.run([sys.executable, str(scripts / f'prove-{name}.py')], check=True)
        outputs.extend(name for name in manifest['generated_files'] if name.startswith(prefix))
    return outputs
