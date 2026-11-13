#!/usr/bin/env python3
"""Convenience entry; each task also has an independent scripts/check.py."""
import argparse
from pathlib import Path
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('tasks', nargs='*', choices=['riscv-mini', 'nutshell', 'arithmetic'])
p.add_argument('--sources', action='store_true')
p.add_argument('--build', action='store_true')
a = p.parse_args()
for task in a.tasks or ['riscv-mini', 'nutshell', 'arithmetic']:
    command = [sys.executable, str(Path(__file__).resolve().parent.parent/task/'scripts/check.py')]
    command += ['--sources'] if a.sources else []
    command += ['--build'] if a.build else []
    subprocess.run(command, check=True)
