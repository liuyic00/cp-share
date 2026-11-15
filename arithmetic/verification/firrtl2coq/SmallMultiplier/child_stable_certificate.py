#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
for mid in range(3):
 runpy.run_path(str(H/'stable_certificate.py'),init_globals={'MODULE_ID':mid,'OUTPUT_PREFIX':f'Child{mid}','WIDTH_LOG':f'small-child{mid}widths.log'})
