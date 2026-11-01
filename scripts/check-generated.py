#!/usr/bin/env python3
"""Regenerate finite geometry in a temporary directory and compare checked-in sources."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
root = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix='four-to-three-generated-') as directory:
    stage = Path(directory)
    shutil.copytree(root / 'ThreeColour', stage / 'ThreeColour')
    (stage / 'scripts').mkdir()
    for name in ('generate_three_colour_lean.py', 'cube_geometry.py'):
        shutil.copy2(root / 'scripts' / name, stage / 'scripts' / name)
    subprocess.run([sys.executable, '-S', str(stage / 'scripts/generate_three_colour_lean.py')], check=True)
    for path in (stage / 'ThreeColour').rglob('*.lean'):
        relative = path.relative_to(stage)
        if path.read_bytes() != (root / relative).read_bytes():
            raise SystemExit(f'Generated source differs: {relative}')
print('Finite geometry regeneration agrees with checked-in Lean sources.')
