#!/usr/bin/env python3
"""Regenerate finite geometry in a temporary directory and compare checked-in sources."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

generated_sources = {
    Path('ThreeColour') / name
    for name in ('Data.lean', 'LowerData.lean', 'PhysicalDefs.lean',
                 'RawData.lean', 'ReflectionData.lean', 'RData.lean', 'FrameData.lean')
}
root = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix='four-to-three-generated-') as directory:
    stage = Path(directory)
    (stage / 'scripts').mkdir()
    for name in ('generate_three_colour_lean.py', 'generate_frame_data.py', 'cube_geometry.py'):
        shutil.copy2(root / 'scripts' / name, stage / 'scripts' / name)
    subprocess.run([sys.executable, '-S', str(stage / 'scripts/generate_three_colour_lean.py')], check=True)
    subprocess.run([sys.executable, '-S', str(stage / 'scripts/generate_frame_data.py')], check=True)
    actual_sources = {
        path.relative_to(stage)
        for path in (stage / 'ThreeColour').rglob('*') if path.is_file()
    }
    if actual_sources != generated_sources:
        missing = ', '.join(map(str, sorted(generated_sources - actual_sources))) or 'none'
        unexpected = ', '.join(map(str, sorted(actual_sources - generated_sources))) or 'none'
        raise SystemExit(f'Generated source set differs: missing {missing}; unexpected {unexpected}')
    for relative in sorted(generated_sources):
        if (stage / relative).read_bytes() != (root / relative).read_bytes():
            raise SystemExit(f'Generated source differs: {relative}')
    subprocess.run([sys.executable, '-S', str(root / 'scripts/generate_figure.py'), directory], check=True)
    for name in ('obstruction-figure.tex', 'obstruction-figure.svg', 'bucket-figure.svg'):
        if (stage / name).read_bytes() != (root / 'paper' / name).read_bytes():
            raise SystemExit(f'Generated figure differs: paper/{name}')
print('Finite geometry and figure regeneration agree with checked-in sources.')
