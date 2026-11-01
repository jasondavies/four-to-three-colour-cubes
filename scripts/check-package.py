#!/usr/bin/env python3
"""Check dependency pins and separation of comparator statements from proofs."""
from pathlib import Path
import json
import re
import tomllib
root = Path(__file__).resolve().parents[1]
config = tomllib.loads((root / 'lakefile.toml').read_text())
manifest = json.loads((root / 'lake-manifest.json').read_text())
upstream = next(d for d in config['require'] if d['name'] == 'macmahon_min_universal_sets')
locked = next(d for d in manifest['packages'] if d['name'] == upstream['name'])
if not re.fullmatch('[0-9a-f]{40}', upstream['rev']) or locked['rev'] != upstream['rev']:
    raise SystemExit('The geometry dependency must be pinned to the same full commit in both files.')
for dependency in manifest['packages']:
    if dependency['type'] != 'git':
        raise SystemExit('Local-path dependency in published manifest.')
# Scan code rather than documentation containing the forbidden words.
for path in [root / 'ThreeColour.lean', root / 'Solution.lean', *(root / 'ThreeColour').rglob('*.lean')]:
    text = path.read_text()
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by)\b', text):
        raise SystemExit(f'Forbidden proof declaration in {path.relative_to(root)}')
    if re.search(r'\bimport\s+Challenge\b', text):
        raise SystemExit('Proof library imports the challenge.')
challenge = (root / 'Challenge.lean').read_text()
comp = json.loads((root / 'comparator.json').read_text())
if challenge.count('by sorry') != len(comp['theorem_names']):
    raise SystemExit('Unexpected challenge hole count.')
if re.findall(r'^(?:public )?import (.+)$', challenge, re.M) != ['Mathlib']:
    raise SystemExit('Independent challenge must import only Mathlib.')
print('Package pins, proof-source scan and comparator separation passed.')
