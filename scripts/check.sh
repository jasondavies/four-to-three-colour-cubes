#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
python3 scripts/check-package.py
python3 scripts/check-generated.py
python3 -S scripts/check_three_colour_threshold.py
python3 -S scripts/check_frames.py
bash scripts/check-near-frames.sh
python3 -S research/thin-cuboids/audit.py
python3 -S research/thin-cuboids/strip_audit.py
python3 -S research/cuboids/review_geometry.py
lake build
