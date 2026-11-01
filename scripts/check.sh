#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
python3 scripts/palomar/check-lean-sources.py
ruby scripts/palomar/validate-formalization.rb
python3 scripts/check-package.py
python3 scripts/check-generated.py
python3 -S scripts/check_three_colour_threshold.py
lake build
