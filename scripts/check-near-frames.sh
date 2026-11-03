#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
audit_directory=$(mktemp -d "${TMPDIR:-/tmp}/four-to-three-near-XXXXXX")
trap 'rm -rf "$audit_directory"' EXIT
"${CXX:-c++}" -std=c++20 -O3 -Wall -Wextra -Wpedantic \
  "$repository_root/scripts/check_near_frames.cpp" -o "$audit_directory/check_near_frames"
"$audit_directory/check_near_frames"
