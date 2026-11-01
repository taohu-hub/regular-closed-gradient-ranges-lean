#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
unset LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT
export PATH="$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
export ELAN_TOOLCHAIN
ELAN_TOOLCHAIN=$(tr -d '\r\n' < lean-toolchain)
elan toolchain install "$ELAN_TOOLCHAIN"
export PATH="$(dirname "$(elan which lean)"):$PATH"
command -v bwrap >/dev/null
command -v nanoda_bin >/dev/null
mkdir -p verification/local
python3 scripts/check_layout.py --self-test | tee verification/local/layout.log
python3 scripts/check_metadata.py | tee verification/local/metadata.log
lake exe cache get
lake build 2>&1 | tee verification/local/build.log
lake comparator --config comparator.json 2>&1 | tee verification/local/comparator.log
.lake/palomar-metadata-venv/bin/python scripts/check_con_ron.py
printf '%s\n' 'PASS: source, metadata, build, axiom audit, statement comparison, Lean kernel and NanoDa checks; advisory con-ron outcome recorded.'
