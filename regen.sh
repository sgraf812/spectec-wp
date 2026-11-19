#!/usr/bin/env bash
# Rebuild SpecTec, regenerate SpecTecWP/Wasm.lean (the model) and SpecTecWP/Interp.lean (its
# interpreter) from the full Wasm 3.0 spec, and elaborate both.
# Usage: regen.sh [log]
set -u
ROOT=$(cd "$(dirname "$0")" && pwd)
LOG=${1:-$ROOT/.regen.log}
cd "$ROOT/spectec/spectec"
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 1500 \
  nix-shell "$ROOT/shell.nix" --run 'dune build src/exe-spectec/main.exe 2>&1 | head -40' 2>&1 | grep -v 'Nix search'
(cd test-lean4 && ../_build/default/src/exe-spectec/main.exe ../../specification/wasm-3.0/*.spectec --lean4 \
  --lean4-import SpecTecWP.Wasm -o "$ROOT/SpecTecWP/Wasm.lean" "$ROOT/SpecTecWP/Interp.lean" 2>&1 | tail -2)
cd "$ROOT"
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 2400 \
  lake build SpecTecWP.Wasm > "$LOG" 2>&1
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 2400 \
  lake env lean -DmaxErrors=100000 SpecTecWP/Interp.lean >> "$LOG" 2>&1
echo "$(wc -l < SpecTecWP/Wasm.lean) lines, $(grep -cE 'error(\([a-zA-Z.]+\))?:' "$LOG") errors"
grep -oE 'error(\([a-zA-Z.]+\))?: (\(kernel\) )?[A-Za-z` ]{3,30}' "$LOG" | sort | uniq -c | sort -rn | head -8
