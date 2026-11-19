#!/usr/bin/env bash
# Rebuild SpecTec, regenerate SpecTecWP/Wasm.lean (the model), SpecTecWP/Interp.lean (its
# interpreter) and SpecTecWP/WasmWf.lean (its well-formedness lemmas) from the full Wasm 3.0
# spec, and elaborate them. A well-formedness lemma whose generated proof fails is listed in
# SpecTecWP/WasmWf.skip and only stated; the script regenerates until WasmWf.lean elaborates.
# Usage: regen.sh [log]
set -u
ROOT=$(cd "$(dirname "$0")" && pwd)
LOG=${1:-$ROOT/.regen.log}
SKIP=$ROOT/SpecTecWP/WasmWf.skip
touch "$SKIP"
cd "$ROOT/spectec/spectec"
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 1500 \
  nix-shell "$ROOT/shell.nix" --run 'dune build src/exe-spectec/main.exe 2>&1 | head -40' 2>&1 | grep -v 'Nix search'
generate() {
  (cd "$ROOT/spectec/spectec/test-lean4" && ../_build/default/src/exe-spectec/main.exe \
    ../../specification/wasm-3.0/*.spectec --lean4 --lean4-import SpecTecWP.Wasm \
    --lean4-wf-skip "$SKIP" \
    -o "$ROOT/SpecTecWP/Wasm.lean" "$ROOT/SpecTecWP/Interp.lean" "$ROOT/SpecTecWP/WasmWf.lean" 2>&1 | tail -2)
}
generate
cd "$ROOT"
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 2400 \
  lake build SpecTecWP.Wasm > "$LOG" 2>&1
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 2400 \
  lake env lean -DmaxErrors=100000 SpecTecWP/Interp.lean >> "$LOG" 2>&1
echo "model and interpreter: $(grep -cE 'error(\([a-zA-Z.]+\))?:' "$LOG") errors"
# Well-formedness lemmas: skip the failing ones until the file elaborates.
for round in $(seq 1 24); do
  systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 3000 \
    lake env lean -DmaxErrors=100000 SpecTecWP/WasmWf.lean > "$LOG.wf" 2>&1
  failed=$(python3 -I "$ROOT/scripts/wf_failures.py" "$LOG.wf" SpecTecWP/WasmWf.lean)
  if [ -z "$failed" ]; then break; fi
  printf '%s\n' $failed >> "$SKIP"
  sort -u -o "$SKIP" "$SKIP"
  echo "round $round: skipping $(wc -l < "$SKIP") lemmas"
  generate
done
echo "well-formedness lemmas: $(grep -c '^theorem' SpecTecWP/WasmWf.lean) proved, $(grep -c '^def' SpecTecWP/WasmWf.lean) stated"
