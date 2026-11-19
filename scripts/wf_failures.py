"""Print the names of the theorems of a generated WasmWf.lean that have an error in a Lean log.

Usage: wf_failures.py LOG WasmWf.lean
"""
import re
import sys

log = open(sys.argv[1]).read()
src = open(sys.argv[2]).read().split('\n')
starts = [(i + 1, line.split()[1]) for i, line in enumerate(src) if line.startswith('theorem ')]
failed = []
for m in re.finditer(r'WasmWf\.lean:(\d+):\d+: error', log):
    line = int(m.group(1))
    name = None
    for start, n in starts:
        if start <= line:
            name = n
    if name and name not in failed:
        failed.append(name)
print('\n'.join(failed))
