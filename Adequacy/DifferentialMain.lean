import Adequacy.Differential

open Differential

def main (args : List String) : IO UInt32 := do
  let count := (args[0]? >>= String.toNat?).getD 1000
  let len := (args[1]? >>= String.toNat?).getD 10
  let seed := (args[2]? >>= String.toNat?).getD 1
  let r := test count len seed
  IO.println s!"programs: {count}, length: {len}, seed: {seed}"
  IO.println s!"agree: {r.agree} ({r.traps} traps), disagree: {r.failures.length}"
  for (p, talos, spec) in r.failures.take 5 do
    IO.println s!"program: {repr p}\n  Talos:   {repr talos}\n  SpecTec: {repr spec}"
  return if r.failures.isEmpty then 0 else 1
