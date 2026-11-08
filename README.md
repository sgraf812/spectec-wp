# spectec-wp: `Std.WP` for the SpecTec Wasm model

A `Std.WP.WP` instance for the Lean 4 model of WebAssembly 3.0 that SpecTec generates.
`SpecTecWP/Wasm.lean` is that model: 19,639 lines, generated from every file of
`specification/wasm-3.0`, with the reduction relation `Step : config → config → Prop`.

## Build

```
lake build
```

Toolchain: `leanprover/lean4:nightly-2026-11-08`.

## Regenerate the model

The generator is the Lean 4 backend of SpecTec on the local branch `lean4-update` of
`spectec/` (a clone of `Wasm-DSL/spectec`, based on `rocq-backend`). `shell.nix` provides OCaml.

```
./regen.sh
```

The script builds SpecTec, writes `SpecTecWP/Wasm.lean` and elaborates it.

## Tour

| File | Content |
| --- | --- |
| `SpecTecWP/Basic.lean` | Stack encoding (top first), `Exit`, `Safe`, `Code.wp`, the `WP` instance, `Step.wf_source`/`Step.wf_target`. |
| `SpecTecWP/Decomp.lean` | The left side of every base rule is a redex: values, then one non-value instruction. `trap_instrs` and `throw_ref_instrs` are the two exceptions. |
| `SpecTecWP/Inversion.lean` | `Step.inv`: a step of `ws ++ i :: t` is a step of the redex `ws ++ [i]` followed by `t`, or a trap/`throw_ref` bubble. `Step.frame` is the converse. |

## Semantics of `wp`

`wp is Q E z vs` holds when `wf_config` of the configuration `vs.reverse ++ is` in state `z`
implies `Safe Q E` of that configuration. `Safe Q E c` is the least predicate with three rules:

* a configuration of values `vs` satisfies `Safe` if `Q z vs`;
* an exit configuration (`br`, `return`, `throw_ref`, `trap`) with exit `e` satisfies `Safe` if
  `E e z`;
* any other configuration satisfies `Safe` if it steps and every successor satisfies `Safe`.

The quantification over successors is demonic, because `memory.grow` and `table.grow` can fail
in every state. Every `Step` rule requires `wf_config` of its source and its target, so every
configuration that a step reaches is well-formed.
