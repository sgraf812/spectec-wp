# spectec-wp: `Std.WP` for the SpecTec Wasm model

A `Std.WP.WP` instance for the Lean 4 model of WebAssembly 3.0 that SpecTec generates, and an
adequacy proof of that model against the Talos interpreter on a fragment.
`SpecTecWP/Wasm.lean` is the model, generated from every file of `specification/wasm-3.0`,
with the reduction relation `Step : config → config → Prop`.

## Build

```
lake build SpecTecWP Adequacy.Straight
```

Toolchain: `leanprover/lean4:nightly-2026-11-08`. The libraries `Interpreter` and `WasmWP`
are symbolic links into `~/code/lean/talos`, a checkout of
[Talos](https://github.com/cajal-technologies/talos) with its `wp/` package (the `Std.WP`
instance for the Talos interpreter). They are needed only for `Adequacy`; adjust the links to
your checkout.

## Regenerate the model

The generator is the Lean 4 backend of SpecTec on the branch `lean4-fixes` of
[sgraf812/spectec](https://github.com/sgraf812/spectec/tree/lean4-fixes), a fork of
`Wasm-DSL/spectec`: Joachim Breitner's `lean4-wip` commit on top of `rocq-backend`, ported to
the current IL and fixed after two reviews. Check it out as `spectec/` next to this README.
`shell.nix` provides OCaml.

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
| `SpecTecWP/Redex.lean` | `Step.redex_pure`, `Step.redex_read`: a step of a redex of a pure or reading instruction is a `Step_pure` or `Step_read` step of a suffix. |
| `SpecTecWP/Exits.lean` | Trap and exception configurations, `Safe.trap_inv`, `Safe.throw_inv`, and the sequencing law `Code.wp_append`. |
| `SpecTecWP/Instr.lean`, `InstrLocal.lean` | Weakest preconditions of the straight-line instructions. |
| `SpecTecWP/Regression.lean` | Facts of the specification that earlier versions of the model contradicted. |
| `Adequacy/Translate.lean` | The translation from Talos values, frames and instructions. |
| `Adequacy/Arith.lean` | The integer operations of Talos and of the model agree. |
| `Adequacy/Straight.lean` | `adequacy_straight`. |

## Semantics of `wp`

`wp is Q E z vs` holds when `wf_config` of the configuration `vs.reverse ++ is` in state `z`
implies `Safe Q E` of that configuration. `Safe Q E c` is the least predicate with three rules:

* a configuration of values `vs` satisfies `Safe` if `Q z vs`;
* an exit configuration (`br`, `return`, `throw_ref` or `trap`, possibly followed by more
  instructions) with exit `e` satisfies `Safe` if `E e z`;
* any other configuration satisfies `Safe` if it steps and every successor satisfies `Safe`.

The quantification over successors is demonic, because `memory.grow` and `table.grow` can fail
in every state. Every `Step` rule requires `wf_config` of its source and its target, so every
configuration that a step reaches is well-formed.

## Adequacy

`Adequacy.adequacy_straight`: for a Talos program `p` of the fragment, if Talos establishes the
postcondition `R` and the exception postcondition `epost` (which rejects `Invalid`), then every
SpecTec reduction of the translation `tp p` from the corresponding configuration terminates and
satisfies the translated postconditions. The fragment is `i32`/`i64` constants, `add`, `sub`,
`mul`, `and`, `or`, `xor`, `eqz`, `eq`, `ne`, `lt_u`, `lt_s`, `local.get`, `local.set`,
`local.tee`, `drop`, `nop` and `unreachable`.
