# spectec-wp: `Std.WP` for the SpecTec Wasm model

A `Std.WP.WP` instance for the Lean 4 model of WebAssembly 3.0 that SpecTec generates, and an
adequacy proof of that model against the Talos interpreter on a fragment.
`SpecTecWP/Wasm.lean` is the model, generated from every file of `specification/wasm-3.0`,
with the reduction relation `Step : config → config → Prop`.

To verify a program, use the `Std.WP` instance of `SpecTecWP/View.lean` with the `@[spec]`
triples of `SpecTecWP/Specs.lean`: assertions talk about the store, the locals and the stack
of a `VState`, and `vcgen ... with finish` proves the triples. `SpecTecWP/Gcd.lean` is the
worked example. The files before `View.lean` in the tour build the weakest precondition
`Code.wp` over `Step` that the instance rests on.

## Build

```
lake build SpecTecWP Adequacy.Straight
```

Toolchain: `leanprover/lean4:nightly-2026-11-08`. `Adequacy` uses the Talos interpreter and its
`Std.WP` instance (the libraries `Interpreter` and `WasmWP`), which Lake fetches from the `wp/`
package of [sgraf812/talos](https://github.com/sgraf812/talos/tree/vcgen/wp), a fork of
[Talos](https://github.com/cajal-technologies/talos).

## Regenerate the model

The generator is the Lean 4 backend of SpecTec on the branch `lean4-fixes` of
[sgraf812/spectec](https://github.com/sgraf812/spectec/tree/lean4-fixes), a fork of
`Wasm-DSL/spectec`: Joachim Breitner's `lean4-wip` commit on top of `rocq-backend`, ported to
the current IL and fixed after two reviews. Check it out as `spectec/` next to this README.
`shell.nix` provides OCaml.

```
./regen.sh
```

The script builds SpecTec, writes the model `SpecTecWP/Wasm.lean`, the interpreter
`SpecTecWP/Interp.lean` and the well-formedness lemmas `SpecTecWP/WasmWf.lean`, and elaborates
them. It adds each lemma whose generated proof fails to `SpecTecWP/WasmWf.skip` and
regenerates, until `WasmWf.lean` elaborates.

## Tour

| File | Content |
| --- | --- |
| `SpecTecWP/Basic.lean` | Stack encoding (top first), `Exit`, `Safe`, `Code.wp`, `Step.wf_source`/`Step.wf_target`. |
| `SpecTecWP/Decomp.lean` | The left side of every base rule is a redex: values, then one non-value instruction. `trap_instrs` and `throw_ref_instrs` are the two exceptions. |
| `SpecTecWP/Inversion.lean` | `Step.inv`: a step of `ws ++ i :: t` is a step of the redex `ws ++ [i]` followed by `t`, or a trap/`throw_ref` bubble. `Step.frame` is the converse. |
| `SpecTecWP/Redex.lean` | `Step.redex_pure`, `Step.redex_read`: a step of a redex of a pure or reading instruction is a `Step_pure` or `Step_read` step of a suffix. |
| `SpecTecWP/Exits.lean` | Trap and exception configurations, `Safe.trap_inv`, `Safe.throw_inv`, and the sequencing law `Code.wp_append`. |
| `SpecTecWP/Instr.lean`, `InstrLocal.lean` | Weakest preconditions of the straight-line instructions. |
| `SpecTecWP/Label.lean` | `Step.redex_label`: the steps of a label, one `LabelStep` constructor per rule. The configurations without steps. |
| `SpecTecWP/Control.lean` | `Safe.label`: `Safe` of the body of a label gives `Safe` of the label. Weakest preconditions of `block`, `loop`, `br`, `br_if`, and the loop rule `Code.wp_loop_inv` with an invariant and a variant. |
| `SpecTecWP/Locals.lean` | Reading a local after `local.set`, the well-formedness of every local of a well-formed state, and `local.set` without a well-formedness hypothesis. |
| `SpecTecWP/View.lean` | The view: `VState` with the store, the module instance, the locals and the stack over typed values `V`; the representation relation `Rep`, with one representation for every well-formed state; the `WP` instance on `List instr` over `VState`; `transport` from a triple to `Code.wp`; and `wp_view_iff`, the equivalence of `Code.wp` and the view `wp` on represented states. |
| `SpecTecWP/ArithSigned.lean` | `$idiv_` and `$irem_` on signed `i32` values are Talos's `Int.tdiv` and `Int.tmod` on the `Int32` readings, with no result for a zero divisor and for `-2^31 / -1`. |
| `SpecTecWP/Arith.lean` | The integer operations of the model on `UInt32`, including the hand-written built-ins, and `$truncz` of a quotient of naturals. |
| `SpecTecWP/Specs.lean` | `@[spec]` triples over the view for `vcgen`: `nil`, `cons`, `i32`/`i64` constants, `i32.add`/`sub`/`mul`/`rem_u`/`eqz`, `local.get`/`set`, `br`, `br_if`, `block`, and `loop` with an invariant and a variant. |
| `SpecTecWP/Examples.lean` | Programs proved with `vcgen ... with finish`: `(a + b) - b = a` from two locals, and two programs that compute `(x + 1) * (x + 1)` in different ways. |
| `SpecTecWP/Gcd.lean` | Euclid's gcd loop of the Talos examples, proved with `vcgen invariants ... with finish` and the Talos invariant: the result is `Nat.gcd a b`, the store does not change, and the loop terminates. `gcd_spectec` is the same statement about the SpecTec model. |
| `SpecTecWP/Regression.lean` | Facts of the specification that earlier versions of the model contradicted. |
| `SpecTecWP/Interp.lean` | Generated. `interp_Step_io c` lists successors `c'` of the configuration `c`, each with a proof of `Step c c'`; `interp_Step_pure_io` does the same for `Step_pure`. The comment at the end lists the rules the interpreter leaves out. |
| `SpecTecWP/InterpTest.lean` | Evaluations of `interp_Step_pure_io` on single redexes. |
| `SpecTecWP/WasmWf.lean` | Generated. The well-formedness lemmas of the functions: a well-formed input gives a well-formed result. A lemma with a generated proof is a `theorem`; a lemma about an opaque function, or one listed in `SpecTecWP/WasmWf.skip`, is a `def … : Prop` that states it. |
| `Adequacy/Translate.lean` | The translation from Talos values, frames and instructions. |
| `Adequacy/Div.lean` | The `$binop_` results of the four `i32` division and remainder operators, and their traps. |
| `Adequacy/Straight.lean` | `adequacy_straight`. |
| `Adequacy/Differential.lean` | The differential test of the interpreter against Talos. |

## Semantics of `wp`

`Code.wp is Q E z vs` holds when `wf_config` of the configuration `vs.reverse ++ is` in state `z`
implies `Safe Q E` of that configuration. `Safe Q E c` is the least predicate with three rules:

* a configuration of values `vs` satisfies `Safe` if `Q z vs`;
* an exit configuration (`br`, `return`, `throw_ref` or `trap`, possibly followed by more
  instructions) with exit `e` satisfies `Safe` if `E e z`;
* any other configuration satisfies `Safe` if it steps and every successor satisfies `Safe`.

The quantification over successors is demonic, because `memory.grow` and `table.grow` can fail
in every state. Every `Step` rule requires `wf_config` of its source and its target, so every
configuration that a step reaches is well-formed.

The `WP` instance has assertions over a `VState` `s`: the store `s.store`, the module instance
`s.inst`, the locals `s.locals : List (Option V)` and the stack `s.stack : List V`. A value `V`
has one constructor per value of the model; `.i32 a` and `.i64 a` carry `UInt32` and `UInt64`
payloads. `wp is Q E s` holds when `Code.wp is` holds from the SpecTec state and stack that
represent `s`, for the postconditions that hold of the represented `VState` when it satisfies
`Q` or `E`. Every well-formed state and stack has exactly one representation, and
`wp_view_iff` states that the view `wp` of the pullbacks of any postconditions is `Code.wp`.

## Adequacy

`Adequacy.adequacy_straight`: for a Talos program `p` of the fragment, if Talos establishes the
postcondition `R` and the exception postcondition `epost` (which rejects `Invalid`), then every
SpecTec reduction of the translation `tp p` from the corresponding configuration terminates and
satisfies the translated postconditions. The fragment is `i32`/`i64` constants, `add`, `sub`,
`mul`, `div_u`, `div_s`, `rem_u`, `rem_s` (with their traps), `and`, `or`, `xor`, `eqz`, `eq`,
`ne`, `lt_u`, `lt_s`, `local.get`, `local.set`, `local.tee`, `drop`, `nop` and `unreachable`.

## Interpreter and differential test

The Lean backend also generates an interpreter of the model (`--lean4 -o Wasm.lean Interp.lean`).
For a relation `R` and a choice of input arguments, the function `interp_R_<mode>` takes the
inputs and returns a list of outputs, each with a proof of `R`. For example,
`interp_Step_io c : List {c' : config // Step c c'}`. Each rule becomes one function: the inputs
are matched against the conclusion of the rule, and the premises are checked or enumerated in an
order in which their inputs are known. The interpreter is sound by construction. A rule outside
this scheme is left out, so the interpreter can miss a successor; a missed successor shows up as
a stuck configuration in the test.

`lake exe difftest <count> <length> <seed>` generates `count` random well-typed straight-line
programs of `length` instructions over all `i32` and `i64` integer instructions, the locals,
`drop`, `nop` and `unreachable`. It runs each program in Talos and in the interpreter, and
compares the stack, the locals and traps. If a configuration has several successors, they must
all lead to the same outcome.
