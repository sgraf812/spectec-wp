import SpecTecWP.Wasm
import Std.WP

/-!
# `Std.WP.WP` instance for the SpecTec Wasm model

`SpecTecWP.Wasm` is the Lean 4 output of SpecTec for the WebAssembly 3.0 specification. Its
operational semantics is the relation `Step : config → config → Prop`. A configuration
`.mk_config z is` pairs a state `z` with one instruction sequence `is`, and the operand stack is
the prefix of values of `is`.

The instance interprets an instruction sequence `is : List instr` by a total-correctness weakest
precondition over `Step`. An assertion `P : Assn` is a predicate on the state and the operand
stack. The stack is a `List val` with its top first: the stack `[.CONST .I32 b, .CONST .I32 a]`
runs as the instruction prefix `[.CONST .I32 a, .CONST .I32 b]`.

`Safe Q E c` holds when every maximal `Step` path from `c` is finite and ends in a configuration
that `Q` or `E` accepts:

* a configuration of values `vs` satisfies `Q z vs`;
* an exit configuration (`br`, `return`, `throw_ref`, `trap`, possibly followed by more
  instructions) with exit `e` satisfies `E e z`;
* any other configuration steps, and every successor is `Safe`.

`Step` requires `wf_config` of its source and of its target. `wp` therefore assumes `wf_config`
of the initial configuration, and every configuration that a step reaches is well-formed.
-/

namespace SpecTecWP

open Std.WP Lean.Order

/-- The operand stack, top first. -/
abbrev Stack := List val

/-- The instruction sequence that runs `is` on the stack `vs`. -/
def code (vs : Stack) (is : List instr) : List instr :=
  vs.reverse.map instr_val ++ is

/-- The configuration that runs `is` on the stack `vs` in state `z`. -/
def cfg (z : state) (vs : Stack) (is : List instr) : config :=
  .mk_config z (code vs is)

/-- A configuration that leaves the instruction sequence early. -/
inductive Exit where
  | br (l : labelidx) (vs : Stack)
  | ret (vs : Stack)
  | throw (a : addr)
  | trap

/-- Assertions over the state and the operand stack. -/
abbrev Assn := state → Stack → Prop

/-- Exception postconditions, one assertion on the state per exit. -/
abbrev EAssn := Exit → state → Prop

/-- `IsExit is e`: the instruction sequence `is` has left early with exit `e`; the
instructions after the exit do not run. A trap and an exception discard the values
before them: the configuration reduces to `[TRAP]` or `[REF.EXN_ADDR a, THROW_REF]`. -/
inductive IsExit : List instr → Exit → Prop where
  | br (vs : Stack) (l : labelidx) (rest : List instr) :
      IsExit (code vs (.BR l :: rest)) (.br l vs)
  | ret (vs : Stack) (rest : List instr) :
      IsExit (code vs (.RETURN :: rest)) (.ret vs)
  | throw (vs : Stack) (a : addr) (rest : List instr) :
      IsExit (code vs (.REF_EXN_ADDR a :: .THROW_REF :: rest)) (.throw a)
  | trap (vs : Stack) (rest : List instr) : IsExit (code vs (.TRAP :: rest)) .trap

/-- Every maximal `Step` path from the configuration is finite, and its last configuration
satisfies `Q` (values) or `E` (an exit). -/
inductive Safe (Q : Assn) (E : EAssn) : config → Prop where
  | vals (z : state) (vs : Stack) : Q z vs → Safe Q E (cfg z vs [])
  | exit (z : state) (is : List instr) (e : Exit) :
      IsExit is e → E e z → Safe Q E (.mk_config z is)
  | step (c : config) :
      (∃ c', Step c c') → (∀ c', Step c c' → Safe Q E c') → Safe Q E c

/-- Total-correctness weakest precondition of `is` on the stack `vs` in state `z`. -/
def Code.wp (is : List instr) (Q : Assn) (E : EAssn) : Assn := fun z vs =>
  wf_config (cfg z vs is) → Safe Q E (cfg z vs is)

theorem Safe.mono {Q Q' : Assn} {E E' : EAssn}
    (hQ : ∀ z vs, Q z vs → Q' z vs) (hE : ∀ e z, E e z → E' e z) {c : config}
    (h : Safe Q E c) : Safe Q' E' c := by
  induction h with
  | vals z vs hq => exact .vals z vs (hQ z vs hq)
  | exit z is e hx he => exact .exit z is e hx (hE e z he)
  | step c hp _ ih => exact .step c hp ih

instance : WP (List instr) Unit Assn EAssn where
  trans is := ⟨fun Q E => Code.wp is (Q ()) E⟩
  trans_monotone is := by
    intro Q Q' E E' hE hQ z vs h hwf
    exact Safe.mono (fun z vs => hQ () z vs) (fun e z => hE e z) (h hwf)

/-- `Std.WP.wp` of an instruction sequence, unfolded to `Code.wp`. -/
theorem wp_apply (is : List instr) (Q : Unit → Assn) (E : EAssn) :
    Std.WP.wp is Q E = Code.wp is (Q ()) E := rfl

/-! ## Well-formedness along steps -/

/-- Every step ends in a well-formed configuration. -/
theorem Step.wf_target {c c' : config} (h : Step c c') : wf_config c' := by
  cases h <;> assumption

/-- Every step starts in a well-formed configuration. -/
theorem Step.wf_source {c c' : config} (h : Step c c') : wf_config c := by
  cases h <;> assumption

end SpecTecWP
