import SpecTecWP.Specs

/-!
# Examples, proved with `vcgen`

Each example is a triple over a Wasm instruction sequence, with assertions over the view of
`SpecTecWP.View`: the typed locals `s.locals` and the typed stack `s.stack`. `vcgen` decomposes
the sequence with the `@[spec]` triples of `SpecTecWP.Specs`, and `finish` closes the
verification conditions. `transport` turns each triple into a statement about the SpecTec
model.
-/

namespace SpecTecWP.Examples

open SpecTecWP Std.WP Lean.Order

set_option experimental.vcgen true

/-- An `i32` constant instruction for a `UInt32`. -/
abbrev const (a : UInt32) : instr := .CONST .I32 (.mk_num__0 .I32 (u a))

abbrev add : instr := .BINOP .I32 (.mk_binop__0 .I32 .ADD)
abbrev sub : instr := .BINOP .I32 (.mk_binop__0 .I32 .SUB)
abbrev mul : instr := .BINOP .I32 (.mk_binop__0 .I32 .MUL)
abbrev get (n : Nat) : instr := .LOCAL_GET (.mk_uN n)

/-- `2 + 3 = 5`. -/
example : ⦃ fun s => s.stack = [] ⦄ ([const 2, const 3, add] : List instr)
    ⦃ fun _ s => s.stack = [.i32 5] ⦄ := by
  vcgen with finish

/-- With the locals `a` and `b`, the program computes `(a + b) - b = a`, for all `a` and `b`,
across the wrap-around at `2^32`. -/
theorem add_sub (a b : UInt32) :
    ⦃ fun s => s.locals = [.i32 a, .i32 b] ∧ s.stack = [] ⦄
      ([get 0, get 1, add, get 1, sub] : List instr)
      ⦃ fun _ s => s.locals = [.i32 a, .i32 b] ∧ s.stack = [.i32 a] ⦄ := by
  vcgen with finish

/-- `x * x + x * 2 + 1`, from the local `x`. -/
abbrev poly₁ : List instr := [get 0, get 0, mul, get 0, const 2, mul, add, const 1, add]

/-- `(x + 1) * (x + 1)`, from the local `x`. -/
abbrev poly₂ : List instr := [get 0, const 1, add, get 0, const 1, add, mul]

/-- The two programs compute the same value from every `x`: the identity
`x * x + 2 * x + 1 = (x + 1) * (x + 1)` holds in `i32`. -/
theorem poly₁_spec (x : UInt32) :
    ⦃ fun s => s.locals = [.i32 x] ∧ s.stack = [] ⦄ poly₁
      ⦃ fun _ s => s.stack = [.i32 ((x + 1) * (x + 1))] ⦄ := by
  vcgen with finish

theorem poly₂_spec (x : UInt32) :
    ⦃ fun s => s.locals = [.i32 x] ∧ s.stack = [] ⦄ poly₂
      ⦃ fun _ s => s.stack = [.i32 ((x + 1) * (x + 1))] ⦄ := by
  vcgen with finish

end SpecTecWP.Examples
