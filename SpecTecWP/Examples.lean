import SpecTecWP.Specs
import SpecTecWP.Arith

/-!
# Examples, proved with `vcgen`

Each example is a triple over a Wasm instruction sequence of the SpecTec model, with `i32`
values written `i32v (u a)` for `a : UInt32`. `vcgen` decomposes the sequence with the
`@[spec]` triples of `SpecTecWP.Specs`, and `finish` closes the verification conditions with
the `grind` lemmas that turn the model's integer operations into `UInt32` operations
(`SpecTecWP.Arith`) and read locals after writes (`SpecTecWP.Locals`).
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
example (z : state) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄
      ([const 2, const 3, add] : List instr)
      ⦃ fun _ z' vs => z' = z ∧ vs = [i32v (u 5)] ⦄ := by
  vcgen with finish

/-- With the locals `a` and `b`, the program computes `(a + b) - b = a`, for all `a` and `b`,
across the wrap-around at `2^32`. -/
theorem add_sub (z : state) (a b : UInt32)
    (h0 : fun_local z (.mk_uN 0) = some (i32v (u a)))
    (h1 : fun_local z (.mk_uN 1) = some (i32v (u b))) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄
      ([get 0, get 1, add, get 1, sub] : List instr)
      ⦃ fun _ z' vs => z' = z ∧ vs = [i32v (u a)] ⦄ := by
  vcgen with finish

/-- `x * x + x * 2 + 1`, from the local `x`. -/
abbrev poly₁ : List instr := [get 0, get 0, mul, get 0, const 2, mul, add, const 1, add]

/-- `(x + 1) * (x + 1)`, from the local `x`. -/
abbrev poly₂ : List instr := [get 0, const 1, add, get 0, const 1, add, mul]

/-- The two programs compute the same value from every `x`: the identity
`x * x + 2 * x + 1 = (x + 1) * (x + 1)` holds in `i32`. -/
theorem poly₁_spec (z : state) (x : UInt32) (h0 : fun_local z (.mk_uN 0) = some (i32v (u x))) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄ poly₁
      ⦃ fun _ z' vs => z' = z ∧ vs = [i32v (u ((x + 1) * (x + 1)))] ⦄ := by
  vcgen with finish

theorem poly₂_spec (z : state) (x : UInt32) (h0 : fun_local z (.mk_uN 0) = some (i32v (u x))) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄ poly₂
      ⦃ fun _ z' vs => z' = z ∧ vs = [i32v (u ((x + 1) * (x + 1)))] ⦄ := by
  vcgen with finish

end SpecTecWP.Examples
