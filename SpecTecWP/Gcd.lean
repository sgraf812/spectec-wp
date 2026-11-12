import SpecTecWP.Examples

/-!
# Euclid's gcd

The gcd loop of the Talos examples, as an instruction sequence of the SpecTec model. A `loop`
runs a `block` that exits when the local `1` is `0`, and otherwise rotates
`(l0, l1) ← (l1, l0 % l1)` through the local `2` and restarts the loop with `br 1`.
-/

namespace SpecTecWP.Examples

open SpecTecWP Std.WP Lean.Order

set_option experimental.vcgen true

abbrev set (n : Nat) : instr := .LOCAL_SET (.mk_uN n)
abbrev eqz : instr := .TESTOP .I32 (.mk_testop__0 .I32 .EQZ)
abbrev remU : instr := .BINOP .I32 (.mk_binop__0 .I32 (.REM .U))

abbrev gcdBody : List instr :=
  [.LOOP (._RESULT none) [.BLOCK (._RESULT none)
    [get 1, eqz, .BR_IF (.mk_uN 0),
     get 0, get 1, remU, set 2,
     get 1, set 0,
     get 2, set 1,
     .BR (.mk_uN 1)]],
   get 0]

@[grind =] theorem gcd_step (a b : Nat) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcd_zero (a : Nat) : Nat.gcd a 0 = a := Nat.gcd_zero_right a

grind_pattern gcd_zero => Nat.gcd a 0

theorem toNat_mod_lt (a : UInt32) {b : UInt32} (h : b ≠ 0) :
    a.toNat % b.toNat < b.toNat := by
  refine Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => h ?_)
  exact UInt32.toNat_inj.mp (by simpa using h0)

grind_pattern toNat_mod_lt => a.toNat % b.toNat

attribute [local grind =] UInt32.toNat_mod UInt32.ofNat_toNat

theorem gcd_spec (z : state) (a b t : UInt32)
    (h0 : fun_local z (.mk_uN 0) = some (i32v (u a)))
    (h1 : fun_local z (.mk_uN 1) = some (i32v (u b)))
    (h2 : fun_local z (.mk_uN 2) = some (i32v (u t))) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄ gcdBody
      ⦃ fun _ z' vs => sof z' = sof z ∧
          vs = [i32v (u (UInt32.ofNat (Nat.gcd a.toNat b.toNat)))] ⦄ := by
  vcgen invariants
    | inv1 => fun z' vs => vs = [] ∧ sof z' = sof z ∧ ∃ a' b' t' : UInt32,
        fun_local z' (.mk_uN 0) = some (i32v (u a')) ∧
        fun_local z' (.mk_uN 1) = some (i32v (u b')) ∧
        fun_local z' (.mk_uN 2) = some (i32v (u t')) ∧
        Nat.gcd a'.toNat b'.toNat = Nat.gcd a.toNat b.toNat
    | inv2 => fun z' _ => proj_uN_0 (asI32 (fun_local z' (.mk_uN 1)).get!)
  with finish

end SpecTecWP.Examples
