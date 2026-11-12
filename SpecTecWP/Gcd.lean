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

theorem gcd_spec (st : store) (a b t : UInt32) :
    ⦃ fun s => s.store = st ∧ s.locals = [some (.i32 a), some (.i32 b), some (.i32 t)] ∧
        s.stack = [] ⦄ gcdBody
      ⦃ fun _ s => s.store = st ∧ s.stack = [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))] ⦄ := by
  vcgen invariants
    | inv1 => fun s => s.store = st ∧ s.stack = [] ∧
        match s.locals with
        | [some (.i32 a'), some (.i32 b'), some (.i32 _)] =>
          Nat.gcd a'.toNat b'.toNat = Nat.gcd a.toNat b.toNat
        | _ => False
    | inv2 => fun s => match s.locals with
        | [_, some (.i32 b'), _] => b'.toNat
        | _ => 0
  with finish

/-- The gcd loop on the SpecTec model: from a state whose frame holds the three `i32` locals,
every reduction terminates with `gcd a b` on the stack and the store unchanged. -/
theorem gcd_spectec (z : state) (a b t : UInt32)
    (h : (fof z).LOCALS = [some (i32v (u a)), some (i32v (u b)), some (i32v (u t))]) :
    Code.wp gcdBody
      (lift fun s => s.store = sof z ∧ s.stack = [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))])
      (liftE ⊥) z [] :=
  transport (gcd_spec (sof z) a b t)
    (s := ⟨sof z, (fof z).MODULE, [some (.i32 a), some (.i32 b), some (.i32 t)], []⟩)
    ⟨⟨rfl, rfl, h⟩, rfl⟩ ⟨rfl, rfl, rfl⟩

end SpecTecWP.Examples
