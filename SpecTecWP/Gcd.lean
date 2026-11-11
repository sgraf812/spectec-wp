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

theorem wf_val_i32 (x : Nat) : wf_val (i32v (.mk_uN x)) ↔ x < 2 ^ 32 := by
  constructor
  · intro h
    cases h with
    | val_case_0 _ _ h =>
      have := wf_of_wf_num h
      cases this with
      | uN_case_0 _ h _ => simp only [Int.ofNat_eq_natCast] at h; omega
  · intro h
    exact .val_case_0 _ _ (wf_num_i32 (.uN_case_0 _ _ ⟨Nat.zero_le _, by
      simp only [Int.ofNat_eq_natCast]; omega⟩ (by decide)))

theorem gcd_rem (a b : Nat) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

theorem mod_lt_pow {a b : Nat} (h : a < 4294967296) : a % b < 4294967296 :=
  Nat.lt_of_le_of_lt (Nat.mod_le a b) h

theorem proj_mk (x : Nat) : proj_uN_0 (.mk_uN x) = x := rfl

theorem proj_ieqz (N x : Nat) : proj_uN_0 (ieqz_ N (.mk_uN x)) = if x = 0 then 1 else 0 := by
  cases x <;> simp [ieqz_, nat_of_bool, proj_uN_0]

/-- The value of the local `i`, as a natural number. -/
def loc (z : state) (i : Nat) : Nat := proj_uN_0 (asI32 (fun_local z (.mk_uN i)).get!)

theorem gcd_spec (z : state) (a b t : Nat) (h3 : 2 < (fof z).LOCALS.length)
    (h0 : fun_local z (.mk_uN 0) = some (i32v (.mk_uN a)))
    (h1 : fun_local z (.mk_uN 1) = some (i32v (.mk_uN b)))
    (h2 : fun_local z (.mk_uN 2) = some (i32v (.mk_uN t)))
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (ht : t < 2 ^ 32) :
    ⦃ fun z' vs => z' = z ∧ vs = [] ⦄ gcdBody
      ⦃ fun _ _ vs => vs = [i32v (.mk_uN (Nat.gcd a b))] ⦄ := by
  have h3' : 1 < (fof z).LOCALS.length := by omega
  have h3'' : 0 < (fof z).LOCALS.length := by omega
  vcgen invariants
    | inv1 => fun z' vs => vs = [] ∧
        0 < (fof z').LOCALS.length ∧ 1 < (fof z').LOCALS.length ∧ 2 < (fof z').LOCALS.length ∧ ∃ x0 x1 x2 : Nat,
        fun_local z' (.mk_uN 0) = some (i32v (.mk_uN x0)) ∧
        fun_local z' (.mk_uN 1) = some (i32v (.mk_uN x1)) ∧
        fun_local z' (.mk_uN 2) = some (i32v (.mk_uN x2)) ∧
        x0 < 2 ^ 32 ∧ x1 < 2 ^ 32 ∧ x2 < 2 ^ 32 ∧ Nat.gcd x0 x1 = Nat.gcd a b
    | inv2 => fun z' _ => loc z' 1
  all_goals
    repeat (first
      | cases ‹∃ _ : Nat, _›
      | cases ‹_ ∧ _›)
  all_goals simp_all [loc, fun_local_with_local, irem_u, proj_ieqz, proj_mk, wf_val_i32,
    gcd_rem, mod_lt_pow]
  all_goals exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

end SpecTecWP.Examples
