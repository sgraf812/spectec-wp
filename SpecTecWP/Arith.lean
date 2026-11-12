import SpecTecWP.Basic

/-!
# The integer operations of the model on `UInt32`

For `a b : UInt32`, each lemma equates an operation of the model on `u a = mk_uN a.toNat` and
`u b` with `u` of the corresponding `UInt32` operation. The bitwise operations and the signed
comparison are the hand-written definitions of `Builtins`.
-/

namespace SpecTecWP

def u (a : UInt32) : uN := .mk_uN a.toNat

theorem iadd_eq (a b : UInt32) : iadd_ 32 (u b) (u a) = u (a + b) := by
  simp only [iadd_, u, proj_uN_0, UInt32.toNat_add, Nat.add_comm, sizenn]

theorem isub_eq (a b : UInt32) : isub_ 32 (u b) (u a) = u (b - a) := by
  simp only [isub_, u, proj_uN_0, uN.mk_uN.injEq, UInt32.toNat_sub]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [Int.ofNat_eq_coe]
  rw [show ((2 ^ 32 + b.toNat : Nat) : Int) - (a.toNat : Int) = ((2 ^ 32 + b.toNat - a.toNat : Nat) : Int) by
    omega]
  rw [show Int.tmod ((2 ^ 32 + b.toNat - a.toNat : Nat) : Int) ((2 ^ 32 : Nat) : Int) =
    (((2 ^ 32 + b.toNat - a.toNat) % 2 ^ 32 : Nat) : Int) from rfl, Int.toNat_natCast]
  omega

theorem imul_eq (a b : UInt32) : imul_ 32 (u b) (u a) = u (a * b) := by
  simp only [imul_, u, proj_uN_0, UInt32.toNat_mul, Nat.mul_comm]

theorem bv_of (x : UInt32) : BitVec.ofNat 32 x.toNat = x.toBitVec := by
  rw [← UInt32.toNat_toBitVec, BitVec.ofNat_toNat]; simp

theorem iand_eq (a b : UInt32) : iand_ 32 (u b) (u a) = u (a &&& b) := by
  simp only [iand_, u, proj_uN_0, uN.mk_uN.injEq, Builtins.OnNat.bin, Builtins.iand_, bv_of]
  simp [UInt32.toBitVec_and, BitVec.and_comm]

theorem ior_eq (a b : UInt32) : ior_ 32 (u a) (u b) = u (a ||| b) := by
  simp only [ior_, u, proj_uN_0, uN.mk_uN.injEq, Builtins.OnNat.bin, Builtins.ior_]
  rw [← UInt32.toNat_toBitVec, ← UInt32.toNat_toBitVec b, BitVec.ofNat_toNat, BitVec.ofNat_toNat]
  simp [BitVec.setWidth_eq, UInt32.toBitVec_or]

theorem ixor_eq (a b : UInt32) : ixor_ 32 (u a) (u b) = u (a ^^^ b) := by
  simp only [ixor_, u, proj_uN_0, uN.mk_uN.injEq, Builtins.OnNat.bin, Builtins.ixor_]
  rw [← UInt32.toNat_toBitVec, ← UInt32.toNat_toBitVec b, BitVec.ofNat_toNat, BitVec.ofNat_toNat]
  simp [BitVec.setWidth_eq, UInt32.toBitVec_xor]

theorem bool_u (p : Prop) [Decidable p] : u (if p then 1 else 0) = .mk_uN (nat_of_bool (decide p)) := by
  by_cases hp : p <;> simp [u, hp, nat_of_bool]

theorem ieqz_eq (a : UInt32) : ieqz_ 32 (u a) = u (if a = 0 then 1 else 0) := by
  rw [bool_u]
  simp only [ieqz_, u, proj_uN_0]
  congr 2

theorem ieq_eq (a b : UInt32) : ieq_ 32 (u a) (u b) = u (if a = b then 1 else 0) := by
  rw [bool_u]
  simp only [ieq_, u]
  congr 2
  exact Bool.eq_iff_iff.mpr (by simp [UInt32.toNat_inj])

theorem ine_eq (a b : UInt32) : ine_ 32 (u a) (u b) = u (if a ≠ b then 1 else 0) := by
  rw [bool_u]
  simp only [ine_, u]
  congr 2
  exact Bool.eq_iff_iff.mpr (by simp [bne, UInt32.toNat_inj])

theorem ilt_u_eq (a b : UInt32) : ilt_ 32 .U (u a) (u b) = u (if a < b then 1 else 0) := by
  have h' : a < b ↔ a.toNat < b.toNat := UInt32.lt_iff_toNat_lt
  by_cases h : a < b
  · simp [ilt_, u, proj_uN_0, Builtins.bool, h, h'.mp h]
  · have h2 : ¬ a.toNat < b.toNat := fun h2 => h (h'.mpr h2)
    simp [ilt_, u, proj_uN_0, Builtins.bool, h, h2]

theorem signed_toInt32 (a : UInt32) : Builtins.signed_ 32 a.toNat = a.toInt32.toInt := by
  rw [Int32.toInt, UInt32.toInt32, Builtins.signed_]
  simp only [Int32.toBitVec, BitVec.toInt, UInt32.toNat_toBitVec]
  have := a.toNat_lt
  split <;> split <;> omega

theorem ilt_s_eq (a b : UInt32) :
    ilt_ 32 .S (u a) (u b) = u (if a.toInt32 < b.toInt32 then 1 else 0) := by
  have h : (a.toInt32 < b.toInt32) ↔ Builtins.signed_ 32 a.toNat < Builtins.signed_ 32 b.toNat := by
    rw [signed_toInt32, signed_toInt32, Int32.lt_iff_toInt_lt]
  by_cases hab : a.toInt32 < b.toInt32
  · simp [ilt_, u, proj_uN_0, Builtins.bool, hab, h.mp hab]
  · have h2 : ¬ Builtins.signed_ 32 a.toNat < Builtins.signed_ 32 b.toNat := fun h2 => hab (h.mpr h2)
    simp [ilt_, u, proj_uN_0, Builtins.bool, hab, h2]

/-! ## Unsigned remainder -/

theorem ofInt_ofNat (a : Nat) : Rat.ofInt (Int.ofNat a) = (a : Rat) := by
  change ((Int.ofNat a : Int) : Rat) = (a : Rat)
  rw [Int.ofNat_eq_natCast, Rat.intCast_natCast]

/-- `$truncz` of a quotient of naturals is the natural quotient. -/
theorem truncz_div (a b : Nat) (hb : 0 < b) :
    truncz (Rat.ofInt (Int.ofNat a) / Rat.ofInt (Int.ofNat b)) = Int.ofNat (a / b) := by
  rw [ofInt_ofNat, ofInt_ofNat]
  have hb' : (0 : Rat) < (b : Rat) := Rat.natCast_pos.mpr hb
  have hq : (0 : Rat) ≤ (a : Rat) / (b : Rat) := by
    apply Rat.not_lt.mp
    rw [Rat.div_lt_iff hb', Rat.zero_mul]
    exact Rat.not_lt.mpr Rat.natCast_nonneg
  simp only [truncz, Builtins.truncz, hq, ↓reduceIte]
  apply Int.le_antisymm
  · have h : ((a : Rat) / (b : Rat)).floor < ((a / b : Nat) : Int) + 1 := by
      rw [Rat.floor_lt_iff, Rat.div_lt_iff hb']
      have h2 : ((a : Nat) : Rat) < (((a / b) * b + b : Nat) : Rat) :=
        Rat.natCast_lt_natCast.mpr (Nat.lt_div_mul_add hb)
      simp only [Rat.natCast_add, Rat.natCast_mul] at h2
      simp only [Rat.intCast_add, Rat.intCast_natCast, Rat.intCast_one, Rat.add_mul, Rat.one_mul]
      exact h2
    simp only [Int.ofNat_eq_natCast]
    omega
  · rw [Int.ofNat_eq_natCast, Rat.le_floor_iff, Rat.intCast_natCast]
    apply Rat.not_lt.mp
    rw [Rat.div_lt_iff hb']
    apply Rat.not_lt.mpr
    have h2 : (((a / b) * b : Nat) : Rat) ≤ ((a : Nat) : Rat) :=
      Rat.natCast_le_natCast.mpr (Nat.div_mul_le_self a b)
    simpa only [Rat.natCast_mul] using h2

/-- The unsigned remainder. -/
def irem_u (x y : uN) : uN := .mk_uN (proj_uN_0 x % proj_uN_0 y)

theorem irem_u_eq_formula (a b : Nat) (hb : b ≠ 0) :
    irem_u (.mk_uN a) (.mk_uN b) = .mk_uN (Int.toNat (Int.ofNat a - Int.ofNat (b *
      Int.toNat (truncz (Rat.ofInt (Int.ofNat a) / Rat.ofInt (Int.ofNat b)))))) := by
  rw [truncz_div a b (Nat.pos_of_ne_zero hb)]
  simp only [irem_u, proj_uN_0, uN.mk_uN.injEq, Int.ofNat_eq_natCast, Int.toNat_natCast]
  have h1 := Nat.mod_add_div a b
  generalize b * (a / b) = m at *
  omega

theorem fun_irem_u {N : Nat} {x y : uN} (hy : proj_uN_0 y ≠ 0) :
    fun_irem_ N .U x y (some (irem_u x y)) := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [proj_uN_0] at hy
  rw [irem_u_eq_formula a b hy]
  have key := truncz_div a b (Nat.pos_of_ne_zero hy)
  refine .fun_irem__case_1 N (.mk_uN a) (.mk_uN b) ?_ ?_ ?_
  · simp only [proj_uN_0]
    rw [key]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    have := Nat.div_mul_le_self a b
    rw [Nat.mul_comm] at this
    omega
  · simp only [proj_uN_0]; rw [key]; exact Int.ofNat_nonneg _
  · simp only [proj_uN_0, ofInt_ofNat]
    exact fun h => hy (Rat.natCast_eq_zero_iff.mp h)

theorem fun_irem_u_uniq {N : Nat} {x y : uN} {r : Option uN} (hy : proj_uN_0 y ≠ 0)
    (h : fun_irem_ N .U x y r) : r = some (irem_u x y) := by
  cases h with
  | fun_irem__case_0 => simp [proj_uN_0] at hy
  | fun_irem__case_1 =>
    obtain ⟨a⟩ := x
    obtain ⟨b⟩ := y
    simp only [proj_uN_0] at hy ⊢
    rw [irem_u_eq_formula a b hy]

theorem irem_u_eq (a b : UInt32) : irem_u (u a) (u b) = u (a % b) := by
  simp [irem_u, u, proj_uN_0, UInt32.toNat_mod]

/-! ## The `UInt32` view for `grind` -/

theorem proj_u (a : UInt32) : proj_uN_0 (u a) = a.toNat := rfl

theorem u_injective : Function.Injective u := by
  intro a b h
  simp only [u, uN.mk_uN.injEq] at h
  exact UInt32.toNat_inj.mp h

attribute [grind =] iadd_eq isub_eq imul_eq iand_eq ior_eq ixor_eq ieqz_eq ieq_eq ine_eq ilt_u_eq
  irem_u_eq proj_u
attribute [grind inj] u_injective

end SpecTecWP
