import SpecTecWP.Arith

/-!
# Signed division and remainder

For `a b : UInt32`, the model's `$idiv_(32, S, a, b)` and `$irem_(32, S, a, b)` are the results
`divS a b` and `remS a b` that Talos computes with `Int.tdiv` and `Int.tmod` on the `Int32`
readings of `a` and `b`. `$idiv_` has no result for the divisor `0` and for `-2^31 / -1`, and
`$irem_` has no result for the divisor `0`. Each relation has exactly these results.
-/

namespace SpecTecWP

/-! ## Rational helpers -/

theorem rat_neg_div (a b : Rat) : (-a) / b = -(a / b) := by
  rw [Rat.div_def, Rat.div_def, Rat.neg_mul]

theorem rat_inv_neg (b : Rat) : (-b)⁻¹ = -b⁻¹ := by
  by_cases hb : b = 0
  · subst hb; simp
  · apply Rat.inv_eq_of_mul_eq_one
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_inv_cancel b hb]

theorem rat_div_neg (a b : Rat) : a / (-b) = -(a / b) := by
  rw [Rat.div_def, Rat.div_def, rat_inv_neg, Rat.mul_neg]

theorem rat_neg_nonneg {q : Rat} : 0 ≤ -q ↔ q ≤ 0 := by
  rw [Rat.le_neg_iff]; simp

theorem truncz_neg (q : Rat) : truncz (-q) = - truncz q := by
  simp only [truncz, Builtins.truncz]
  by_cases h : 0 ≤ q
  · by_cases h0 : q = 0
    · subst h0; rfl
    · have hn : ¬ 0 ≤ -q := fun hn => h0 (Rat.le_antisymm (rat_neg_nonneg.mp hn) h)
      rw [ite_eq_right hn, ite_eq_left h, Rat.ceil_eq_neg_floor_neg, Rat.neg_neg]
  · have hn : 0 ≤ -q := rat_neg_nonneg.mpr (Rat.le_of_lt (Rat.not_le.mp h))
    rw [ite_eq_left hn, ite_eq_right h, Rat.ceil_eq_neg_floor_neg, Int.neg_neg]

theorem cast_natCast (m : Nat) : ((m : Int) : Rat) = (m : Rat) := Rat.intCast_natCast m

theorem cast_negSucc (m : Nat) : ((Int.negSucc m : Int) : Rat) = -(((m + 1 : Nat)) : Rat) := by
  rw [Int.negSucc_eq, Rat.intCast_neg, ← cast_natCast]; rfl

theorem truncz_nat (m n : Nat) (hn : 0 < n) :
    truncz ((m : Rat) / (n : Rat)) = ((m / n : Nat) : Int) := by
  have := truncz_div m n hn
  rw [ofInt_ofNat, ofInt_ofNat] at this
  simpa using this

/-- `$truncz` of a quotient of integers is the quotient rounded towards zero. -/
theorem truncz_tdiv (x y : Int) (hy : y ≠ 0) :
    truncz (Rat.ofInt x / Rat.ofInt y) = x.tdiv y := by
  change truncz ((x : Rat) / (y : Rat)) = x.tdiv y
  rcases x with m | m <;> rcases y with n | n
  · have hn : n ≠ 0 := fun h => hy (by simp [h])
    rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, cast_natCast, cast_natCast,
      truncz_nat m n (by omega)]
    rfl
  · rw [Int.ofNat_eq_natCast, cast_natCast, cast_negSucc, rat_div_neg, truncz_neg,
      truncz_nat m (n + 1) (by omega)]
    rfl
  · have hn : n ≠ 0 := fun h => hy (by simp [h])
    rw [Int.ofNat_eq_natCast, cast_natCast, cast_negSucc, rat_neg_div, truncz_neg,
      truncz_nat (m + 1) n (by omega)]
    rfl
  · rw [cast_negSucc, cast_negSucc, rat_neg_div, rat_div_neg, Rat.neg_neg,
      truncz_nat (m + 1) (n + 1) (by omega)]
    rfl

/-! ## Signed values -/

theorem n31 : Int.toNat (Int.ofNat 32 - Int.ofNat 1) = 31 := rfl

theorem fun_signed_32 (a : UInt32) : fun_signed_ 32 a.toNat a.toInt32.toInt := by
  rw [← signed_toInt32, Builtins.signed_]
  have := a.toNat_lt
  split
  · exact .fun_signed__case_0 32 _ (by rw [n31]; omega) (by decide)
  · have e : ((a.toNat : Int) - 2 ^ 32) = Int.ofNat a.toNat - Int.ofNat (2 ^ 32) := by simp
    rw [e]
    exact .fun_signed__case_1 32 _ ⟨by rw [n31]; omega, by omega⟩ (by decide)

theorem fun_signed_uniq {N i : Nat} {x y : Int} (hx : fun_signed_ N i x)
    (hy : fun_signed_ N i y) : x = y := by
  cases hx <;> cases hy <;> first | rfl | omega

theorem toUInt32_ofInt_toNat (q : Int) :
    (Int32.ofInt q).toUInt32.toNat = (q % 2 ^ 32).toNat := by
  simp [Int32.toUInt32, Int32.ofInt, BitVec.toNat_ofInt, Int32.toBitVec]

theorem fun_inv_signed_32 {q : Int} (h1 : -2 ^ 31 ≤ q) (h2 : q < 2 ^ 31) :
    fun_inv_signed_ 32 q (Int32.ofInt q).toUInt32.toNat := by
  rw [toUInt32_ofInt_toNat]
  by_cases hq : 0 ≤ q
  · have e : (q % 2 ^ 32).toNat = q.toNat := by congr 1; omega
    rw [e]
    exact .fun_inv_signed__case_0 32 q ⟨by simpa using hq, by rw [n31]; simp; omega⟩ hq (by decide)
  · have e : (q % 2 ^ 32).toNat = (q + Int.ofNat (2 ^ 32)).toNat := by congr 1; simp; omega
    rw [e]
    exact .fun_inv_signed__case_1 32 q ⟨by rw [n31]; simp; omega, by simp; omega⟩
      (by simp; omega) (by decide)

theorem fun_inv_signed_uniq {N : Nat} {q : Int} {x y : Nat} (hx : fun_inv_signed_ N q x)
    (hy : fun_inv_signed_ N q y) : x = y := by
  cases hx <;> cases hy <;> first | rfl | omega

theorem fun_inv_signed_none {x : Nat} (h : fun_inv_signed_ 32 (2 ^ 31) x) : False := by
  cases h <;> simp at * <;> omega

theorem sa_range (a : UInt32) : -2 ^ 31 ≤ a.toInt32.toInt ∧ a.toInt32.toInt < 2 ^ 31 := by
  rw [← signed_toInt32, Builtins.signed_]
  have := a.toNat_lt
  split <;> omega

theorem sa_min_iff (a : UInt32) : a.toInt32.toInt = -2 ^ 31 ↔ a = 0x80000000 := by
  rw [← signed_toInt32, Builtins.signed_, ← UInt32.toNat_inj]
  have := a.toNat_lt
  split <;> simp <;> omega

theorem sa_neg_one_iff (b : UInt32) : b.toInt32.toInt = -1 ↔ b = 0xFFFFFFFF := by
  rw [← signed_toInt32, Builtins.signed_, ← UInt32.toNat_inj]
  have := b.toNat_lt
  split <;> simp <;> omega

theorem sa_ne_zero {b : UInt32} (hb : b ≠ 0) : b.toInt32.toInt ≠ 0 := by
  rw [← signed_toInt32, Builtins.signed_]
  have := b.toNat_lt
  have h0 := toNat_ne_zero hb
  split <;> omega

/-- The quotient of signed `i32` values is a signed `i32` value, except `-2^31 / -1`. -/
theorem tdiv_range {x y : Int} (hx : -2 ^ 31 ≤ x ∧ x < 2 ^ 31) (hy : y ≠ 0)
    (hov : ¬ (x = -2 ^ 31 ∧ y = -1)) : -2 ^ 31 ≤ x.tdiv y ∧ x.tdiv y < 2 ^ 31 := by
  by_cases hY : y.natAbs = 1
  · rcases Int.natAbs_eq_iff.mp hY with h | h <;> (try simp only [Int.ofNat_eq_natCast] at h) <;>
      subst h
    · simp; omega
    · simp [Int.tdiv_neg]; omega
  · have hQ := Int.natAbs_tdiv x y
    have h2 : x.natAbs / y.natAbs ≤ x.natAbs / 2 :=
      Nat.div_le_div_left (by omega) (by decide)
    have : (x.tdiv y).natAbs ≤ x.natAbs / 2 := by rw [hQ]; exact h2
    omega

theorem tmod_range {x y : Int} (hy : -2 ^ 31 ≤ y ∧ y < 2 ^ 31) (hy0 : y ≠ 0) :
    -2 ^ 31 ≤ x.tmod y ∧ x.tmod y < 2 ^ 31 := by
  have h := Int.natAbs_tmod x y
  have h2 : x.natAbs % y.natAbs < y.natAbs := Nat.mod_lt _ (by omega)
  omega

/-! ## Signed division and remainder in the model -/

/-- The `i32` result of `div_s` on `a` and `b`, as Talos computes it. -/
def divS (a b : UInt32) : UInt32 := (Int32.ofInt (a.toInt32.toInt.tdiv b.toInt32.toInt)).toUInt32

/-- The `i32` result of `rem_s` on `a` and `b`, as Talos computes it. -/
def remS (a b : UInt32) : UInt32 := (Int32.ofInt (a.toInt32.toInt.tmod b.toInt32.toInt)).toUInt32

theorem rat_ofInt_ne_zero {y : Int} (h : y ≠ 0) : Rat.ofInt y ≠ 0 :=
  fun h0 => h (Rat.intCast_eq_zero_iff.mp h0)

theorem rat_div_one (a : Rat) : a / 1 = a := by
  rw [Rat.div_def, show (1 : Rat)⁻¹ = 1 from Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]

theorem ov_iff {a b : UInt32} :
    (a.toInt32.toInt = -2 ^ 31 ∧ b.toInt32.toInt = -1) ↔ (a = 0x80000000 ∧ b = 0xFFFFFFFF) := by
  rw [sa_min_iff, sa_neg_one_iff]

theorem two_pow_31 : Rat.ofInt (Int.ofNat (2 ^ Int.toNat (Int.ofNat 32 - Int.ofNat 1))) =
    Rat.ofInt (2 ^ 31) := rfl

theorem truncz_intCast (n : Int) : truncz (Rat.ofInt n) = n := by
  simp only [truncz, Builtins.truncz]
  split
  · exact Rat.floor_intCast n
  · rw [Rat.ceil_eq_neg_floor_neg, show -Rat.ofInt n = Rat.ofInt (-n) from (Rat.intCast_neg n).symm,
      show Rat.ofInt (-n) = ((-n : Int) : Rat) from rfl, Rat.floor_intCast, Int.neg_neg]

/-- The overflow premise of `$idiv_` holds exactly for `-2^31 / -1`. -/
theorem ov_rat_iff {a b : UInt32} (hb : b ≠ 0) :
    Rat.ofInt a.toInt32.toInt / Rat.ofInt b.toInt32.toInt = Rat.ofInt (2 ^ 31) ↔
      (a = 0x80000000 ∧ b = 0xFFFFFFFF) := by
  rw [← ov_iff]
  constructor
  · intro h
    have ht := congrArg truncz h
    rw [truncz_tdiv _ _ (sa_ne_zero hb), truncz_intCast] at ht
    refine Classical.byContradiction fun hov => ?_
    have := tdiv_range (sa_range a) (sa_ne_zero hb) hov
    omega
  · rintro ⟨ha, hb'⟩
    rw [ha, hb']
    change ((-2 ^ 31 : Int) : Rat) / ((-1 : Int) : Rat) = ((2 ^ 31 : Int) : Rat)
    rw [Rat.intCast_neg 1, rat_div_neg, Rat.intCast_one, rat_div_one, ← Rat.intCast_neg,
      Int.neg_neg]

theorem u_ne_zero {b : UInt32} (hb : b ≠ 0) : u b ≠ .mk_uN 0 :=
  fun h => toNat_ne_zero hb (by simpa [u] using h)

theorem fun_idiv_s {a b : UInt32} (hb : b ≠ 0) (hov : ¬ (a = 0x80000000 ∧ b = 0xFFFFFFFF)) :
    fun_idiv_ 32 .S (u a) (u b) (some (u (divS a b))) := by
  have hr := tdiv_range (sa_range a) (sa_ne_zero hb) (by rwa [ov_iff])
  refine .fun_idiv__case_4 32 (u a) (u b) _ _ _ (fun_signed_32 b) (fun_signed_32 a) ?_ ?_
    (rat_ofInt_ne_zero (sa_ne_zero hb))
  · rw [truncz_tdiv _ _ (sa_ne_zero hb)]
    exact fun_inv_signed_32 hr.1 hr.2
  · have := (divS a b).toNat_lt
    exact .uN_case_0 _ _ ⟨Nat.zero_le _, by simp; omega⟩ (by decide)

theorem fun_idiv_s_uniq {a b : UInt32} {x y : uN} {r : Option uN} (hb : b ≠ 0)
    (hov : ¬ (a = 0x80000000 ∧ b = 0xFFFFFFFF)) (hx : x = u a) (hy : y = u b)
    (h : fun_idiv_ 32 .S x y r) : r = some (u (divS a b)) := by
  cases h with
  | fun_idiv__case_2 => exact absurd hy.symm (u_ne_zero hb)
  | fun_idiv__case_3 =>
    subst hx hy
    have e2 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u b)) _› (fun_signed_32 b)
    have e1 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u a)) _› (fun_signed_32 a)
    subst e2 e1
    have hq := ‹Rat.ofInt _ / Rat.ofInt _ = _›
    rw [two_pow_31, ov_rat_iff hb] at hq
    exact absurd hq hov
  | fun_idiv__case_4 =>
    subst hx hy
    have e2 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u b)) _› (fun_signed_32 b)
    have e1 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u a)) _› (fun_signed_32 a)
    subst e2 e1
    have hinv := ‹fun_inv_signed_ 32 _ _›
    rw [truncz_tdiv _ _ (sa_ne_zero hb)] at hinv
    have hr := tdiv_range (sa_range a) (sa_ne_zero hb) (by rwa [ov_iff])
    rw [fun_inv_signed_uniq hinv (fun_inv_signed_32 hr.1 hr.2)]
    rfl

theorem fun_idiv_s_ov : fun_idiv_ 32 .S (u 0x80000000) (u 0xFFFFFFFF) none :=
  .fun_idiv__case_3 32 _ _ _ _ (fun_signed_32 _) (fun_signed_32 _)
    (by rw [two_pow_31, ov_rat_iff (by decide)]; exact ⟨rfl, rfl⟩)
    (rat_ofInt_ne_zero (sa_ne_zero (by decide))) (by decide)

theorem fun_idiv_s_ov_uniq {x y : uN} {r : Option uN} (hx : x = u 0x80000000)
    (hy : y = u 0xFFFFFFFF) (h : fun_idiv_ 32 .S x y r) : r = none := by
  cases h with
  | fun_idiv__case_2 => exact absurd hy (by decide)
  | fun_idiv__case_3 => rfl
  | fun_idiv__case_4 =>
    subst hx hy
    have e2 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u 0xFFFFFFFF)) _› (fun_signed_32 _)
    have e1 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u 0x80000000)) _› (fun_signed_32 _)
    subst e2 e1
    have hinv := ‹fun_inv_signed_ 32 _ _›
    rw [truncz_tdiv _ _ (sa_ne_zero (by decide))] at hinv
    exact (fun_inv_signed_none (by simpa using hinv)).elim

theorem fun_idiv_s_zero_uniq {x y : uN} {r : Option uN} (hy : y = .mk_uN 0)
    (h : fun_idiv_ 32 .S x y r) : r = none := by
  cases h with
  | fun_idiv__case_2 => rfl
  | fun_idiv__case_3 =>
    subst hy
    have e := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (uN.mk_uN 0)) _› (fun_signed_32 0)
    subst e
    have hne := ‹Rat.ofInt _ ≠ 0›
    exact (hne (by decide)).elim
  | fun_idiv__case_4 =>
    subst hy
    have e := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (uN.mk_uN 0)) _› (fun_signed_32 0)
    subst e
    have hne := ‹Rat.ofInt _ ≠ 0›
    exact (hne (by decide)).elim

theorem fun_irem_s {a b : UInt32} (hb : b ≠ 0) :
    fun_irem_ 32 .S (u a) (u b) (some (u (remS a b))) := by
  have hr := tmod_range (x := a.toInt32.toInt) (sa_range b) (sa_ne_zero hb)
  refine .fun_irem__case_3 32 (u a) (u b) _ _ _ _ _ (fun_signed_32 b) (fun_signed_32 a) ?_
    ⟨rfl, rfl⟩ (rat_ofInt_ne_zero (sa_ne_zero hb))
  rw [truncz_tdiv _ _ (sa_ne_zero hb), ← Int.tmod_def]
  exact fun_inv_signed_32 hr.1 hr.2

theorem fun_irem_s_uniq {a b : UInt32} {x y : uN} {r : Option uN} (hb : b ≠ 0)
    (hx : x = u a) (hy : y = u b) (h : fun_irem_ 32 .S x y r) : r = some (u (remS a b)) := by
  cases h with
  | fun_irem__case_2 => exact absurd hy.symm (u_ne_zero hb)
  | fun_irem__case_3 =>
    subst hx hy
    obtain ⟨rfl, rfl⟩ := ‹(_ : Int) = _ ∧ (_ : Int) = _›
    have e2 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u b)) _› (fun_signed_32 b)
    have e1 := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (u a)) _› (fun_signed_32 a)
    subst e2 e1
    have hinv := ‹fun_inv_signed_ 32 _ _›
    rw [truncz_tdiv _ _ (sa_ne_zero hb), ← Int.tmod_def] at hinv
    have hr := tmod_range (x := a.toInt32.toInt) (sa_range b) (sa_ne_zero hb)
    rw [fun_inv_signed_uniq hinv (fun_inv_signed_32 hr.1 hr.2)]
    rfl

theorem fun_irem_s_zero_uniq {x y : uN} {r : Option uN} (hy : y = .mk_uN 0)
    (h : fun_irem_ 32 .S x y r) : r = none := by
  cases h with
  | fun_irem__case_2 => rfl
  | fun_irem__case_3 =>
    subst hy
    obtain ⟨rfl, rfl⟩ := ‹(_ : Int) = _ ∧ (_ : Int) = _›
    have e := fun_signed_uniq ‹fun_signed_ 32 (proj_uN_0 (uN.mk_uN 0)) _› (fun_signed_32 0)
    subst e
    have hne := ‹Rat.ofInt _ ≠ 0›
    exact (hne (by decide)).elim

end SpecTecWP
