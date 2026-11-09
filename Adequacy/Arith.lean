import Adequacy.Translate

/-!
# The integer operations of Talos and of the SpecTec model agree

For `a b : UInt32`, each lemma equates the SpecTec operation on `mk_uN a.toNat` and
`mk_uN b.toNat` with the `toNat` of the Talos result. The bitwise operations and the signed
comparison are hand-written in `Builtins`.
-/

namespace Adequacy

open SpecTecWP

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

end Adequacy
