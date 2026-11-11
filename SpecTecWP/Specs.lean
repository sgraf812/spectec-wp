import SpecTecWP.InstrLocal
import Std.Tactic.Do

/-!
# Specification triples for `vcgen`

The program structure is a list: `Spec.cons` sequences the head with the tail, and each
instruction has one `@[spec]` triple in total style. A read from the stack is `vs[i]!`, an
`i32` payload is `asI32`, and the partiality of an instruction is one closed `⌜…⌝` guard.
-/

namespace SpecTecWP

open Std.WP Lean.Order

set_option mvcgen.warning false

/-- An `i32` value. -/
abbrev i32v (x : uN) : val := .CONST .I32 (.mk_num__0 .I32 x)

/-- The payload of an `i32` value. -/
def asI32 : val → uN
  | .CONST .I32 (.mk_num__0 .I32 x) => x
  | _ => default

@[simp] theorem asI32_i32v (x : uN) : asI32 (i32v x) = x := rfl

theorem wp_eq (is : List instr) (Q : Unit → Assn) (E : EAssn) :
    Std.WP.wp is Q E = Code.wp is (Q ()) E := rfl

@[spec] theorem Spec.nil {Q : Unit → Assn} {E : EAssn} : Triple ([] : List instr) (Q ()) Q E := by
  refine Triple.iff.mpr fun z vs hq _ => ?_
  have := Safe.vals (E := E) z vs hq
  simpa [cfg_eq] using this

@[spec] theorem Spec.cons {i j : instr} {q : List instr} {Q : Unit → Assn} {E : EAssn} :
    Triple (i :: j :: q) (Std.WP.wp [i] (fun _ => Std.WP.wp (j :: q) Q E) E) Q E := by
  refine Triple.iff.mpr fun z vs h => ?_
  have : Code.wp ([i] ++ j :: q) (Q ()) E z vs := Code.wp_append h
  simpa [wp_eq] using this

@[spec] theorem Spec.const {nt : numtype} {k : num_} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.CONST nt k] : List instr) (fun z vs => Q () z (.CONST nt k :: vs)) Q E :=
  Triple.iff.mpr fun _ _ h => Code.wp_const (c := .CONST nt k) h

/-! ## `i32` binary operators -/

theorem wf_mod (N i : Nat) : wf_uN N (.mk_uN (i % 2 ^ N)) := by
  have h1 := Nat.mod_lt i (Nat.two_pow_pos N)
  have h2 := Nat.two_pow_pos N
  refine .uN_case_0 _ _ ⟨by omega, ?_⟩ ?_ <;> simp only [Int.ofNat_eq_coe] <;> omega

theorem wf_num_i32 {x : uN} (h : wf_uN 32 x) : wf_num_ .I32 (.mk_num__0 .I32 x) :=
  .num__case_0 _ _ _ h rfl

/-- An `i32` binary operator whose result is `g x y`. -/
theorem Spec.i32_binop {op : binop_Inn} (g : uN → uN → uN)
    (hf : ∀ x y, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 x) (.mk_num__0 .I32 y)
      (some [.mk_num__0 .I32 (g x y)]))
    (huniq : ∀ x y r, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 x)
      (.mk_num__0 .I32 y) r → r = some [.mk_num__0 .I32 (g x y)])
    (hwf : ∀ x y, wf_uN 32 (g x y)) {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 op)] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ vs[1]! = i32v (asI32 vs[1]!) ∧
          2 ≤ vs.length⌝ : Prop) ⊓
        Q () z (i32v (g (asI32 vs[1]!) (asI32 vs[0]!)) :: vs.drop 2)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  rcases vs with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons,
      List.drop_zero] at h0 h1 hq
    rw [h0, h1]
    exact Code.wp_binop (hf _ _) (huniq _ _)
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact wf_num_i32 (hwf _ _))
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact hq)
      (fun h => by simp at h)

/-- The `otherwise` clause of `$binop_` does not apply to a defined `i32` operation. -/
macro "binop_uniq" w:term : tactic => `(tactic| (
  intro x y r hr
  cases hr
  · rfl
  · rename_i hneg; exact absurd (by constructor; exact $w _ _) hneg))

theorem wf_iadd (x y : uN) : wf_uN 32 (iadd_ 32 x y) := wf_mod 32 _
theorem wf_imul (x y : uN) : wf_uN 32 (imul_ 32 x y) := wf_mod 32 _

@[spec] theorem Spec.i32_add {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .ADD)] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ vs[1]! = i32v (asI32 vs[1]!) ∧
          2 ≤ vs.length⌝ : Prop) ⊓
        Q () z (i32v (iadd_ 32 (asI32 vs[1]!) (asI32 vs[0]!)) :: vs.drop 2)) Q E :=
  Spec.i32_binop (iadd_ 32) (fun x y => by constructor; exact wf_num_i32 (wf_iadd x y))
    (by binop_uniq (fun x y => wf_num_i32 (wf_iadd x y))) wf_iadd

@[spec] theorem Spec.i32_mul {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .MUL)] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ vs[1]! = i32v (asI32 vs[1]!) ∧
          2 ≤ vs.length⌝ : Prop) ⊓
        Q () z (i32v (imul_ 32 (asI32 vs[1]!) (asI32 vs[0]!)) :: vs.drop 2)) Q E :=
  Spec.i32_binop (imul_ 32) (fun x y => by constructor; exact wf_num_i32 (wf_imul x y))
    (by binop_uniq (fun x y => wf_num_i32 (wf_imul x y))) wf_imul

theorem wf_isub (x y : uN) : wf_uN 32 (isub_ 32 x y) := by
  simp only [isub_]
  refine .uN_case_0 _ _ ⟨by omega, ?_⟩ (by decide)
  have h := Int.tmod_lt_of_pos (Int.ofNat (2 ^ 32 + proj_uN_0 x) - Int.ofNat (proj_uN_0 y))
    (b := Int.ofNat (2 ^ 32)) (by decide)
  simp only [Int.ofNat_eq_coe] at h ⊢
  omega

@[spec] theorem Spec.i32_sub {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .SUB)] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ vs[1]! = i32v (asI32 vs[1]!) ∧
          2 ≤ vs.length⌝ : Prop) ⊓
        Q () z (i32v (isub_ 32 (asI32 vs[1]!) (asI32 vs[0]!)) :: vs.drop 2)) Q E :=
  Spec.i32_binop (isub_ 32) (fun x y => by constructor; exact wf_num_i32 (wf_isub x y))
    (by binop_uniq (fun x y => wf_num_i32 (wf_isub x y))) wf_isub

@[spec] theorem Spec.local_get {x : idx} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.LOCAL_GET x] : List instr)
      (fun z vs => (⌜(fun_local z x).isSome ∧ wf_val (fun_local z x).get!⌝ : Prop) ⊓
        Q () z ((fun_local z x).get! :: vs)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨hsome, hwf⟩, hq⟩ := hpre
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  rw [hv] at hwf hq
  exact Code.wp_local_get hv hwf hq

end SpecTecWP
