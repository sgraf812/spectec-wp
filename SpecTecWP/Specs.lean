import SpecTecWP.Locals
import SpecTecWP.Arith
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
      (fun z vs => (⌜(fun_local z x).isSome⌝ : Prop) ⊓ Q () z ((fun_local z x).get! :: vs)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨hsome, hq⟩ := hpre
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  rw [hv] at hq
  intro hwf
  have hs := (wf_config_iff.mp (by rwa [cfg_eq] at hwf)).1
  exact Code.wp_local_get hv (wf_val_of_fun_local hs hv) hq hwf

/-! ## `i32.eqz` and `i32.rem_u` -/

theorem wf_ieqz (x : uN) : wf_uN 32 (ieqz_ 32 x) := by
  simp only [ieqz_]
  refine .uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ (by decide)
  cases (proj_uN_0 x == 0) <;> decide

@[spec] theorem Spec.i32_eqz {Q : Unit → Assn} {E : EAssn} :
    Triple ([.TESTOP .I32 (.mk_testop__0 .I32 .EQZ)] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ 1 ≤ vs.length⌝ : Prop) ⊓
        Q () z (i32v (ieqz_ 32 (asI32 vs[0]!)) :: vs.drop 1)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, hlen⟩, hq⟩ := hpre
  rcases vs with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at h0 hq
    rw [h0]
    exact Code.wp_testop rfl (wf_ieqz _) hq

theorem wf_of_wf_num {x : uN} (h : wf_num_ .I32 (.mk_num__0 .I32 x)) : wf_uN 32 x := by
  cases h with | num__case_0 _ _ h _ => exact h

theorem wf_irem_u {x y : uN} (hx : wf_uN 32 x) : wf_uN 32 (irem_u x y) := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  cases hx with
  | uN_case_0 _ h1 h2 =>
    refine .uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ h2
    simp only [irem_u, proj_uN_0]
    exact Nat.le_trans (Nat.mod_le a b) h1.2

theorem fun_binop_rem_u {x y : uN} (hy : proj_uN_0 y ≠ 0) (hwr : wf_uN 32 (irem_u x y)) :
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 x) (.mk_num__0 .I32 y)
      (some [.mk_num__0 .I32 (irem_u x y)]) :=
  .fun_binop__case_8 .U x y (some (irem_u x y)) (fun_irem_u hy)
    (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hwr)
    (fun i hi => by
      simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact wf_num_i32 hwr)

theorem fun_binop_rem_u_uniq {x y : uN} (hy : proj_uN_0 y ≠ 0) (hwr : wf_uN 32 (irem_u x y)) :
    ∀ r, fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 x) (.mk_num__0 .I32 y) r →
      r = some [.mk_num__0 .I32 (irem_u x y)] := by
  intro r hr
  cases hr
  · rename_i _ _ hirem
    rw [fun_irem_u_uniq hy hirem]
    rfl
  · rename_i hneg
    exact absurd (.fun_binop__case_8 .U x y (some (irem_u x y)) (fun_irem_u hy)
      (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hwr)
      (fun i hi => by
        simp only [Option.toList_some, List.mem_singleton] at hi; subst hi
        exact wf_num_i32 hwr)) hneg

@[spec] theorem Spec.i32_rem_u {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 (.REM .U))] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ vs[1]! = i32v (asI32 vs[1]!) ∧
          2 ≤ vs.length ∧ proj_uN_0 (asI32 vs[0]!) ≠ 0⌝ : Prop) ⊓
        Q () z (i32v (irem_u (asI32 vs[1]!) (asI32 vs[0]!)) :: vs.drop 2)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen, hnz⟩, hq⟩ := hpre
  rcases vs with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons,
      List.drop_zero] at h0 h1 hq hnz
    rw [h0, h1]
    intro hwf
    have hwf' := hwf
    rw [cfg_eq] at hwf'
    obtain ⟨-, hi⟩ := wf_config_iff.mp hwf'
    have hwx : wf_uN 32 (asI32 v1) := by
      have := hi (.CONST .I32 (.mk_num__0 .I32 (asI32 v1))) (by simp [instr_val])
      cases this with | instr_case_76 _ _ h => exact wf_of_wf_num h
    have hwr := wf_irem_u (y := asI32 v0) hwx
    exact Code.wp_binop (fun_binop_rem_u hnz hwr) (fun_binop_rem_u_uniq hnz hwr)
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact wf_num_i32 hwr)
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact hq)
      (fun h => by simp at h) hwf

/-! ## `local.set` -/

@[spec] theorem Spec.local_set {x : idx} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.LOCAL_SET x] : List instr)
      (fun z vs => (⌜1 ≤ vs.length⌝ : Prop) ⊓ Q () (with_local z x vs[0]!) (vs.drop 1)) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨hlen, hq⟩ := hpre
  rcases vs with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at hq
    exact Code.wp_local_set' hq

/-! ## Control flow -/

@[spec] theorem Spec.br {l : labelidx} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BR l] : List instr) (fun z vs => E (.br l vs) z) Q E :=
  Triple.iff.mpr fun _ _ h => Code.wp_br h

@[spec] theorem Spec.br_if {l : labelidx} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BR_IF l] : List instr)
      (fun z vs => (⌜vs[0]! = i32v (asI32 vs[0]!) ∧ 1 ≤ vs.length⌝ : Prop) ⊓
        ((proj_uN_0 (asI32 vs[0]!) = 0 → Q () z (vs.drop 1)) ∧
          (proj_uN_0 (asI32 vs[0]!) ≠ 0 → E (.br l (vs.drop 1)) z))) Q E := by
  refine Triple.iff.mpr fun z vs hpre => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, hlen⟩, hF, hT⟩ := hpre
  rcases vs with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at h0 hF hT
    rw [h0]
    exact Code.wp_br_if hT hF

/-- A block with the empty block type: the body runs on the empty stack, `br 0` continues
after the block, and `br (l + 1)` leaves the block as `br l`. -/
@[spec] theorem Spec.block {B : List instr} {Q : Unit → Assn} {E : EAssn} :
    Triple ([.BLOCK (._RESULT none) B] : List instr)
      (fun z vs => Std.WP.wp B (fun _ z' bs => Q () z' (bs ++ vs))
        (fun e => match e with
          | .br (.mk_uN 0) _ => fun z' => Q () z' vs
          | .br (.mk_uN (l + 1)) bs => E (.br (.mk_uN l) (bs ++ vs))
          | .ret bs => E (.ret (bs ++ vs))
          | e => E e) z []) Q E := by
  refine Triple.iff.mpr fun z vs h => ?_
  rw [wp_eq] at h
  refine Code.wp_block (Code.wp_conseq (fun _ _ h => h) ?_ h)
  intro e z' he
  rcases e with ⟨⟨_ | l⟩, bs⟩ | bs | a | _
  · refine ⟨Nat.zero_le _, ?_⟩
    rw [List.take_zero, List.nil_append]
    exact fun _ => Safe.vals _ _ he
  all_goals exact he

/-- The termination measure of a loop. -/
@[spec_invariant_type] def LoopVariant : Type := state → Stack → Nat

/-- The invariant of a loop. -/
@[spec_invariant_type] def LoopInvariant : Type := Assn

/-- A loop with the empty block type: the body runs on the empty stack from every state
`z₀` and stack `vs₀` that satisfy the invariant, and `br 0` must restore the invariant and
decrease the variant. -/
@[spec] theorem Spec.loop {B : List instr} {Q : Unit → Assn} {E : EAssn}
    (var : LoopVariant) (inv : LoopInvariant)
    (step : ∀ z₀ vs₀, inv z₀ vs₀ →
      Std.WP.wp B (fun _ z bs => Q () z (bs ++ vs₀))
        (fun e => match e with
          | .br (.mk_uN 0) _ => fun z => inv z vs₀ ∧ var z vs₀ < var z₀ vs₀
          | .br (.mk_uN (l + 1)) bs => E (.br (.mk_uN l) (bs ++ vs₀))
          | .ret bs => E (.ret (bs ++ vs₀))
          | e => E e) z₀ []) :
    Triple ([.LOOP (._RESULT none) B] : List instr) (fun z vs => inv z vs) Q E := by
  refine Triple.iff.mpr fun z vs hI => ?_
  refine Code.wp_loop_inv (inv := inv) (var := var) (fun z₀ vs₀ hI₀ => ?_) hI
  have h := step z₀ vs₀ hI₀
  rw [wp_eq] at h
  refine Code.wp_conseq (fun _ _ h => h) ?_ h
  intro e z' he
  rcases e with ⟨⟨_ | l⟩, bs⟩ | bs | a | _ <;> exact he

/-! ## `grind` setup for the verification conditions

`open SpecTecWP` makes `grind`, and so `vcgen ... with finish`, normalize the stack accesses of
the specifications and read the values out of `some (i32v x)`. -/

attribute [scoped grind norm] List.getElem!_cons_zero List.getElem!_cons_succ
  List.drop_succ_cons List.drop_zero List.length_cons List.length_nil
  List.cons_append List.nil_append
attribute [scoped grind =] Option.get!_some asI32_i32v

end SpecTecWP
