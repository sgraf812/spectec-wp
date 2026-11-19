import SpecTecWP.View
import Std.Tactic.Do

/-!
# Specification triples for `vcgen`

The triples are over the view of `SpecTecWP.View`: a precondition is a predicate on a
`VState`, with the locals `s.locals`, the value `s.loc i` of the local `i`, and the stack
`s.stack`, top first. `Spec.cons` sequences the head of a list with its tail, and each
instruction has one `@[spec]` triple in total style. A read from the stack is `s.stack[i]!`,
an `i32` payload is `asI32`, and the partiality of an instruction is one closed `⌜…⌝` guard.
Each triple is proved from the weakest precondition of its instruction over the SpecTec model.
-/

namespace SpecTecWP

open Std.WP Lean.Order


/-! ## Sequencing -/

@[spec] theorem Spec.nil {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([] : List instr) (Q ()) Q E :=
  Triple.iff.mpr fun s hq _ _ hr _ => Safe.vals _ _ ⟨s, hr, hq⟩

@[spec] theorem Spec.cons {i j : instr} {q : List instr} {Q : Unit → VAssn} {E : VEAssn} :
    Triple (i :: j :: q) (Std.WP.wp [i] (fun _ => Std.WP.wp (j :: q) Q E) E) Q E := by
  refine Triple.iff.mpr fun s h z vs hr => ?_
  have h1 : Code.wp [i] (lift (Std.WP.wp (j :: q) Q E)) (liftE E) z vs := h z vs hr
  exact Code.wp_append (Code.wp_conseq (fun z' vs' ⟨s', hr', h'⟩ => h' z' vs' hr')
    (fun _ _ h => h) h1)

/-! ## Constants -/

@[spec] theorem Spec.i32_const {a : UInt32} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.CONST .I32 (.mk_num__0 .I32 (u a))] : List instr)
      (fun s => Q () { s with stack := .i32 a :: s.stack }) Q E := by
  refine Triple.iff.mpr fun s h z vs hr => ?_
  obtain ⟨hrf, rfl⟩ := hr
  exact Code.wp_const (c := (V.i32 a).enc) (lift_of (.i32 a :: s.stack) hrf rfl h)

@[spec] theorem Spec.i64_const {a : UInt64} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.toNat))] : List instr)
      (fun s => Q () { s with stack := .i64 a :: s.stack }) Q E := by
  refine Triple.iff.mpr fun s h z vs hr => ?_
  obtain ⟨hrf, rfl⟩ := hr
  exact Code.wp_const (c := (V.i64 a).enc) (lift_of (.i64 a :: s.stack) hrf rfl h)

/-! ## `i32` binary operators -/

theorem wf_mod (N i : Nat) : wf_uN N (.mk_uN (i % 2 ^ N)) := by
  have h1 := Nat.mod_lt i (Nat.two_pow_pos N)
  have h2 := Nat.two_pow_pos N
  refine .uN_case_0 _ _ ⟨by omega, ?_⟩ ?_ <;> simp only [Int.ofNat_eq_natCast] <;> omega

theorem wf_u (a : UInt32) : wf_uN 32 (u a) := by
  have := a.toNat_lt
  refine .uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ (by decide)
  simp only [Int.ofNat_eq_natCast]
  omega

theorem wf_num_i32 {x : uN} (h : wf_uN 32 x) : wf_num_ .I32 (.mk_num__0 .I32 x) :=
  .num__case_0 _ _ _ h rfl

/-- An `i32` binary operator: the model's operation `g` on payloads is `f` on `UInt32`. -/
theorem Spec.i32_binop {op : binop_Inn} (f : UInt32 → UInt32 → UInt32) (g : uN → uN → uN)
    (hf : ∀ a b : UInt32, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u b)) (some [.mk_num__0 .I32 (g (u a) (u b))]))
    (huniq : ∀ (a b : UInt32) r, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u b)) r → r = some [.mk_num__0 .I32 (g (u a) (u b))])
    (hwf : ∀ a b : UInt32, wf_uN 32 (g (u a) (u b))) (hg : ∀ a b, g (u a) (u b) = u (f a b))
    {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 op)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ s.stack[1]! = .i32 s.stack[1]!.asI32 ∧
          2 ≤ s.stack.length⌝ : Prop) ⊓
        Q () { s with stack := .i32 (f s.stack[1]!.asI32 s.stack[0]!.asI32) :: s.stack.drop 2 })
      Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen⟩, hq⟩ := hpre
  obtain ⟨hrf, rfl⟩ := hr
  obtain ⟨st, m, ls, stk⟩ := s
  rcases stk with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons,
      List.drop_zero] at h0 h1 hq
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := ⟨_, h0⟩
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := ⟨_, h1⟩
    simp only [V.asI32_i32] at hq
    refine Code.wp_binop (hf a1 a0) (huniq _ _)
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact wf_num_i32 (hwf _ _))
      (fun c hc => ?_) (fun h => by simp at h)
    simp only [List.mem_singleton] at hc
    subst hc
    rw [hg]
    exact ⟨⟨st, m, ls, .i32 (f a1 a0) :: rest⟩, ⟨hrf, rfl⟩, hq⟩

/-- The `otherwise` clause of `$binop_` does not apply to a defined `i32` operation. -/
macro "binop_uniq" w:term : tactic => `(tactic| (
  intro x y r hr
  cases hr
  · rfl
  · rename_i hneg; exact absurd (by constructor <;> (try decide) <;> exact $w _ _) hneg))

theorem wf_iadd (x y : uN) : wf_uN 32 (iadd_ 32 x y) := wf_mod 32 _
theorem wf_imul (x y : uN) : wf_uN 32 (imul_ 32 x y) := wf_mod 32 _

theorem wf_isub (x y : uN) : wf_uN 32 (isub_ 32 x y) := by
  simp only [isub_]
  refine .uN_case_0 _ _ ⟨by omega, ?_⟩ (by decide)
  have h := Int.tmod_lt_of_pos (Int.ofNat (2 ^ 32 + proj_uN_0 x) - Int.ofNat (proj_uN_0 y))
    (b := Int.ofNat (2 ^ 32)) (by decide)
  simp only [Int.ofNat_eq_natCast] at h ⊢
  omega

@[spec] theorem Spec.i32_add {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .ADD)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ s.stack[1]! = .i32 s.stack[1]!.asI32 ∧
          2 ≤ s.stack.length⌝ : Prop) ⊓
        Q () { s with stack := .i32 (s.stack[1]!.asI32 + s.stack[0]!.asI32) :: s.stack.drop 2 })
      Q E :=
  Spec.i32_binop (· + ·) (iadd_ 32)
    (fun x y => by constructor <;> (try decide) <;> exact wf_num_i32 (wf_iadd _ _))
    (by binop_uniq (fun x y => wf_num_i32 (wf_iadd (u x) (u y)))) (fun _ _ => wf_iadd _ _)
    (fun a b => by rw [iadd_eq, UInt32.add_comm])

@[spec] theorem Spec.i32_sub {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .SUB)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ s.stack[1]! = .i32 s.stack[1]!.asI32 ∧
          2 ≤ s.stack.length⌝ : Prop) ⊓
        Q () { s with stack := .i32 (s.stack[1]!.asI32 - s.stack[0]!.asI32) :: s.stack.drop 2 })
      Q E :=
  Spec.i32_binop (· - ·) (isub_ 32)
    (fun x y => by
      constructor <;> first | decide | exact wf_num_i32 (wf_isub _ _) | exact isub_nonneg _ _)
    (by
      intro x y r hr
      cases hr
      · rfl
      · rename_i hneg
        exact absurd (by
          constructor <;> first | decide | exact wf_num_i32 (wf_isub _ _) |
            exact isub_nonneg _ _) hneg)
    (fun _ _ => wf_isub _ _) (fun a b => isub_eq b a)

@[spec] theorem Spec.i32_mul {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 .MUL)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ s.stack[1]! = .i32 s.stack[1]!.asI32 ∧
          2 ≤ s.stack.length⌝ : Prop) ⊓
        Q () { s with stack := .i32 (s.stack[1]!.asI32 * s.stack[0]!.asI32) :: s.stack.drop 2 })
      Q E :=
  Spec.i32_binop (· * ·) (imul_ 32)
    (fun x y => by constructor <;> (try decide) <;> exact wf_num_i32 (wf_imul _ _))
    (by binop_uniq (fun x y => wf_num_i32 (wf_imul (u x) (u y)))) (fun _ _ => wf_imul _ _)
    (fun a b => by rw [imul_eq, UInt32.mul_comm])

/-! ## `i32.rem_u` and `i32.eqz` -/

theorem wf_irem_u {x y : uN} (hx : wf_uN 32 x) : wf_uN 32 (irem_u x y) := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  cases hx with
  | uN_case_0 _ h1 h2 =>
    refine .uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ h2
    simp only [proj_uN_0]
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
    exact absurd (.fun_binop__case_8 .U x y none) hneg

theorem proj_u_ne_zero {a : UInt32} (h : a ≠ 0) : proj_uN_0 (u a) ≠ 0 :=
  fun h0 => h (UInt32.toNat_inj.mp (h0 : a.toNat = 0))

@[spec] theorem Spec.i32_rem_u {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BINOP .I32 (.mk_binop__0 .I32 (.REM .U))] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ s.stack[1]! = .i32 s.stack[1]!.asI32 ∧
          2 ≤ s.stack.length ∧ s.stack[0]!.asI32 ≠ 0⌝ : Prop) ⊓
        Q () { s with stack := .i32 (s.stack[1]!.asI32 % s.stack[0]!.asI32) :: s.stack.drop 2 })
      Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, h1, hlen, hnz⟩, hq⟩ := hpre
  obtain ⟨hrf, rfl⟩ := hr
  obtain ⟨st, m, ls, stk⟩ := s
  rcases stk with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons,
      List.drop_zero] at h0 h1 hq hnz
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := ⟨_, h0⟩
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := ⟨_, h1⟩
    simp only [V.asI32_i32] at hq hnz
    have hy := proj_u_ne_zero hnz
    have hwr := wf_irem_u (y := u a0) (wf_u a1)
    refine Code.wp_binop (fun_binop_rem_u hy hwr) (fun_binop_rem_u_uniq hy hwr)
      (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact wf_num_i32 hwr)
      (fun c hc => ?_) (fun h => by simp at h)
    simp only [List.mem_singleton] at hc
    subst hc
    rw [irem_u_eq]
    exact ⟨⟨st, m, ls, .i32 (a1 % a0) :: rest⟩, ⟨hrf, rfl⟩, hq⟩

theorem wf_ieqz (x : uN) : wf_uN 32 (ieqz_ 32 x) := by
  simp only [ieqz_]
  refine .uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ (by decide)
  cases (proj_uN_0 x == 0) <;> decide

@[spec] theorem Spec.i32_eqz {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.TESTOP .I32 (.mk_testop__0 .I32 .EQZ)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ 1 ≤ s.stack.length⌝ : Prop) ⊓
        Q () { s with stack := .i32 (if s.stack[0]!.asI32 = 0 then 1 else 0) :: s.stack.drop 1 })
      Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, hlen⟩, hq⟩ := hpre
  obtain ⟨hrf, rfl⟩ := hr
  obtain ⟨st, m, ls, stk⟩ := s
  rcases stk with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at h0 hq
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := ⟨_, h0⟩
    simp only [V.asI32_i32] at hq
    refine Code.wp_testop (u := ieqz_ 32 (u a0)) rfl (wf_ieqz _) ?_
    rw [ieqz_eq]
    exact ⟨⟨st, m, ls, .i32 (if a0 = 0 then 1 else 0) :: rest⟩, ⟨hrf, rfl⟩, hq⟩

/-! ## Locals -/

@[spec] theorem Spec.local_get {i : Nat} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.LOCAL_GET (.mk_uN i)] : List instr)
      (fun s => (⌜(s.loc i).isSome⌝ : Prop) ⊓
        Q () { s with stack := (s.loc i).get! :: s.stack }) Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨hsome, hq⟩ := hpre
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  rw [hv, Option.get!_some] at hq
  have hl : fun_local z (.mk_uN i) = some v.enc := by rw [hr.get_local, hv]; rfl
  intro hwf
  have hz := (wf_config_iff.mp (by rwa [cfg_eq] at hwf)).1
  obtain ⟨hrf, rfl⟩ := hr
  exact Code.wp_local_get hl (wf_val_of_fun_local hz hl) (lift_of (v :: s.stack) hrf rfl hq) hwf

@[spec] theorem Spec.local_set {i : Nat} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.LOCAL_SET (.mk_uN i)] : List instr)
      (fun s => (⌜1 ≤ s.stack.length ∧ i < s.locals.length⌝ : Prop) ⊓
        Q () { s with locals := s.locals.set i (some s.stack[0]!), stack := s.stack.drop 1 })
      Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨hlen, hi⟩, hq⟩ := hpre
  obtain ⟨hrf, rfl⟩ := hr
  have hx : proj_uN_0 (.mk_uN i) < (fof z).LOCALS.length := by
    simpa [proj_uN_0, hrf.2.2] using hi
  obtain ⟨st, m, ls, stk⟩ := s
  rcases stk with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at hq
    exact Code.wp_local_set' hx
      ⟨_, Rep.set_local (s := ⟨st, m, ls, rest⟩) (i := i) v0 ⟨hrf, rfl⟩, hq⟩

/-! ## Control flow -/

@[spec] theorem Spec.br {l : Nat} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BR (.mk_uN l)] : List instr) (fun s => E (.br l) s) Q E :=
  Triple.iff.mpr fun s h _ _ hr => Code.wp_br ⟨s, hr, h⟩

@[spec] theorem Spec.br_if {l : Nat} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BR_IF (.mk_uN l)] : List instr)
      (fun s => (⌜s.stack[0]! = .i32 s.stack[0]!.asI32 ∧ 1 ≤ s.stack.length⌝ : Prop) ⊓
        ((s.stack[0]!.asI32 = 0 → Q () { s with stack := s.stack.drop 1 }) ∧
          (s.stack[0]!.asI32 ≠ 0 → E (.br l) { s with stack := s.stack.drop 1 }))) Q E := by
  refine Triple.iff.mpr fun s hpre z vs hr => ?_
  simp only [meet_prop_eq_and, CompleteLattice.ofProp_prop_eq] at hpre
  obtain ⟨⟨h0, hlen⟩, hF, hT⟩ := hpre
  obtain ⟨hrf, rfl⟩ := hr
  obtain ⟨st, m, ls, stk⟩ := s
  rcases stk with _ | ⟨v0, rest⟩
  · simp at hlen
  · simp only [List.getElem!_cons_zero, List.drop_succ_cons, List.drop_zero] at h0 hF hT
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := ⟨_, h0⟩
    simp only [V.asI32_i32] at hF hT
    exact Code.wp_br_if (x := u a0)
      (fun h => ⟨⟨st, m, ls, rest⟩, ⟨hrf, rfl⟩, hT fun e => h (by rw [e]; rfl)⟩)
      (fun h => ⟨⟨st, m, ls, rest⟩, ⟨hrf, rfl⟩, hF (UInt32.toNat_inj.mp (h : a0.toNat = 0))⟩)

/-- A block with the empty block type: the body runs on the empty stack, `br 0` continues
after the block, and `br (l + 1)` leaves the block as `br l`. -/
@[spec] theorem Spec.block {B : List instr} {Q : Unit → VAssn} {E : VEAssn} :
    Triple ([.BLOCK (._RESULT none) B] : List instr)
      (fun s => Std.WP.wp B (fun _ s' => Q () { s' with stack := s'.stack ++ s.stack })
        (fun e => match e with
          | .br 0 => fun s' => Q () { s' with stack := s.stack }
          | .br (l + 1) => fun s' => E (.br l) { s' with stack := s'.stack ++ s.stack }
          | .ret => fun s' => E .ret { s' with stack := s'.stack ++ s.stack }
          | e => E e) { s with stack := [] }) Q E := by
  refine Triple.iff.mpr fun s h z vs hr => ?_
  obtain ⟨hrf, rfl⟩ := hr
  have hb := h z [] ⟨hrf, rfl⟩
  refine Code.wp_block (Code.wp_conseq ?_ ?_ hb)
  · rintro z' bs ⟨s', ⟨hrf', rfl⟩, hq⟩
    exact lift_of (s'.stack ++ s.stack) hrf' (by simp) hq
  · intro e z' he
    rcases e with ⟨⟨_ | l⟩, bs⟩ | bs | a | _
    · obtain ⟨s', ⟨hrf', rfl⟩, hq⟩ := he
      refine ⟨Nat.zero_le _, ?_⟩
      rw [List.take_zero, List.nil_append]
      exact fun _ => Safe.vals _ _ (lift_of s.stack hrf' rfl hq)
    · obtain ⟨s', ⟨hrf', rfl⟩, hq⟩ := he
      exact lift_of (s'.stack ++ s.stack) hrf' (by simp) hq
    · obtain ⟨s', ⟨hrf', rfl⟩, hq⟩ := he
      exact lift_of (s'.stack ++ s.stack) hrf' (by simp) hq
    · exact he
    · exact he

/-- The termination measure of a loop. -/
@[spec_invariant_type] def LoopVariant : Type := VState → Nat

/-- The invariant of a loop. -/
@[spec_invariant_type] def LoopInvariant : Type := VAssn

/-- A loop with the empty block type: the body runs on the empty stack from every `s₀` that
satisfies the invariant, and `br 0` must restore the invariant and decrease the variant. -/
@[spec] theorem Spec.loop {B : List instr} {Q : Unit → VAssn} {E : VEAssn}
    (var : LoopVariant) (inv : LoopInvariant)
    (step : ∀ s₀, inv s₀ →
      Std.WP.wp B (fun _ s => Q () { s with stack := s.stack ++ s₀.stack })
        (fun e => match e with
          | .br 0 => fun s =>
              inv { s with stack := s₀.stack } ∧ var { s with stack := s₀.stack } < var s₀
          | .br (l + 1) => fun s => E (.br l) { s with stack := s.stack ++ s₀.stack }
          | .ret => fun s => E .ret { s with stack := s.stack ++ s₀.stack }
          | e => E e) { s₀ with stack := [] }) :
    Triple ([.LOOP (._RESULT none) B] : List instr) (fun s => inv s) Q E := by
  refine Triple.iff.mpr fun s hI z vs hr => ?_
  let inv' : Assn := fun z vs => ∃ s, Rep s z vs ∧ inv s
  let var' : state → Stack → Nat := fun z vs =>
    @dite _ (∃ s, Rep s z vs) (Classical.propDecidable _) (fun h => var h.choose) (fun _ => 0)
  have hvar : ∀ {s z vs}, Rep s z vs → var' z vs = var s := by
    intro s z vs hr
    have h : ∃ s, Rep s z vs := ⟨s, hr⟩
    show @dite _ (∃ s, Rep s z vs) (Classical.propDecidable _) (fun h => var h.choose)
      (fun _ => 0) = var s
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact congrArg var (Rep.unique (Exists.choose_spec (of_eq_true (eq_true h))) hr)
  refine Code.wp_loop_inv (inv := inv') (var := var') (fun z₀ vs₀ hI₀ => ?_) ⟨s, hr, hI⟩
  obtain ⟨s₀, hr₀, hI₀⟩ := hI₀
  obtain ⟨hrf₀, rfl⟩ := hr₀
  have hb := step s₀ hI₀ z₀ [] ⟨hrf₀, rfl⟩
  refine Code.wp_conseq ?_ ?_ hb
  · rintro z' bs ⟨s', ⟨hrf', rfl⟩, hq⟩
    exact lift_of (s'.stack ++ s₀.stack) hrf' (by simp) hq
  · intro e z' he
    rcases e with ⟨⟨_ | l⟩, bs⟩ | bs | a | _
    · obtain ⟨s', ⟨hrf', rfl⟩, hI', hlt⟩ := he
      have hr' : Rep { s' with stack := s₀.stack } z' (s₀.stack.map V.enc) := ⟨hrf', rfl⟩
      refine ⟨⟨_, hr', hI'⟩, ?_⟩
      have e1 := hvar hr'
      have e2 := hvar (s := s₀) ⟨hrf₀, rfl⟩
      omega
    · obtain ⟨s', ⟨hrf', rfl⟩, hq⟩ := he
      exact lift_of (s'.stack ++ s₀.stack) hrf' (by simp) hq
    · obtain ⟨s', ⟨hrf', rfl⟩, hq⟩ := he
      exact lift_of (s'.stack ++ s₀.stack) hrf' (by simp) hq
    · exact he
    · exact he

/-! ## `grind` setup for the verification conditions

`open SpecTecWP` lets `grind`, and so `vcgen ... with finish`, read the entries of a list of
known shape, also when the list is known only through an equation such as
`s.locals = [some (.i32 a)]`. -/

attribute [scoped grind =] List.getElem!_cons_zero List.getElem!_cons_succ

end SpecTecWP
