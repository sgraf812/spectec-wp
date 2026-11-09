import Adequacy.Arith

/-!
# Adequacy on the straight-line fragment

`adequacy_straight`: if Talos establishes `P` and `epost` for a straight-line program `p`,
then every SpecTec reduction of the translation `tp p` terminates, and ends in the translated
postcondition. `epost` must reject `Invalid`, because SpecTec has no such outcome.
-/

namespace Adequacy

open SpecTecWP Std.WP Lean.Order

variable {m : Wasm.Module} {env : Wasm.HostEnv Wasm.U} {st : Wasm.Store Wasm.U}
  {Q : Unit → Wasm.Assn} {epost : Wasm.EAssn} {s : Wasm.Locals}

/-- The exception postcondition rejects every `Invalid` outcome. -/
def NoInvalid (epost : Wasm.EAssn) : Prop := ∀ msg st s, ¬ epost (.Invalid msg) st s

/-! ## Talos equations for the remaining instructions -/

section TalosEquations
open Wasm

theorem wp_and_eq' : Std.WP.wp (⟨m, env, [.and]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => Q () st { s with values := .i32 (a &&& b) :: vs }
     | _ => ∀ st' s', epost (.Invalid "and: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_or_eq' : Std.WP.wp (⟨m, env, [.or]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => Q () st { s with values := .i32 (a ||| b) :: vs }
     | _ => ∀ st' s', epost (.Invalid "or: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_xor_eq' : Std.WP.wp (⟨m, env, [.xor]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => Q () st { s with values := .i32 (a ^^^ b) :: vs }
     | _ => ∀ st' s', epost (.Invalid "xor: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_eq_eq' : Std.WP.wp (⟨m, env, [.eq]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => Q () st { s with values := .i32 (if a = b then 1 else 0) :: vs }
     | _ => ∀ st' s', epost (.Invalid "eq: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_ne_eq' : Std.WP.wp (⟨m, env, [.ne]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => Q () st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
     | _ => ∀ st' s', epost (.Invalid "ne: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_ltU_eq' : Std.WP.wp (⟨m, env, [.ltU]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => Q () st { s with values := .i32 (if a < b then 1 else 0) :: vs }
     | _ => ∀ st' s', epost (.Invalid "ltU: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_ltS_eq' : Std.WP.wp (⟨m, env, [.ltS]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       Q () st { s with values := .i32 (if a.toInt32 < b.toInt32 then 1 else 0) :: vs }
     | _ => ∀ st' s', epost (.Invalid "ltS: ill-shaped operand stack") st' s') := by
  wasm_eq

theorem wp_drop_eq' : Std.WP.wp (⟨m, env, [.drop]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | _ :: vs => Q () st { s with values := vs }
     | _ => ∀ st' s', epost (.Invalid "drop: empty operand stack") st' s') := by
  wasm_eq

theorem wp_nop_eq' : Std.WP.wp (⟨m, env, [.nop]⟩ : Wasm.Code) Q epost st s ↔ Q () st s := by
  wasm_eq

theorem wp_unreachable_eq' : Std.WP.wp (⟨m, env, [.unreachable]⟩ : Wasm.Code) Q epost st s ↔
    ∀ s', epost (.Trap "unreachable") st s' := by
  wasm_eq

end TalosEquations

/-! ## Values, frames and stacks -/

theorem wf_num_u (x : UInt32) : wf_num_ .I32 (.mk_num__0 .I32 (u x)) := by
  have := wf_tv (.i32 x); cases this; assumption

theorem wf_uN_u (x : UInt32) : wf_uN 32 (u x) := by
  have := wf_num_u x; cases this; assumption

theorem tv_i32 (x : UInt32) : tv (.i32 x) = .CONST .I32 (.mk_num__0 .I32 (u x)) := rfl

theorem zOf_values (s : Wasm.Locals) (vs : List Wasm.Value) :
    zOf { s with values := vs } = zOf s := rfl

theorem Code.wp_mono {c : List instr} {Q Q' : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hQ : ∀ z vs, Q z vs → Q' z vs) (h : Code.wp c Q E z vs) : Code.wp c Q' E z vs :=
  fun hwf => Safe.mono hQ (fun _ _ h => h) (h hwf)

theorem Locals.get_eq (s : Wasm.Locals) (n : Nat) : s.get n = (s.params ++ s.locals)[n]? := by
  simp only [Wasm.Locals.get]
  split
  · rw [List.getElem?_append_left (by omega)]
  · split
    · rw [List.getElem?_append_right (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega)]

theorem fun_local_zOf {s : Wasm.Locals} {n : Nat} {v : Wasm.Value} (h : s.get n = some v) :
    fun_local (zOf s) (.mk_uN n) = some (tv v) := by
  rw [Locals.get_eq] at h
  simp only [fun_local, fof, fun_frame, zOf, frameOf, proj_uN_0, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_map, h]
  rfl

theorem with_local_zOf {s s' : Wasm.Locals} {n : Nat} {v : Wasm.Value}
    (h : s.set? n v = some s') : with_local (zOf s) (.mk_uN n) (tv v) = zOf s' := by
  simp only [Wasm.Locals.set?] at h
  simp only [with_local, sof, fof, fun_frame, fun_store, zOf, frameOf, proj_uN_0]
  congr 1
  have hmod : ∀ (l : List (Option val)) (i : Nat) (a : Option val),
      List.modify l i (fun _ => a) = l.set i a := by
    intro l i a; induction l generalizing i with
    | nil => cases i <;> rfl
    | cons x xs ih => cases i <;> simp_all [List.modify]
  split at h
  · rename_i hn
    cases h
    simp only [hmod, List.map_append, List.map_set]
    rw [List.set_append_left n _ (by simpa using hn)]
  · split at h
    · rename_i hn hn'
      cases h
      simp only [hmod, List.map_append, List.map_set]
      rw [List.set_append_right n _ (by simp; omega), List.length_map]
    · cases h

theorem set_values {s s' : Wasm.Locals} {n : Nat} {v : Wasm.Value} (h : s.set? n v = some s') :
    s'.values = s.values := by
  simp only [Wasm.Locals.set?] at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-! ## Instructions -/

theorem sim_binop {op : binop_Inn} (f : UInt32 → UInt32 → UInt32) (g : uN → uN → uN)
    (hf : ∀ x y : UInt32, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u y))
      (.mk_num__0 .I32 (u x)) (some [.mk_num__0 .I32 (g (u y) (u x))]))
    (huniq : ∀ (x y : UInt32) r, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u y))
      (.mk_num__0 .I32 (u x)) r → r = some [.mk_num__0 .I32 (g (u y) (u x))])
    (hg : ∀ x y, g (u y) (u x) = u (f x y))
    {R : Unit → Wasm.Assn} {x y : UInt32} {vs : List Wasm.Value}
    (hv : s.values = .i32 x :: .i32 y :: vs) (h : R () st { s with values := .i32 (f x y) :: vs }) :
    Code.wp [.BINOP .I32 (.mk_binop__0 .I32 op)] (postT st (R ())) (epostT st epost) (zOf s) (stk s) := by
  rw [show stk s = .CONST .I32 (.mk_num__0 .I32 (u x)) :: .CONST .I32 (.mk_num__0 .I32 (u y)) ::
    vs.map tv by simp [stk, hv, tv_i32]]
  refine Code.wp_binop (hf x y) (huniq x y) ?_ ?_ ?_
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; rw [hg]; exact wf_num_u _
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc
    exact ⟨{ s with values := .i32 (f x y) :: vs }, rfl, by simp [stk, tv_i32, hg], h⟩
  · intro h; simp at h

theorem sim_relop {op : relop_Inn} (f : UInt32 → UInt32 → UInt32)
    (hf : ∀ x y : UInt32, fun_relop_ .I32 (.mk_relop__0 .I32 op) (.mk_num__0 .I32 (u y))
      (.mk_num__0 .I32 (u x)) = some (u (f x y)))
    {R : Unit → Wasm.Assn} {x y : UInt32} {vs : List Wasm.Value}
    (hv : s.values = .i32 x :: .i32 y :: vs) (h : R () st { s with values := .i32 (f x y) :: vs }) :
    Code.wp [.RELOP .I32 (.mk_relop__0 .I32 op)] (postT st (R ())) (epostT st epost) (zOf s) (stk s) := by
  rw [show stk s = .CONST .I32 (.mk_num__0 .I32 (u x)) :: .CONST .I32 (.mk_num__0 .I32 (u y)) ::
    vs.map tv by simp [stk, hv, tv_i32]]
  exact Code.wp_relop (hf x y) (wf_uN_u _)
    ⟨{ s with values := .i32 (f x y) :: vs }, rfl, by simp [stk, tv_i32], h⟩

/-- A Talos instruction of the fragment and its translation have corresponding weakest
preconditions. -/
theorem sim (i : Wasm.Instruction) (j : instr) (hti : ti i = some j) {R : Unit → Wasm.Assn}
    (hinv : NoInvalid epost) (h : Std.WP.wp (⟨m, env, [i]⟩ : Wasm.Code) R epost st s) :
    Code.wp [j] (postT st (R ())) (epostT st epost) (zOf s) (stk s) := by
  have inv : ∀ {msg}, (∀ st' s', epost (.Invalid msg) st' s') → False :=
    fun h' => hinv _ st s (h' st s)
  cases i <;> simp only [ti, Option.some.injEq, reduceCtorEq] at hti <;> subst hti
  case const n =>
    rw [Wasm.wp_const_eq] at h
    exact Code.wp_const ⟨{ s with values := .i32 n :: s.values }, rfl, by simp [stk], h⟩
  case constI64 n =>
    rw [Wasm.wp_constI64_eq] at h
    exact Code.wp_const ⟨{ s with values := .i64 n :: s.values }, rfl, by simp [stk], h⟩
  case add =>
    rw [Wasm.wp_add_eq] at h; split at h
    · exact sim_binop (fun x y => x + y) (iadd_ 32)
        (fun x y => by constructor; have := wf_num_u (x + y); rw [← iadd_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (x + y); rw [← iadd_eq] at this; exact this) hneg) (fun x y => iadd_eq x y) (by assumption) h
    · exact (inv h).elim
  case sub =>
    rw [Wasm.wp_sub_eq] at h; split at h
    · exact sim_binop (fun x y => y - x) (isub_ 32)
        (fun x y => by constructor; have := wf_num_u (y - x); rw [← isub_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (y - x); rw [← isub_eq] at this; exact this) hneg) (fun x y => isub_eq x y) (by assumption) h
    · exact (inv h).elim
  case mul =>
    rw [Wasm.wp_mul_eq] at h; split at h
    · exact sim_binop (fun x y => x * y) (imul_ 32)
        (fun x y => by constructor; have := wf_num_u (x * y); rw [← imul_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (x * y); rw [← imul_eq] at this; exact this) hneg) (fun x y => imul_eq x y) (by assumption) h
    · exact (inv h).elim
  case and =>
    rw [wp_and_eq'] at h; split at h
    · exact sim_binop (fun x y => x &&& y) (iand_ 32)
        (fun x y => by constructor; have := wf_num_u (x &&& y); rw [← iand_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (x &&& y); rw [← iand_eq] at this; exact this) hneg) (fun x y => iand_eq x y) (by assumption) h
    · exact (inv h).elim
  case or =>
    rw [wp_or_eq'] at h; split at h
    · exact sim_binop (fun x y => y ||| x) (ior_ 32)
        (fun x y => by constructor; have := wf_num_u (y ||| x); rw [← ior_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (y ||| x); rw [← ior_eq] at this; exact this) hneg) (fun x y => ior_eq y x) (by assumption) h
    · exact (inv h).elim
  case xor =>
    rw [wp_xor_eq'] at h; split at h
    · exact sim_binop (fun x y => y ^^^ x) (ixor_ 32)
        (fun x y => by constructor; have := wf_num_u (y ^^^ x); rw [← ixor_eq] at this; exact this)
        (fun x y r hr => by
          cases hr
          · rfl
          · rename_i hneg
            exact absurd (by constructor; have := wf_num_u (y ^^^ x); rw [← ixor_eq] at this; exact this) hneg) (fun x y => ixor_eq y x) (by assumption) h
    · exact (inv h).elim
  case eqz =>
    rw [Wasm.wp_eqz_eq] at h; split at h
    · rename_i a vs hv
      rw [show stk s = .CONST .I32 (.mk_num__0 .I32 (u a)) :: vs.map tv by simp [stk, hv, tv_i32]]
      exact Code.wp_testop (show fun_testop_ .I32 (.mk_testop__0 .I32 .EQZ) (.mk_num__0 .I32 (u a)) =
          some (u (if a = 0 then 1 else 0)) from congrArg some (ieqz_eq a)) (wf_uN_u _)
        ⟨{ s with values := .i32 (if a = 0 then 1 else 0) :: vs }, rfl, by simp [stk, tv_i32], h⟩
    · exact (inv h).elim
  case eq =>
    rw [wp_eq_eq'] at h; split at h
    · exact sim_relop (op := .EQ) (fun x y => if y = x then 1 else 0)
        (fun x y => congrArg some (ieq_eq y x)) (by assumption) h
    · exact (inv h).elim
  case ne =>
    rw [wp_ne_eq'] at h; split at h
    · exact sim_relop (op := .NE) (fun x y => if y ≠ x then 1 else 0)
        (fun x y => congrArg some (ine_eq y x)) (by assumption) h
    · exact (inv h).elim
  case ltU =>
    rw [wp_ltU_eq'] at h; split at h
    · exact sim_relop (op := (.LT .U)) (fun x y => if y < x then 1 else 0)
        (fun x y => congrArg some (ilt_u_eq y x)) (by assumption) h
    · exact (inv h).elim
  case ltS =>
    rw [wp_ltS_eq'] at h; split at h
    · exact sim_relop (op := (.LT .S)) (fun x y => if y.toInt32 < x.toInt32 then 1 else 0)
        (fun x y => congrArg some (ilt_s_eq y x)) (by assumption) h
    · exact (inv h).elim
  case localGet n =>
    rw [Wasm.wp_localGet_eq] at h; split at h
    · rename_i v hv
      exact Code.wp_local_get (fun_local_zOf hv) (wf_tv v)
        ⟨{ s with values := v :: s.values }, rfl, by simp [stk], h⟩
    · exact (inv h).elim
  case localSet n =>
    rw [Wasm.wp_localSet_eq] at h; split at h
    · rename_i v vs hv
      split at h
      · rename_i s' hs'
        rw [show stk s = tv v :: vs.map tv by simp [stk, hv]]
        refine Code.wp_local_set (by rw [with_local_zOf hs']; exact wf_zOf _)
          ⟨{ s' with values := vs }, by rw [with_local_zOf hs']; rfl, rfl, h⟩
      · exact (inv h).elim
    · exact (inv h).elim
  case localTee n =>
    rw [Wasm.wp_localTee_eq] at h; split at h
    · rename_i v vs hv
      split at h
      · rename_i s' hs'
        have hvals : s'.values = s.values := set_values hs'
        rw [show stk s = tv v :: vs.map tv by simp [stk, hv]]
        exact Code.wp_local_tee (Code.wp_local_set (by rw [with_local_zOf hs']; exact wf_zOf _)
          ⟨s', by rw [with_local_zOf hs'], by simp [stk, hvals, hv], h⟩)
      · exact (inv h).elim
    · exact (inv h).elim
  case drop =>
    rw [wp_drop_eq'] at h; split at h
    · rename_i v vs hv
      rw [show stk s = tv v :: vs.map tv by simp [stk, hv]]
      exact Code.wp_drop ⟨{ s with values := vs }, rfl, rfl, h⟩
    · exact (inv h).elim
  case nop =>
    rw [wp_nop_eq'] at h
    exact Code.wp_nop ⟨s, rfl, rfl, h⟩
  case unreachable =>
    rw [wp_unreachable_eq'] at h
    exact Code.wp_unreachable ⟨_, h⟩

/-- **Adequacy on the straight-line fragment.** If Talos establishes the postcondition `R`
and the exception postcondition `epost` for a program `p` of the fragment, then every
SpecTec reduction of its translation from the corresponding configuration terminates and
satisfies the translated postconditions. -/
theorem adequacy_straight (p : Wasm.Program) :
    ∀ (q : List instr), tp p = some q → ∀ {R : Unit → Wasm.Assn} {s : Wasm.Locals},
      NoInvalid epost → Std.WP.wp (⟨m, env, p⟩ : Wasm.Code) R epost st s →
      Code.wp q (postT st (R ())) (epostT st epost) (zOf s) (stk s) := by
  induction p with
  | nil =>
    intro q hq R s _ h
    simp only [tp, Option.some.injEq] at hq
    subst hq
    rw [Wasm.wp_nil_eq] at h
    intro _
    have := Safe.vals (Q := postT st (R ())) (E := epostT st epost) (zOf s) (stk s) ⟨s, rfl, rfl, h⟩
    simpa [cfg_eq] using this
  | cons i p ih =>
    intro q hq R s hinv h
    simp only [tp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hq
    obtain ⟨j, hj, q', hq', rfl⟩ := hq
    rw [Wasm.wp_cons_eq] at h
    have h₁ := sim i j hj hinv h
    have : Code.wp ([j] ++ q') (postT st (R ())) (epostT st epost) (zOf s) (stk s) :=
      Code.wp_append (Code.wp_mono (fun z vs hQ => by
        obtain ⟨s', rfl, rfl, h'⟩ := hQ
        exact ih q' hq' hinv h') h₁)
    simpa using this

end Adequacy
