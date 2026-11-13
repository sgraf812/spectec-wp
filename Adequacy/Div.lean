import Adequacy.Translate

/-!
# Division and remainder

The `i32` operators `div_u` and `rem_u` are partial: a divisor `0` traps, in Talos and in the
SpecTec model. `sim_binop_rs` simulates a binary operator whose `$binop_` result `rs` is a
list of one value or empty, and the lemmas below compute `rs` for both operators.
-/

namespace Adequacy

open SpecTecWP Std.WP Lean.Order

variable {m : Wasm.Module} {env : Wasm.HostEnv Wasm.U} {st : Wasm.Store Wasm.U}
  {Q : Unit → Wasm.Assn} {epost : Wasm.EAssn} {s : Wasm.Locals}

section TalosEquations
open Wasm

theorem wp_divU_eq' : Std.WP.wp (⟨m, env, [.divU]⟩ : Wasm.Code) Q epost st s ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then ∀ s', epost (.Trap "integer divide by zero") st s'
       else Q () st { s with values := .i32 (a / b) :: vs }
     | _ => ∀ st' s', epost (.Invalid "divU: ill-shaped operand stack") st' s') := by
  wasm_eq

end TalosEquations

/-- A binary `i32` operator with the results `rs`: the value of the result, or a trap. -/
theorem sim_binop_rs {op : binop_Inn} {R : Unit → Wasm.Assn} {x y : UInt32}
    {vs : List Wasm.Value} {rs : List num_}
    (hf : fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u y)) (.mk_num__0 .I32 (u x))
      (some rs))
    (huniq : ∀ r, fun_binop_ .I32 (.mk_binop__0 .I32 op) (.mk_num__0 .I32 (u y))
      (.mk_num__0 .I32 (u x)) r → r = some rs)
    (hv : s.values = .i32 x :: .i32 y :: vs)
    (hQ : ∀ c ∈ rs, ∃ w : UInt32, c = .mk_num__0 .I32 (u w) ∧
      R () st { s with values := .i32 w :: vs })
    (hE : rs = [] → ∃ msg, ∀ s', epost (.Trap msg) st s') :
    Code.wp [.BINOP .I32 (.mk_binop__0 .I32 op)] (postT st (R ())) (epostT st epost) (zOf s)
      (stk s) := by
  rw [show stk s = .CONST .I32 (.mk_num__0 .I32 (u x)) :: .CONST .I32 (.mk_num__0 .I32 (u y)) ::
    vs.map tv by simp [stk, hv, tv_i32]]
  refine Code.wp_binop hf huniq ?_ ?_ hE
  · intro c hc
    obtain ⟨w, rfl, -⟩ := hQ c hc
    exact wf_num_u w
  · intro c hc
    obtain ⟨w, rfl, h⟩ := hQ c hc
    exact ⟨{ s with values := .i32 w :: vs }, rfl, by simp [stk, tv_i32], h⟩

/-! ## `div_u` -/

theorem fun_binop_div_u {a b : UInt32} (hb : b ≠ 0) :
    fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U)) (.mk_num__0 .I32 (u a)) (.mk_num__0 .I32 (u b))
      (some [.mk_num__0 .I32 (u (a / b))]) := by
  have hw : wf_uN 32 (u (a / b)) := wf_uN_u _
  rw [u_div] at hw ⊢
  exact .fun_binop__case_6 .U (u a) (u b) _ (fun_idiv_u (toNat_ne_zero hb) hw)
    (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hw)
    (fun i hi => by
      simp only [Option.toList_some, List.mem_singleton] at hi; subst hi
      exact .num__case_0 _ _ _ hw rfl)

theorem fun_binop_div_u_uniq {a b : UInt32} (hb : b ≠ 0) (r : Option (List num_))
    (hr : fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U)) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u b)) r) : r = some [.mk_num__0 .I32 (u (a / b))] := by
  cases hr
  · rename_i _ _ hid
    rw [fun_idiv_u_uniq (toNat_ne_zero hb) hid, u_div]
    rfl
  · rename_i hneg
    have hw : wf_uN 32 (.mk_uN (a.toNat / b.toNat)) := by rw [← u_div]; exact wf_uN_u _
    exact (hneg (.fun_binop__case_6 .U (u a) (u b) _ (fun_idiv_u (toNat_ne_zero hb) hw)
      (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hw)
      (fun i hi => by
        simp only [Option.toList_some, List.mem_singleton] at hi; subst hi
        exact .num__case_0 _ _ _ hw rfl))).elim

theorem fun_binop_div_u_zero (a : UInt32) :
    fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U)) (.mk_num__0 .I32 (u a)) (.mk_num__0 .I32 (u 0))
      (some []) :=
  .fun_binop__case_6 .U (u a) (u 0) none (.fun_idiv__case_0 _ _) (fun _ h => by cases h)
    (fun _ h => by cases h)

theorem fun_binop_div_u_zero_uniq (a : UInt32) (r : Option (List num_))
    (hr : fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U)) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u 0)) r) : r = some [] := by
  cases hr
  · rename_i _ _ hid
    rw [fun_idiv_u_zero_uniq hid]
    rfl
  · rename_i hneg
    exact (hneg (.fun_binop__case_6 .U (u a) (u 0) none (.fun_idiv__case_0 _ _)
      (fun _ h => by cases h) (fun _ h => by cases h))).elim

/-! ## `rem_u` -/

theorem fun_binop_rem_u {a b : UInt32} (hb : b ≠ 0) :
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 (u a)) (.mk_num__0 .I32 (u b))
      (some [.mk_num__0 .I32 (u (a % b))]) := by
  have hw : wf_uN 32 (u (a % b)) := wf_uN_u _
  rw [← irem_u_eq] at hw ⊢
  exact .fun_binop__case_8 .U (u a) (u b) _ (fun_irem_u (toNat_ne_zero hb))
    (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hw)
    (fun i hi => by
      simp only [Option.toList_some, List.mem_singleton] at hi; subst hi
      exact .num__case_0 _ _ _ hw rfl)

theorem fun_binop_rem_u_uniq {a b : UInt32} (hb : b ≠ 0) (r : Option (List num_))
    (hr : fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u b)) r) : r = some [.mk_num__0 .I32 (u (a % b))] := by
  cases hr
  · rename_i _ _ hir
    rw [fun_irem_u_uniq (toNat_ne_zero hb) hir, ← irem_u_eq]
    rfl
  · rename_i hneg
    have hw : wf_uN 32 (irem_u (u a) (u b)) := by rw [irem_u_eq]; exact wf_uN_u _
    exact (hneg (.fun_binop__case_8 .U (u a) (u b) _ (fun_irem_u (toNat_ne_zero hb))
      (fun i hi => by simp only [Option.toList_some, List.mem_singleton] at hi; subst hi; exact hw)
      (fun i hi => by
        simp only [Option.toList_some, List.mem_singleton] at hi; subst hi
        exact .num__case_0 _ _ _ hw rfl))).elim

theorem fun_binop_rem_u_zero (a : UInt32) :
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 (u a)) (.mk_num__0 .I32 (u 0))
      (some []) :=
  .fun_binop__case_8 .U (u a) (u 0) none (.fun_irem__case_0 _ _) (fun _ h => by cases h)
    (fun _ h => by cases h)

theorem fun_binop_rem_u_zero_uniq (a : UInt32) (r : Option (List num_))
    (hr : fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U)) (.mk_num__0 .I32 (u a))
      (.mk_num__0 .I32 (u 0)) r) : r = some [] := by
  cases hr
  · rename_i _ _ hir
    rw [fun_irem_u_zero_uniq hir]
    rfl
  · rename_i hneg
    exact (hneg (.fun_binop__case_8 .U (u a) (u 0) none (.fun_irem__case_0 _ _)
      (fun _ h => by cases h) (fun _ h => by cases h))).elim

end Adequacy
