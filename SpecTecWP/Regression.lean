import SpecTecWP.Wasm

/-!
# Regression tests for the Lean backend of SpecTec

Each test states a fact of the WebAssembly specification that an earlier version of the
generated model contradicted.
-/

namespace SpecTecWP.Regression

theorem exists_zip_of_mem {α β : Type} {xs : List α} {ys : List β} {x : α}
    (hlen : xs.length = ys.length) (hx : x ∈ xs) : ∃ y, (x, y) ∈ List.zip xs ys := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨ys[i]'(hlen ▸ hi), List.mem_iff_getElem.mpr
    ⟨i, by simp only [List.length_zip]; omega, by simp⟩⟩

theorem length_le_concat (l : List (List byte)) (h : ∀ x ∈ l, 1 ≤ x.length) :
    l.length ≤ (concat_ byte l).length := by
  induction l with
  | nil => simp [concat_]
  | cons x xs ih =>
    simp only [concat_, List.length_append, List.length_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- UTF-8 encodes every character with at least one byte. The iteration `$utf8(ch)*` over
`ch*` has one encoding per character. -/
theorem utf8_length {cs : List char} {bs : List byte} (h : fun_utf8 cs bs) :
    cs.length ≤ bs.length := by
  induction h with
  | fun_utf8_case_0 ch_lst _ _ var_0_lst _ _ h0 _ _ _ _ hlen0 _ _ ih0 =>
    refine hlen0 ▸ length_le_concat var_0_lst fun x hx => ?_
    obtain ⟨y, hy⟩ := exists_zip_of_mem hlen0 hx
    simpa using ih0 x y hy
  | _ => simp

theorem not_utf8_nil (c : char) : ¬ fun_utf8 [c] [] := fun h => by
  simpa using utf8_length h

/-- Equality on the mutually recursive type group is lawful, so a `==` condition can be
proved. -/
example : ((valtype.I32 : valtype) == .I32) = true := by simp
example : LawfulBEq instr := inferInstance
example : LawfulBEq deftype := inferInstance

/-- A partial function is defined on its domain: `$zsize(I32) = 32`. -/
example : zsize .I32 = some 32 := rfl

/-- `$funcsxa` keeps every function address: its `otherwise` clause applies only to an
external address that is not a function. -/
theorem not_funcsxa_skip : ¬ fun_funcsxa [.FUNC 5] [] := by
  intro h
  generalize hx : ([.FUNC 5] : List externaddr) = xs at h
  generalize hy : ([] : List funcaddr) = ys at h
  cases h with
  | fun_funcsxa_case_0 => simp at hx
  | fun_funcsxa_case_1 a xa var_0 _ => simp at hy
  | fun_funcsxa_case_2 v xa var_0 hneg _ =>
    simp only [List.singleton_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact hneg (.fun_funcsxa_case_1 5 [] [])

/-! The hand-written integer operations on concrete values (WebAssembly 3.0, 4.3). -/
example : iclz_ 32 (.mk_uN 1) = .mk_uN 31 := by decide
example : ishr_ 32 .S (.mk_uN 0xFFFFFFF0) (.mk_uN 4) = .mk_uN 0xFFFFFFFF := by decide
example : ishr_ 32 .U (.mk_uN 0xFFFFFFF0) (.mk_uN 36) = .mk_uN 0x0FFFFFFF := by decide
example : ilt_ 32 .S (.mk_uN 0xFFFFFFFF) (.mk_uN 0) = .mk_uN 1 := by decide
example : ilt_ 32 .U (.mk_uN 0xFFFFFFFF) (.mk_uN 0) = .mk_uN 0 := by decide
example : wrap__ 64 32 (.mk_uN 0x100000005) = .mk_uN 5 := by decide
example : extend__ 8 32 .S (.mk_uN 0x80) = .mk_uN 0xFFFFFF80 := by decide
example : iadd_sat_ 8 .S (.mk_uN 0x7F) (.mk_uN 1) = .mk_uN 0x7F := by decide
example : truncz (-7/2) = -3 := by unfold truncz Builtins.truncz; decide +kernel
example : ibytes_ 32 (.mk_uN 0x01020304) = [.mk_byte 4, .mk_byte 3, .mk_byte 2, .mk_byte 1] := by
  decide

/-- An unsigned remainder by zero has no result, so `i32.rem_u` traps: the second clause of
`$irem_` divides by `i_2`, which is undefined at `0`. -/
theorem not_irem_by_zero : ¬ fun_irem_ 32 .U (.mk_uN 5) (.mk_uN 0) (some (.mk_uN 5)) := by
  intro h
  generalize hr : (some (.mk_uN 5) : Option iN) = r at h
  cases h with
  | fun_irem__case_0 => simp at hr
  | fun_irem__case_1 =>
    simp only [proj_uN_0] at *
    exact absurd rfl ‹Rat.ofInt (Int.ofNat 0) ≠ 0›

end SpecTecWP.Regression
