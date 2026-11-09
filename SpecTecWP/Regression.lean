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

end SpecTecWP.Regression
