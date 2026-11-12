import SpecTecWP.Control
import SpecTecWP.InstrLocal

/-!
# Local variables

`fun_local_with_local` reads a local after a write. `Code.wp_local_set'` is the weakest
precondition of `local.set`: the well-formedness of the new state follows from the
well-formedness of the configuration.
-/

namespace SpecTecWP

theorem mem_modify_const {α : Type} {a o : α} :
    ∀ {L : List α} {i : Nat}, o ∈ L.modify i (fun _ => a) → o ∈ L ∨ o = a
  | [], _, h => by simp at h
  | b :: L, 0, h => by
    simp only [List.modify_zero_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr rfl
    · exact .inl (List.mem_cons_of_mem _ h)
  | b :: L, i + 1, h => by
    simp only [List.modify_succ_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl (List.mem_cons_self ..)
    · rcases mem_modify_const h with h | rfl
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr rfl

theorem wf_state_with_local {z : state} {x : idx} {v : val} (hz : wf_state z) (hv : wf_val v) :
    wf_state (with_local z x v) := by
  cases hz with
  | state_case_0 s f hs hf =>
    cases hf with
    | frame_case_ L mi hL hmi =>
      simp only [with_local, sof, fof, fun_store, fun_frame]
      refine .state_case_0 _ _ hs (.frame_case_ _ _ ?_ hmi)
      intro o ho
      rcases mem_modify_const ho with ho | rfl
      · exact hL o ho
      · intro w hw
        simp only [Option.toList_some, List.mem_singleton] at hw
        subst hw
        exact hv

theorem fun_local_with_local (z : state) (i j : Nat) (v : val) :
    fun_local (with_local z (.mk_uN i) v) (.mk_uN j) =
      if i = j ∧ i < (fof z).LOCALS.length then some v else fun_local z (.mk_uN j) := by
  obtain ⟨s, f⟩ := z
  simp only [fun_local, with_local, fof, sof, fun_frame, proj_uN_0]
  by_cases hij : i = j
  · subst hij
    simp only [true_and, List.getElem!_eq_getElem?_getD, List.getElem?_modify_eq]
    by_cases hi : i < f.LOCALS.length
    · simp [hi]
    · simp [hi]
  · simp [hij, List.getElem!_eq_getElem?_getD, List.getElem?_modify_ne _ _ hij]

@[simp] theorem locals_length_with_local (z : state) (x : idx) (v : val) :
    (fof (with_local z x v)).LOCALS.length = (fof z).LOCALS.length := by
  simp [with_local, fof, fun_frame]

theorem lt_length_of_fun_local {z : state} {i : Nat} {w : val}
    (h : fun_local z (.mk_uN i) = some w) : i < (fof z).LOCALS.length := by
  simp only [fun_local, proj_uN_0, List.getElem!_eq_getElem?_getD] at h
  refine Nat.lt_of_not_le fun hi => ?_
  rw [List.getElem?_eq_none hi] at h
  cases h

theorem Code.wp_local_set' {x : idx} {v : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hQ : Q (with_local z x v) vs) : Code.wp [.LOCAL_SET x] Q E z (v :: vs) := by
  intro hwf
  have hwf' := hwf
  rw [cfg_eq] at hwf'
  obtain ⟨hs, hi⟩ := wf_config_iff.mp hwf'
  have hv : wf_val v := wf_val_of_wf_instr (hi (instr_val v) (by simp))
  exact Code.wp_local_set (wf_state_with_local hs hv) hQ hwf

theorem Code.wp_conseq {is : List instr} {Q Q' : Assn} {E E' : EAssn} {z : state} {vs : Stack}
    (hQ : ∀ z vs, Q z vs → Q' z vs) (hE : ∀ e z, E e z → E' e z) (h : Code.wp is Q E z vs) :
    Code.wp is Q' E' z vs :=
  fun hwf => Safe.mono hQ hE (h hwf)

/-! ## Locals for `grind` -/

theorem fun_local_with_local_self {z : state} {i : Nat} {v : val}
    (h : (fun_local z (.mk_uN i)).isSome) :
    fun_local (with_local z (.mk_uN i) v) (.mk_uN i) = some v := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  rw [fun_local_with_local]
  simp [lt_length_of_fun_local hw]

theorem fun_local_with_local_ne {z : state} {i j : Nat} {v : val} (h : i ≠ j) :
    fun_local (with_local z (.mk_uN i) v) (.mk_uN j) = fun_local z (.mk_uN j) := by
  rw [fun_local_with_local]
  simp [h]

theorem sof_with_local (z : state) (x : idx) (v : val) : sof (with_local z x v) = sof z := by
  simp [with_local, sof, fun_store]

/-- Every local of a well-formed state is a well-formed value. -/
theorem wf_val_of_fun_local {z : state} {x : idx} {v : val} (hz : wf_state z)
    (h : fun_local z x = some v) : wf_val v := by
  cases hz with
  | state_case_0 s f hs hf =>
    cases hf with
    | frame_case_ L mi hL hmi =>
      simp only [fun_local, fof, fun_frame, List.getElem!_eq_getElem?_getD] at h
      cases hl : L[proj_uN_0 x]? with
      | none => rw [hl] at h; cases h
      | some o =>
        rw [hl] at h
        simp only [Option.getD_some] at h
        subst h
        exact hL _ (List.mem_of_getElem? hl) v (by simp)

attribute [grind =] fun_local_with_local_self fun_local_with_local_ne sof_with_local

end SpecTecWP
