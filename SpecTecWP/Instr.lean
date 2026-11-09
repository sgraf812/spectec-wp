import SpecTecWP.Exits

/-!
# Weakest preconditions of single instructions

Each lemma gives a sufficient condition for `Code.wp [i] Q E z vs`: the step exists, and
every successor satisfies `Q` or `E`.
-/

namespace SpecTecWP

theorem cfg_eq (z : state) (vs : Stack) (is : List instr) :
    cfg z vs is = .mk_config z (vs.reverse.map instr_val ++ is) := rfl

/-- A step of a sequence `R` is a step of `R` under the values `ws`. -/
theorem Step.under {z z' : state} {R R' : List instr} (ws : List val)
    (h : Step (.mk_config z R) (.mk_config z' R'))
    (hwf : wf_config (.mk_config z (ws.map instr_val ++ R))) :
    Step (.mk_config z (ws.map instr_val ++ R)) (.mk_config z' (ws.map instr_val ++ R')) := by
  have := Step.frame ws [] h (by simpa using hwf)
  simpa using this

theorem wf_config_of_cons_iff {z : state} {L : List instr} :
    wf_config (.mk_config z L) ↔ wf_state z ∧ ∀ i ∈ L, wf_instr i := wf_config_iff

/-- The values under the top two values of a stack. -/
theorem split_two {ws ws₁ : List val} {a b a' b' : val}
    (h : ws ++ [a, b] = ws₁ ++ [a', b']) : ws = ws₁ ∧ a = a' ∧ b = b' := by
  have h' := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

theorem split_one {ws ws₁ : List val} {a a' : val}
    (h : ws ++ [a] = ws₁ ++ [a']) : ws = ws₁ ∧ a = a' := by
  have h' := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h'
  exact ⟨h'.1, h'.2⟩

/-! ## Binary operators -/

theorem Step_pure.binop_redex {ws : List val} {nt : numtype} {op : binop_} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.BINOP nt op]) L) :
    ∃ (c₁ c₂ : num_) (r : Option (List num_)),
      ws = [.CONST nt c₁, .CONST nt c₂] ∧ fun_binop_ nt op c₁ c₂ r ∧ r ≠ none ∧
      ((∃ c, c ∈ r.get! ∧ L = [.CONST nt c]) ∨ (r.get! = [] ∧ L = [.TRAP])) := by
  generalize hL : ws.map instr_val ++ [.BINOP nt op] = L₀ at h
  cases h
  case binop_val nt' c₁ c₂ op' c r hf _ hne hmem _ _ _ _ _ =>
    have hL' : ws.map instr_val ++ [.BINOP nt op] =
        [val.CONST nt' c₁, val.CONST nt' c₂].map instr_val ++ [.BINOP nt' op'] := hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.BINOP.injEq, and_true] at hlast
    obtain ⟨rfl, rfl⟩ := hlast
    exact ⟨c₁, c₂, r, map_instr_val_inj hws, hf, hne, .inl ⟨c, List.contains_iff_mem.mp
      (by simpa using hmem), rfl⟩⟩
  case binop_trap nt' c₁ c₂ op' r hf hne hnil _ _ _ _ _ =>
    have hL' : ws.map instr_val ++ [.BINOP nt op] =
        [val.CONST nt' c₁, val.CONST nt' c₂].map instr_val ++ [.BINOP nt' op'] := hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.BINOP.injEq, and_true] at hlast
    obtain ⟨rfl, rfl⟩ := hlast
    exact ⟨c₁, c₂, r, map_instr_val_inj hws, hf, hne, .inr ⟨hnil, rfl⟩⟩
  all_goals list_contra hL

theorem wf_redex {z : state} {pre R : List instr} (h : wf_config (.mk_config z (pre ++ R))) :
    wf_state z ∧ ∀ i ∈ R, wf_instr i := by
  obtain ⟨hs, hi⟩ := wf_config_iff.mp h
  exact ⟨hs, fun i hm => hi i (List.mem_append_right _ hm)⟩

/-- A binary operator with the results `rs`: a value for each result, a trap for none. -/
theorem Code.wp_binop {nt : numtype} {op : binop_} {c₁ c₂ : num_} {rs : List num_}
    {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hf : fun_binop_ nt op c₁ c₂ (some rs))
    (huniq : ∀ r, fun_binop_ nt op c₁ c₂ r → r = some rs)
    (hwfr : ∀ c ∈ rs, wf_num_ nt c)
    (hQ : ∀ c ∈ rs, Q z (.CONST nt c :: vs))
    (hE : rs = [] → E .trap z) :
    Code.wp [.BINOP nt op] Q E z (.CONST nt c₂ :: .CONST nt c₁ :: vs) := by
  intro hwf
  have hlist : (val.CONST nt c₂ :: val.CONST nt c₁ :: vs).reverse.map instr_val ++ [.BINOP nt op] =
      vs.reverse.map instr_val ++ [.CONST nt c₁, .CONST nt c₂, .BINOP nt op] := by
    simp [instr_val]
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hc₁ : wf_instr (.CONST nt c₁) := hi _ (by simp)
  have hc₂ : wf_instr (.CONST nt c₂) := hi _ (by simp)
  have hb : wf_instr (.BINOP nt op) := hi _ (by simp)
  have hwfR : wf_config (.mk_config z [.CONST nt c₁, .CONST nt c₂, .BINOP nt op]) :=
    wf_config_iff.mpr ⟨hs, hi⟩
  refine .step _ ?_ ?_
  · cases rs with
    | nil =>
      have hp : Step_pure [.CONST nt c₁, .CONST nt c₂, .BINOP nt op] [.TRAP] :=
        .binop_trap nt c₁ c₂ op (some []) hf (by simp) rfl (by simp [Forall]) hc₁ hc₂ hb
          .instr_case_115
      have hstep := Step.pure z _ _ hp hwfR (wf_config_iff.mpr ⟨hs, by simp [wf_instr.instr_case_115]⟩)
      exact ⟨_, Step.under vs.reverse hstep hwf⟩
    | cons c cs =>
      have hwc : wf_instr (.CONST nt c) := .instr_case_76 _ _ (hwfr c (by simp))
      have hp : Step_pure [.CONST nt c₁, .CONST nt c₂, .BINOP nt op] [.CONST nt c] :=
        .binop_val nt c₁ c₂ op c (some (c :: cs)) hf (by simp) (by simp) (by simp)
          (fun x hx => hwfr x (by simpa using hx)) hc₁ hc₂ hb hwc
      have hstep := Step.pure z _ _ hp hwfR (wf_config_iff.mpr ⟨hs, by simpa using hwc⟩)
      exact ⟨_, Step.under vs.reverse hstep hwf⟩
  · intro c' hs'
    have hs'' : Step (.mk_config z ((vs.reverse ++ [val.CONST nt c₁, val.CONST nt c₂]).map instr_val ++
        [.BINOP nt op])) c' := by simpa [instr_val] using hs'
    obtain ⟨ws₁, ws₂, L'', hsplit, hp, rfl⟩ := Step.redex_pure rfl hs''
    obtain ⟨d₁, d₂, r, rfl, hf', -, hres⟩ := Step_pure.binop_redex hp
    obtain ⟨rfl, hd₁, hd₂⟩ := split_two hsplit
    cases hd₁; cases hd₂

    obtain rfl := huniq r hf'
    rcases hres with ⟨c, hc, rfl⟩ | ⟨hnil, rfl⟩
    · have hQc := hQ c (by simpa using hc)
      have := Safe.vals (E := E) z (.CONST nt c :: vs) hQc
      simpa [cfg_eq, instr_val] using this
    · have hE' := hE (by simpa using hnil)
      exact .exit _ _ _ (by simpa [code_eq] using IsExit.trap vs []) hE'

/-! ## Comparisons and tests: an `i32` result `u` -/

/-- A constant of type `i32` whose projection is `u` is `mk_num__0 I32 u`. -/
theorem num_i32_of_proj {c : num_} {u : uN} (hne : proj_num__0 c ≠ none)
    (heq : (proj_num__0 c).get! = u) (hwf : wf_instr (.CONST .I32 c)) :
    c = .mk_num__0 .I32 u := by
  cases c with
  | mk_num__0 inn x =>
    simp only [proj_num__0, Option.get!_some] at heq
    subst heq
    cases hwf with
    | instr_case_76 _ _ hn =>
      cases hn with
      | num__case_0 _ _ _ hinn => cases inn <;> simp_all [numtype_addrtype]
  | mk_num__1 _ _ => simp [proj_num__0] at hne

theorem wf_i32_const {u : uN} (h : wf_uN 32 u) : wf_instr (.CONST .I32 (.mk_num__0 .I32 u)) :=
  .instr_case_76 _ _ (.num__case_0 _ _ _ h rfl)

theorem Step_pure.relop_redex {ws : List val} {nt : numtype} {op : relop_} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.RELOP nt op]) L) :
    ∃ (c₁ c₂ : num_) (u : uN), ws = [.CONST nt c₁, .CONST nt c₂] ∧
      fun_relop_ nt op c₁ c₂ = some u ∧ L = [.CONST .I32 (.mk_num__0 .I32 u)] := by
  generalize hL : ws.map instr_val ++ [.RELOP nt op] = L₀ at h
  cases h
  case relop nt' c₁ c₂ op' c hpc hf heq _ _ _ _ hwc =>
    have hL' : ws.map instr_val ++ [.RELOP nt op] =
        [val.CONST nt' c₁, val.CONST nt' c₂].map instr_val ++ [.RELOP nt' op'] := hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.RELOP.injEq, and_true] at hlast
    obtain ⟨rfl, rfl⟩ := hlast
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hf
    rw [hu, Option.get!_some] at heq
    exact ⟨c₁, c₂, u, map_instr_val_inj hws, hu, by rw [num_i32_of_proj hpc heq hwc]⟩
  all_goals list_contra hL

theorem Code.wp_relop {nt : numtype} {op : relop_} {c₁ c₂ : num_} {u : uN}
    {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hf : fun_relop_ nt op c₁ c₂ = some u) (hwu : wf_uN 32 u)
    (hQ : Q z (.CONST .I32 (.mk_num__0 .I32 u) :: vs)) :
    Code.wp [.RELOP nt op] Q E z (.CONST nt c₂ :: .CONST nt c₁ :: vs) := by
  intro hwf
  have hlist : (val.CONST nt c₂ :: val.CONST nt c₁ :: vs).reverse.map instr_val ++ [.RELOP nt op] =
      vs.reverse.map instr_val ++ [.CONST nt c₁, .CONST nt c₂, .RELOP nt op] := by
    simp [instr_val]
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwc := wf_i32_const hwu
  have hp : Step_pure [.CONST nt c₁, .CONST nt c₂, .RELOP nt op] [.CONST .I32 (.mk_num__0 .I32 u)] :=
    .relop nt c₁ c₂ op _ (by simp [proj_num__0]) (by simp [hf]) (by simp [proj_num__0, hf])
      (by simpa [hf] using hwu) (hi _ (by simp)) (hi _ (by simp)) (hi _ (by simp)) hwc
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩) (wf_config_iff.mpr ⟨hs, by simpa using hwc⟩))
    hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z ((vs.reverse ++ [val.CONST nt c₁, val.CONST nt c₂]).map instr_val ++
      [.RELOP nt op])) c' := by simpa [instr_val] using hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨d₁, d₂, u', rfl, hf', rfl⟩ := Step_pure.relop_redex hp'
  obtain ⟨rfl, hd₁, hd₂⟩ := split_two hsplit
  cases hd₁; cases hd₂
  rw [hf] at hf'
  cases hf'
  have := Safe.vals (E := E) z (.CONST .I32 (.mk_num__0 .I32 u) :: vs) hQ
  simpa [cfg_eq, instr_val] using this

theorem Step_pure.testop_redex {ws : List val} {nt : numtype} {op : testop_} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.TESTOP nt op]) L) :
    ∃ (c₁ : num_) (u : uN), ws = [.CONST nt c₁] ∧
      fun_testop_ nt op c₁ = some u ∧ L = [.CONST .I32 (.mk_num__0 .I32 u)] := by
  generalize hL : ws.map instr_val ++ [.TESTOP nt op] = L₀ at h
  cases h
  case testop nt' c₁ op' c hpc hf heq _ _ _ hwc =>
    have hL' : ws.map instr_val ++ [.TESTOP nt op] =
        [val.CONST nt' c₁].map instr_val ++ [.TESTOP nt' op'] := hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.TESTOP.injEq, and_true] at hlast
    obtain ⟨rfl, rfl⟩ := hlast
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hf
    rw [hu, Option.get!_some] at heq
    exact ⟨c₁, u, map_instr_val_inj hws, hu, by rw [num_i32_of_proj hpc heq hwc]⟩
  all_goals list_contra hL

theorem Code.wp_testop {nt : numtype} {op : testop_} {c₁ : num_} {u : uN}
    {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hf : fun_testop_ nt op c₁ = some u) (hwu : wf_uN 32 u)
    (hQ : Q z (.CONST .I32 (.mk_num__0 .I32 u) :: vs)) :
    Code.wp [.TESTOP nt op] Q E z (.CONST nt c₁ :: vs) := by
  intro hwf
  have hlist : (val.CONST nt c₁ :: vs).reverse.map instr_val ++ [.TESTOP nt op] =
      vs.reverse.map instr_val ++ [.CONST nt c₁, .TESTOP nt op] := by
    simp [instr_val]
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwc := wf_i32_const hwu
  have hp : Step_pure [.CONST nt c₁, .TESTOP nt op] [.CONST .I32 (.mk_num__0 .I32 u)] :=
    .testop nt c₁ op _ (by simp [proj_num__0]) (by simp [hf]) (by simp [proj_num__0, hf])
      (by simpa [hf] using hwu) (hi _ (by simp)) (hi _ (by simp)) hwc
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩) (wf_config_iff.mpr ⟨hs, by simpa using hwc⟩))
    hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z ((vs.reverse ++ [val.CONST nt c₁]).map instr_val ++
      [.TESTOP nt op])) c' := by simpa [instr_val] using hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨d₁, u', rfl, hf', rfl⟩ := Step_pure.testop_redex hp'
  obtain ⟨rfl, hd₁⟩ := split_one hsplit
  cases hd₁
  rw [hf] at hf'
  cases hf'
  have := Safe.vals (E := E) z (.CONST .I32 (.mk_num__0 .I32 u) :: vs) hQ
  simpa [cfg_eq, instr_val] using this

/-! ## Constants, `nop`, `drop`, `unreachable` -/

theorem Code.wp_const {c : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hQ : Q z (c :: vs)) : Code.wp [instr_val c] Q E z vs := by
  intro _
  have := Safe.vals (E := E) z (c :: vs) hQ
  simpa [cfg_eq] using this

theorem Step_pure.nop_redex {ws : List val} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.NOP]) L) : ws = [] ∧ L = [] := by
  generalize hL : ws.map instr_val ++ [.NOP] = L₀ at h
  cases h
  case nop => exact ⟨by simpa using congrArg List.length hL, rfl⟩
  all_goals list_contra hL

theorem Code.wp_nop {Q : Assn} {E : EAssn} {z : state} {vs : Stack} (hQ : Q z vs) :
    Code.wp [.NOP] Q E z vs := by
  intro hwf
  rw [cfg_eq] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hp : Step_pure [.NOP] [] := .nop (hi _ (by simp))
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩) (wf_config_iff.mpr ⟨hs, by simp⟩)) hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z (vs.reverse.map instr_val ++ [.NOP])) c' := hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨rfl, rfl⟩ := Step_pure.nop_redex hp'
  simp only [List.append_nil] at hsplit
  subst hsplit
  have := Safe.vals (E := E) z vs hQ
  simpa [cfg_eq] using this

theorem Step_pure.drop_redex {ws : List val} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.DROP]) L) : ∃ v, ws = [v] ∧ L = [] := by
  generalize hL : ws.map instr_val ++ [.DROP] = L₀ at h
  cases h
  case drop v _ _ =>
    have hL' : ws.map instr_val ++ [.DROP] = [v].map instr_val ++ [.DROP] := hL
    exact ⟨v, map_instr_val_inj (List.append_inj' hL' rfl).1, rfl⟩
  all_goals list_contra hL

theorem wf_instr_of_wf_val {v : val} (h : wf_val v) : wf_instr (instr_val v) := by
  cases h <;> first | (constructor <;> assumption) | constructor

theorem Code.wp_drop {v : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack} (hQ : Q z vs) :
    Code.wp [.DROP] Q E z (v :: vs) := by
  intro hwf
  have hlist : (v :: vs).reverse.map instr_val ++ [.DROP] =
      vs.reverse.map instr_val ++ [instr_val v, .DROP] := by simp
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwv : wf_val v := by
    have := hi (instr_val v) (by simp)
    cases v <;> cases this <;> constructor <;> assumption
  have hp : Step_pure [instr_val v, .DROP] [] := .drop v hwv (hi _ (by simp))
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩) (wf_config_iff.mpr ⟨hs, by simp⟩)) hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z ((vs.reverse ++ [v]).map instr_val ++ [.DROP])) c' := by
    simpa using hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨w, rfl, rfl⟩ := Step_pure.drop_redex hp'
  obtain ⟨rfl, -⟩ := split_one hsplit
  have := Safe.vals (E := E) z vs hQ
  simpa [cfg_eq] using this

theorem Step_pure.unreachable_redex {ws : List val} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.UNREACHABLE]) L) : ws = [] ∧ L = [.TRAP] := by
  generalize hL : ws.map instr_val ++ [.UNREACHABLE] = L₀ at h
  cases h
  case unreachable => exact ⟨by simpa using congrArg List.length hL, rfl⟩
  all_goals list_contra hL

theorem Code.wp_unreachable {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hE : E .trap z) : Code.wp [.UNREACHABLE] Q E z vs := by
  intro hwf
  rw [cfg_eq] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hp : Step_pure [.UNREACHABLE] [.TRAP] := .unreachable (hi _ (by simp)) .instr_case_115
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩)
      (wf_config_iff.mpr ⟨hs, by simp [wf_instr.instr_case_115]⟩)) hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z (vs.reverse.map instr_val ++ [.UNREACHABLE])) c' := hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨rfl, rfl⟩ := Step_pure.unreachable_redex hp'
  simp only [List.append_nil] at hsplit
  subst hsplit
  exact .exit _ _ _ (by simpa [code_eq] using IsExit.trap vs []) hE

end SpecTecWP
