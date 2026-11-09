import SpecTecWP.Decomp

/-!
# Inversion of `Step` on an instruction sequence

Let `L = ws.map instr_val ++ i :: t`, where `i` is the first instruction of `L` that is not a
value. `Step.inv` shows that a step of `L` is one of two kinds:

* a step of the redex `ws.map instr_val ++ [i]`, followed by `t` unchanged (`Step.frame` is the
  converse);
* a *bubble*: `i` is `TRAP` or `THROW_REF`, the state is unchanged, and the successor is again
  `ws'.map instr_val ++ i :: t'`, strictly shorter than `L`. A `THROW_REF` bubble keeps the last
  value, the exception reference.
-/

namespace SpecTecWP

/-! ## Values and the first non-value instruction -/

theorem toVal_ne_none_of_instr_val (v : val) : toVal (instr_val v) ≠ none := by simp

/-- Two splits at the first non-value instruction agree. -/
theorem vals_cons_inj : ∀ {ws₁ ws₂ : List val} {i₁ i₂ : instr} {t₁ t₂ : List instr},
    ws₁.map instr_val ++ i₁ :: t₁ = ws₂.map instr_val ++ i₂ :: t₂ →
    toVal i₁ = none → toVal i₂ = none → ws₁ = ws₂ ∧ i₁ = i₂ ∧ t₁ = t₂
  | [], [], _, _, _, _, h, _, _ => by simp_all
  | [], w :: _, _, _, _, _, h, h₁, _ => by
    simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
      List.cons.injEq] at h
    simp [h.1] at h₁
  | w :: _, [], _, _, _, _, h, _, h₂ => by
    simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
      List.cons.injEq] at h
    simp [← h.1] at h₂
  | w₁ :: ws₁, w₂ :: ws₂, _, _, _, _, h, h₁, h₂ => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    have hw : w₁ = w₂ := by
      have := congrArg toVal h.1; simpa using this
    obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj h.2 h₁ h₂
    exact ⟨by rw [hw], rfl, rfl⟩

/-- A list is all values, or it splits at its first non-value instruction. -/
theorem split_first : ∀ L : List instr,
    (∃ ws : List val, L = ws.map instr_val) ∨
    ∃ (ws : List val) (i : instr) (t : List instr), L = ws.map instr_val ++ i :: t ∧ toVal i = none
  | [] => .inl ⟨[], rfl⟩
  | j :: L => by
    cases hj : toVal j with
    | none => exact .inr ⟨[], j, L, rfl, hj⟩
    | some w =>
      have hw := instr_val_of_toVal hj
      rcases split_first L with ⟨ws, rfl⟩ | ⟨ws, i, t, rfl, hi⟩
      · exact .inl ⟨w :: ws, by simp [hw]⟩
      · exact .inr ⟨w :: ws, i, t, by simp [hw], hi⟩

theorem Redex.split {L : List instr} (h : Redex L) :
    ∃ (ws : List val) (i : instr) (t : List instr), L = ws.map instr_val ++ i :: t ∧ toVal i = none := by
  obtain ⟨ws, i, rfl, hi⟩ := h
  exact ⟨ws, i, [], rfl, hi⟩

/-- A configuration that steps has a non-value instruction. -/
theorem Step.has_nonval {c c' : config} (h : Step c c') :
    ∃ (ws : List val) (i : instr) (t : List instr), instrsOf c = ws.map instr_val ++ i :: t ∧ toVal i = none := by
  induction h
  case pure L L' hp _ _ =>
    rcases Step_pure.lhs hp with hr | ⟨ws, rest, hL, -, -⟩
    · exact hr.split
    · exact ⟨ws, .TRAP, rest, hL, rfl⟩
  case read z L L' hr _ _ =>
    rcases Step_read.lhs hr with hr | ⟨ws, a, rest, hL, -, -⟩
    · exact hr.split
    · exact ⟨ws ++ [val.REF_EXN_ADDR a], .THROW_REF, rest, by simp [hL, instr_val], rfl⟩
  case ctxt_instrs vals L₀ L₁ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨ws, i, t, hL, hi⟩ := ih
    simp only [instrsOf_mk] at hL ⊢
    exact ⟨vals ++ ws, i, t ++ L₁, by simp [hL], hi⟩
  all_goals (simp only [instrsOf_mk]; exact Redex.split (by redex))

/-! ## Well-formedness of parts of a configuration -/

theorem wf_config_iff {z : state} {L : List instr} :
    wf_config (.mk_config z L) ↔ wf_state z ∧ ∀ i ∈ L, wf_instr i := by
  constructor
  · intro h; cases h with | config_case_0 _ _ hs hf => exact ⟨hs, hf⟩
  · rintro ⟨hs, hf⟩; exact .config_case_0 _ _ hs hf

theorem wf_config_append_left {z : state} {A B : List instr}
    (h : wf_config (.mk_config z (A ++ B))) : wf_config (.mk_config z A) := by
  rw [wf_config_iff] at h ⊢
  exact ⟨h.1, fun i hi => h.2 i (List.mem_append_left _ hi)⟩

theorem wf_config_append_right {z : state} {A B : List instr}
    (h : wf_config (.mk_config z (A ++ B))) : wf_config (.mk_config z B) := by
  rw [wf_config_iff] at h ⊢
  exact ⟨h.1, fun i hi => h.2 i (List.mem_append_right _ hi)⟩

theorem wf_config_append {z : state} {A B : List instr}
    (hA : wf_config (.mk_config z A)) (hB : ∀ i ∈ B, wf_instr i) :
    wf_config (.mk_config z (A ++ B)) := by
  rw [wf_config_iff] at hA ⊢
  refine ⟨hA.1, fun i hi => ?_⟩
  rcases List.mem_append.mp hi with h | h
  · exact hA.2 i h
  · exact hB i h

/-! ## Framing a step -/

/-- A step of `L` is a step of `vs ++ L ++ t`, when that configuration is well-formed. -/
theorem Step.frame {z z' : state} {L L' : List instr} (vals : List val) (t : List instr)
    (h : Step (.mk_config z L) (.mk_config z' L'))
    (hwf : wf_config (.mk_config z (vals.map instr_val ++ (L ++ t)))) :
    Step (.mk_config z (vals.map instr_val ++ (L ++ t)))
      (.mk_config z' (vals.map instr_val ++ (L' ++ t))) := by
  have htgt := wf_config_iff.mp (Step.wf_target h)
  have hsrc := wf_config_iff.mp hwf
  have hwft : wf_config (.mk_config z' (vals.map instr_val ++ (L' ++ t))) := by
    rw [wf_config_iff]
    refine ⟨htgt.1, fun i hi => ?_⟩
    simp only [List.mem_append] at hi
    rcases hi with hi | hi | hi
    · exact hsrc.2 i (List.mem_append_left _ hi)
    · exact htgt.2 i hi
    · exact hsrc.2 i (List.mem_append_right _ (List.mem_append_right _ hi))
  rcases vals with _ | ⟨v, vs⟩ <;> rcases t with _ | ⟨j, js⟩
  · simpa using h
  all_goals exact Step.ctxt_instrs z _ L _ z' L' h (by first | rfl | simp) hwf hwft (Step.wf_source h) (Step.wf_target h)

/-! ## Inversion -/

/-- The successor of a step of `ws ++ i :: t`, by the two kinds of steps. -/
def StepResult (z : state) (ws : List val) (i : instr) (t : List instr) (c' : config) : Prop :=
  (∃ z' L'', Step (.mk_config z (ws.map instr_val ++ [i])) (.mk_config z' L'') ∧
      c' = .mk_config z' (L'' ++ t)) ∨
  ((i = .TRAP ∨ i = .THROW_REF) ∧ ∃ (ws' : List val) (t' : List instr), c' = .mk_config z (ws'.map instr_val ++ i :: t') ∧
      ws'.length + t'.length < ws.length + t.length ∧
      (i = .THROW_REF → ∃ a, ws.getLast? = some (.REF_EXN_ADDR a) ∧ ws'.getLast? = ws.getLast?))

theorem StepResult.of_redex {z : state} {ws : List val} {i : instr} {t : List instr}
    {c c' : config} (hc : c = .mk_config z (ws.map instr_val ++ i :: t)) (hi : toVal i = none)
    (hs : Step c c') (hr : Redex (instrsOf c)) : StepResult z ws i t c' := by
  obtain ⟨ws₀, i₀, hL, hi₀⟩ := hr
  subst hc
  simp only [instrsOf_mk] at hL
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj (t₂ := []) hL hi hi₀
  obtain ⟨z', L''⟩ := c'
  exact .inl ⟨z', L'', by simpa using hs, by simp⟩

theorem Step.inv_aux {c c' : config} (h : Step c c') :
    Step c c' → ∀ z ws i t, c = .mk_config z (ws.map instr_val ++ i :: t) → toVal i = none →
      StepResult z ws i t c' := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro hs z ws i t hc hi
    rcases Step_pure.lhs hp with hr | ⟨vs, rest, hL, rfl, hne⟩
    · exact StepResult.of_redex hc hi hs (by simpa using hr)
    · simp only [config.mk_config.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj (hL.symm.trans hc) rfl hi
      refine .inr ⟨.inl rfl, [], [], by simp, ?_, by simp⟩
      rcases hne with h | h
      · cases vs with
        | nil => exact absurd rfl h
        | cons _ _ => simp only [List.length_nil, List.length_cons]; omega
      · cases rest with
        | nil => exact absurd rfl h
        | cons _ _ => simp only [List.length_nil, List.length_cons]; omega
  case read z₀ L L' hr _ _ =>
    intro hs z ws i t hc hi
    rcases Step_read.lhs hr with hr | ⟨vs, a, rest, hL, rfl, hne⟩
    · exact StepResult.of_redex hc hi hs hr
    · simp only [config.mk_config.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      simp only [instrsOf_mk] at hL
      have hL' : L = (vs ++ [val.REF_EXN_ADDR a]).map instr_val ++ .THROW_REF :: rest := by
        simp [hL, instr_val]
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj (hL'.symm.trans hc) rfl hi
      refine .inr ⟨.inr rfl, [.REF_EXN_ADDR a], [], by simp [instr_val], ?_,
        fun _ => ⟨a, by simp, by simp⟩⟩
      rcases hne with h | h
      · cases vs with
        | nil => exact absurd rfl h
        | cons _ _ => simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · cases rest with
        | nil => exact absurd rfl h
        | cons _ _ => simp only [List.length_append, List.length_cons, List.length_nil]; omega
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ hwft _ _ ih =>
    intro hs z ws i t hc hi
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₀, i₀, t₀, hL₀, hi₀⟩ := Step.has_nonval hinner
    simp only [instrsOf_mk] at hL₀
    subst hL₀
    have hc' : (vals ++ ws₀).map instr_val ++ i₀ :: (t₀ ++ L₁) = ws.map instr_val ++ i :: t := by
      simpa using hc
    obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj hc' hi₀ hi
    rcases ih hinner z₀ ws₀ i₀ t₀ rfl hi₀ with ⟨z'', L'', hs'', heq⟩ | ⟨hb, ws', t', heq, hlen, hlast⟩
    · simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine .inl ⟨z', vals.map instr_val ++ L'', ?_, by simp⟩
      have hwf : wf_config (.mk_config z₀ (vals.map instr_val ++ (ws₀.map instr_val ++ [i₀] ++ []))) := by
        have h0 := Step.wf_source hs
        have heq : vals.map instr_val ++ (ws₀.map instr_val ++ i₀ :: t₀ ++ L₁) =
            (vals.map instr_val ++ (ws₀.map instr_val ++ [i₀] ++ [])) ++ (t₀ ++ L₁) := by simp
        rw [heq] at h0
        exact wf_config_append_left h0
      simpa using Step.frame vals [] hs'' hwf
    · simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine .inr ⟨hb, vals ++ ws', t' ++ L₁, by simp, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · intro hT
        obtain ⟨a, ha, hl⟩ := hlast hT
        exact ⟨a, by simp [List.getLast?_append, ha], by simp only [List.getLast?_append, hl]⟩
  all_goals
    intro hs z ws i t hc hi
    exact StepResult.of_redex hc hi hs (by simp only [instrsOf_mk]; redex)

/-- Inversion of `Step` at the first non-value instruction. -/
theorem Step.inv {z : state} {ws : List val} {i : instr} {t : List instr} {c' : config}
    (hi : toVal i = none) (h : Step (.mk_config z (ws.map instr_val ++ i :: t)) c') :
    StepResult z ws i t c' :=
  Step.inv_aux h h z ws i t rfl hi

end SpecTecWP
