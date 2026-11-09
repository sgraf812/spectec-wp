import SpecTecWP.Redex

/-!
# Exits and the sequencing law

A trap configuration `ws ++ TRAP :: t` and an exception configuration
`ws ++ [REF.EXN_ADDR a, THROW_REF] ++ t` only reduce to shorter configurations of the same
kind, and a `Safe` such configuration satisfies the exception postcondition of its exit
(`Safe.trap_inv`, `Safe.throw_inv`). With these, `Code.wp_append` sequences two instruction
sequences.
-/

namespace SpecTecWP

/-- The first non-value instruction of a list whose prefix is values. -/
theorem find_nonval_cons (ws : List val) (i : instr) (t : List instr) (hi : toVal i = none) :
    (ws.map instr_val ++ i :: t).find? (fun x => (toVal x).isNone) = some i := by
  rw [find_nonval_vals_append]; simp [hi]

/-- Closes a goal whose hypothesis `hL` equates two lists with different last instructions,
or with different first non-value instructions. -/
macro "list_contra" hL:ident : tactic => `(tactic| first
  | (have h' := congrArg List.getLast? $hL; simp at h'; done)
  | (have h' := congrArg (List.find? (fun x => (toVal x).isNone)) $hL
     rw [find_nonval_redex _ _ rfl, find_nonval_vals_append] at h'
     simp [List.find?_cons, toVal] at h'; done))

/-! ## Redexes of exits -/

theorem Step_pure.trap_redex {ws : List val} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.TRAP]) L) : L = [.TRAP] ∧ ws ≠ [] := by
  generalize hL : ws.map instr_val ++ [.TRAP] = L₀ at h
  cases h
  case trap_instrs vals rest hne _ _ _ =>
    have h' : ws.map instr_val ++ .TRAP :: [] = vals.map instr_val ++ .TRAP :: rest := by
      simpa using hL
    obtain ⟨rfl, -, rfl⟩ := vals_cons_inj h' rfl rfl
    exact ⟨rfl, by simpa using hne⟩
  all_goals list_contra hL

theorem Step_pure.br_redex {ws : List val} {l : labelidx} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.BR l]) L) : False := by
  generalize hL : ws.map instr_val ++ [.BR l] = L₀ at h
  cases h <;> list_contra hL

theorem Step_pure.return_redex {ws : List val} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.RETURN]) L) : False := by
  generalize hL : ws.map instr_val ++ [.RETURN] = L₀ at h
  cases h <;> list_contra hL

theorem Step_read.throw_redex {z : state} {ws : List val} {L : List instr}
    (h : Step_read (.mk_config z (ws.map instr_val ++ [.THROW_REF])) L) :
    (∃ (vs : List val) (a : addr), ws = vs ++ [.REF_EXN_ADDR a] ∧ vs ≠ [] ∧
      L = [.REF_EXN_ADDR a, .THROW_REF]) ∨
    (ws = [.REF_NULL_ADDR] ∧ L = [.TRAP]) := by
  generalize hc : config.mk_config z (ws.map instr_val ++ [.THROW_REF]) = c at h
  cases h
  case throw_ref_null =>
    simp only [config.mk_config.injEq] at hc
    have h' : ws.map instr_val ++ .THROW_REF :: [] =
        [val.REF_NULL_ADDR].map instr_val ++ .THROW_REF :: [] := by rw [hc.2]; rfl
    obtain ⟨rfl, -, -⟩ := vals_cons_inj h' rfl rfl
    exact .inr ⟨rfl, rfl⟩
  case throw_ref_instrs vals a rest hne _ _ _ =>
    simp only [config.mk_config.injEq] at hc
    have h' : ws.map instr_val ++ .THROW_REF :: [] =
        (vals ++ [val.REF_EXN_ADDR a]).map instr_val ++ .THROW_REF :: rest := by
      rw [hc.2]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append, List.singleton_append]
      rfl
    obtain ⟨rfl, -, rfl⟩ := vals_cons_inj h' rfl rfl
    exact .inl ⟨vals, a, rfl, by simpa using hne, rfl⟩
  all_goals
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    list_contra hc

/-! ## Successors of trap and exception configurations -/

theorem Step.trap_succ {z : state} {ws : List val} {t : List instr} {c' : config}
    (h : Step (.mk_config z (ws.map instr_val ++ .TRAP :: t)) c') :
    ∃ (ws' : List val) (t' : List instr), c' = .mk_config z (ws'.map instr_val ++ .TRAP :: t') ∧
      ws'.length + t'.length < ws.length + t.length := by
  rcases Step.inv rfl h with ⟨z', L'', hs, rfl⟩ | ⟨-, ws', t', rfl, hlen, -⟩
  · obtain ⟨ws₁, ws₂, L₃, rfl, hp, heq⟩ := Step.redex_pure rfl hs
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨rfl, hne⟩ := Step_pure.trap_redex hp
    refine ⟨ws₁, t, by simp, ?_⟩
    have : 0 < ws₂.length := List.length_pos_iff.mpr hne
    simp only [List.length_append]; omega
  · exact ⟨ws', t', rfl, hlen⟩

theorem Step.throw_succ {z : state} {ws : List val} {t : List instr} {c' : config} {a : addr}
    (hlast : ws.getLast? = some (.REF_EXN_ADDR a))
    (h : Step (.mk_config z (ws.map instr_val ++ .THROW_REF :: t)) c') :
    ∃ (ws' : List val) (t' : List instr),
      c' = .mk_config z (ws'.map instr_val ++ .THROW_REF :: t') ∧
      ws'.getLast? = some (.REF_EXN_ADDR a) ∧ ws'.length + t'.length < ws.length + t.length := by
  rcases Step.inv rfl h with ⟨z', L'', hs, rfl⟩ | ⟨-, ws', t', rfl, hlen, hl⟩
  · obtain ⟨ws₁, ws₂, L₃, rfl, hr, heq⟩ := Step.redex_read rfl hs
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rcases Step_read.throw_redex hr with ⟨vs, a', rfl, hne, rfl⟩ | ⟨rfl, -⟩
    · have ha : a' = a := by simpa [List.getLast?_append] using hlast
      subst ha
      refine ⟨ws₁ ++ [.REF_EXN_ADDR a'], t, by simp [instr_val], by simp, ?_⟩
      have : 0 < vs.length := List.length_pos_iff.mpr hne
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp [List.getLast?_append] at hlast
  · obtain ⟨-, -, hl⟩ := hl rfl
    exact ⟨ws', t', rfl, hl.trans hlast, hlen⟩

/-! ## Exit postconditions of `Safe` configurations -/

theorem code_eq (vs : Stack) (is : List instr) : code vs is = vs.reverse.map instr_val ++ is := rfl

theorem find_nonval_vals (vs : List val) :
    (vs.map instr_val).find? (fun x => (toVal x).isNone) = none := by
  have := find_nonval_vals_append vs []
  simpa using this

theorem Safe.trap_inv {Q : Assn} {E : EAssn} {c : config} (h : Safe Q E c) :
    ∀ (z : state) (ws : List val) (t : List instr),
      c = .mk_config z (ws.map instr_val ++ .TRAP :: t) → E .trap z := by
  induction h with
  | vals z vs _ =>
    intro z' ws t hc
    simp only [cfg, config.mk_config.injEq] at hc
    have := congrArg (List.find? (fun x => (toVal x).isNone)) hc.2
    rw [code_eq, List.append_nil, find_nonval_vals, find_nonval_cons _ _ _ rfl] at this
    cases this
  | exit z L e hx he =>
    intro z' ws t hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hL : ws.map instr_val ++ .TRAP :: t = L at hx
    cases hx with
    | trap => exact he
    | _ =>
      exfalso
      have := congrArg (List.find? (fun x => (toVal x).isNone)) hL
      rw [find_nonval_cons _ _ _ rfl, code_eq, find_nonval_vals_append] at this
      simp [List.find?_cons, toVal] at this
  | step c hprog _ ih =>
    intro z ws t hc
    subst hc
    obtain ⟨c', hs⟩ := hprog
    obtain ⟨ws', t', rfl, -⟩ := Step.trap_succ hs
    exact ih _ hs z ws' t' rfl

theorem Safe.throw_inv {Q : Assn} {E : EAssn} {c : config} (h : Safe Q E c) :
    ∀ (z : state) (ws : List val) (t : List instr) (a : addr),
      ws.getLast? = some (.REF_EXN_ADDR a) →
      c = .mk_config z (ws.map instr_val ++ .THROW_REF :: t) → E (.throw a) z := by
  induction h with
  | vals z vs _ =>
    intro z' ws t a _ hc
    simp only [cfg, config.mk_config.injEq] at hc
    have := congrArg (List.find? (fun x => (toVal x).isNone)) hc.2
    rw [code_eq, List.append_nil, find_nonval_vals, find_nonval_cons _ _ _ rfl] at this
    cases this
  | exit z L e hx he =>
    intro z' ws t a ha hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hL : ws.map instr_val ++ .THROW_REF :: t = L at hx
    cases hx with
    | throw vs a' rest =>
      have h' : ws.map instr_val ++ .THROW_REF :: t =
          (vs.reverse ++ [val.REF_EXN_ADDR a']).map instr_val ++ .THROW_REF :: rest := by
        rw [hL, code_eq]
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append, List.nil_append, List.singleton_append]
        rfl
      obtain ⟨rfl, -, -⟩ := vals_cons_inj h' rfl rfl
      have : a' = a := by simpa [List.getLast?_append] using ha
      exact this ▸ he
    | _ =>
      exfalso
      have := congrArg (List.find? (fun x => (toVal x).isNone)) hL
      rw [find_nonval_cons _ _ _ rfl, code_eq, find_nonval_vals_append] at this
      simp [List.find?_cons, toVal] at this
  | step c hprog _ ih =>
    intro z ws t a ha hc
    subst hc
    obtain ⟨c', hs⟩ := hprog
    obtain ⟨ws', t', rfl, ha', -⟩ := Step.throw_succ ha hs
    exact ih _ hs z ws' t' a ha' rfl

/-! ## The sequencing law -/

/-- A `Safe` configuration followed by `c₂` is `Safe` for the postcondition that `Safe` holds
after `c₂`. -/
theorem Safe.seq {Q : Assn} {E : EAssn} {c₂ : List instr} {c : config}
    (h : Safe (fun z vs => wf_config (cfg z vs c₂) → Safe Q E (cfg z vs c₂)) E c) :
    ∀ (z : state) (L : List instr), c = .mk_config z L →
      wf_config (.mk_config z (L ++ c₂)) → Safe Q E (.mk_config z (L ++ c₂)) := by
  induction h with
  | vals z vs hq =>
    intro z' L hc hwf
    simp only [cfg, config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have e : code vs [] ++ c₂ = code vs c₂ := by simp [code_eq]
    rw [e] at hwf ⊢
    exact hq hwf
  | exit z L e hx he =>
    intro z' L' hc hwf
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases hx with
    | br vs l rest =>
      rw [show code vs (.BR l :: rest) ++ c₂ = code vs (.BR l :: (rest ++ c₂)) by simp [code_eq]]
      exact .exit _ _ _ (.br vs l _) he
    | ret vs rest =>
      rw [show code vs (.RETURN :: rest) ++ c₂ = code vs (.RETURN :: (rest ++ c₂)) by simp [code_eq]]
      exact .exit _ _ _ (.ret vs _) he
    | throw vs a rest =>
      rw [show code vs (.REF_EXN_ADDR a :: .THROW_REF :: rest) ++ c₂ =
        code vs (.REF_EXN_ADDR a :: .THROW_REF :: (rest ++ c₂)) by simp [code_eq]]
      exact .exit _ _ _ (.throw vs a _) he
    | trap vs rest =>
      rw [show code vs (.TRAP :: rest) ++ c₂ = code vs (.TRAP :: (rest ++ c₂)) by simp [code_eq]]
      exact .exit _ _ _ (.trap vs _) he
  | step c hprog hsucc ih =>
    intro z L hc hwf
    subst hc
    have hsafe : Safe _ E (.mk_config z L) := .step _ hprog hsucc
    obtain ⟨c', hs⟩ := hprog
    obtain ⟨ws, i, t, hL, hi⟩ := Step.has_nonval hs
    simp only [instrsOf_mk] at hL
    subst hL
    by_cases htrap : i = .TRAP
    · subst htrap
      have he := Safe.trap_inv hsafe z ws t rfl
      rw [show ws.map instr_val ++ .TRAP :: t ++ c₂ = code ws.reverse (.TRAP :: (t ++ c₂)) by
        simp [code_eq]]
      exact .exit _ _ _ (.trap _ _) he
    by_cases hthrow : i = .THROW_REF ∧ ∃ a, ws.getLast? = some (.REF_EXN_ADDR a)
    · obtain ⟨rfl, a, ha⟩ := hthrow
      have he := Safe.throw_inv hsafe z ws t a ha rfl
      obtain ⟨ws', rfl⟩ := List.getLast?_eq_some_iff.mp ha
      rw [show (ws' ++ [val.REF_EXN_ADDR a]).map instr_val ++ .THROW_REF :: t ++ c₂ =
          code ws'.reverse (.REF_EXN_ADDR a :: .THROW_REF :: (t ++ c₂)) by
        simp only [code_eq, List.reverse_reverse, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
        rfl]
      exact .exit _ _ _ (.throw _ _ _) he
    have hwfL : wf_config (.mk_config z (([] : List val).map instr_val ++ ((ws.map instr_val ++ [i]) ++ t))) := by
      have := wf_config_append_left (A := ws.map instr_val ++ i :: t) (B := c₂) (by simpa using hwf)
      simpa using this
    refine .step _ ?_ ?_
    · obtain ⟨z', L'⟩ := c'
      have := Step.frame [] c₂ hs (by simpa using hwf)
      exact ⟨_, by simpa using this⟩
    · intro c'' hs''
      rw [show ws.map instr_val ++ i :: t ++ c₂ = ws.map instr_val ++ i :: (t ++ c₂) by simp] at hs''
      rcases Step.inv hi hs'' with ⟨z', L'', hr, rfl⟩ | ⟨hb, ws', t', rfl, -, hl⟩
      · have hstep : Step (.mk_config z (ws.map instr_val ++ i :: t)) (.mk_config z' (L'' ++ t)) := by
          have := Step.frame [] t hr hwfL
          simpa using this
        have hwf'' : wf_config (.mk_config z' ((L'' ++ t) ++ c₂)) := by
          have := Step.wf_target hs''
          simpa using this
        have := ih _ hstep z' (L'' ++ t) rfl hwf''
        simpa using this
      · rcases hb with rfl | rfl
        · exact absurd rfl htrap
        · obtain ⟨a, ha, -⟩ := hl rfl
          exact absurd ⟨rfl, a, ha⟩ hthrow

/-- The sequencing law: running `c₁` and then `c₂`. -/
theorem Code.wp_append {c₁ c₂ : List instr} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (h : Code.wp c₁ (Code.wp c₂ Q E) E z vs) : Code.wp (c₁ ++ c₂) Q E z vs := by
  intro hwf
  have hwf₁ : wf_config (cfg z vs c₁) := by
    have := wf_config_append_left (A := code vs c₁) (B := c₂) (by simpa [cfg, code_eq] using hwf)
    simpa [cfg] using this
  have := Safe.seq (h hwf₁) z (code vs c₁) rfl (by simpa [cfg, code_eq] using hwf)
  simpa [cfg, code_eq] using this

end SpecTecWP
