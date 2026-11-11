import SpecTecWP.Instr

/-!
# Labels

A block runs its body `B` inside the label `LABEL_ k K B`: `k` is the arity of the label and
`K` is its continuation. `LabelStep` lists the steps of a label configuration, one constructor
per rule. `Safe.label` transports `Safe` of the body to `Safe` of the label: the body's values
stay on the stack, `br 0` with the stack `bs` continues with `K` on the top `k` values of `bs`,
and `br (l + 1)` leaves the label as `br l`.
-/

namespace SpecTecWP

/-- The steps of the configuration `[LABEL_ k K B]` in state `z`, by rule. -/
inductive LabelStep (z : state) (k : n) (K B : List instr) : state → List instr → Prop where
  | ctxt {z' : state} {B' : List instr} :
      Step (.mk_config z B) (.mk_config z' B') → LabelStep z k K B z' [.LABEL_ k K B']
  | vals (vs : List val) : B = vs.map instr_val → LabelStep z k K B z B
  | br_zero (vs' vs : List val) (l : labelidx) (rest : List instr) :
      proj_uN_0 l = 0 → vs.length = k →
      B = vs'.map instr_val ++ vs.map instr_val ++ .BR l :: rest →
      LabelStep z k K B z (vs.map instr_val ++ K)
  | br_succ (vs : List val) (l : labelidx) (rest : List instr) :
      0 < proj_uN_0 l → B = vs.map instr_val ++ .BR l :: rest →
      LabelStep z k K B z (vs.map instr_val ++ [.BR (.mk_uN (proj_uN_0 l - 1))])
  | ret (vs : List val) (rest : List instr) :
      B = vs.map instr_val ++ .RETURN :: rest →
      LabelStep z k K B z (vs.map instr_val ++ [.RETURN])
  | return_call_ref (vs : List val) (yy : typeuse) (rest : List instr) :
      B = vs.map instr_val ++ .RETURN_CALL_REF yy :: rest →
      LabelStep z k K B z (vs.map instr_val ++ [.RETURN_CALL_REF yy])
  | trap : B = [.TRAP] → LabelStep z k K B z [.TRAP]
  | throw (a : addr) : B = [.REF_EXN_ADDR a, .THROW_REF] → LabelStep z k K B z B

theorem vals_append_singleton {ws : List val} {i j : instr}
    (h : ws.map instr_val ++ [i] = [j]) : ws = [] ∧ i = j := by
  cases ws with
  | nil => simpa using h
  | cons w ws => simp at h

theorem toNat_pred (a : Nat) : Int.toNat (Int.ofNat a - Int.ofNat 1) = a - 1 := by
  simp only [Int.ofNat_eq_natCast]; omega

/-- Closes a goal for a label rule: the redex is the label itself, without values in front. -/
macro "label_rule" hL:ident : tactic => `(tactic| (
  obtain ⟨h₀, hi⟩ := vals_append_singleton $hL
  simp only [instr.LABEL_.injEq] at hi
  obtain ⟨h₁, h₂, h₃⟩ := hi
  subst h₀ h₁ h₂ h₃))

/-- Closes `L = vs.map instr_val ++ i :: t` by unification, after reassociating `L`. -/
macro "app_rfl" : tactic => `(tactic|
  (simp only [List.append_assoc, List.singleton_append, List.cons_append]; rfl))

theorem Step.redex_label_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (k : n) (K B : List instr),
      c = .mk_config z (ws.map instr_val ++ [.LABEL_ k K B]) →
      ∃ z' L'', LabelStep z k K B z' L'' ∧ c' = .mk_config z' (ws.map instr_val ++ L'') := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro z ws k K B hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hL : ws.map instr_val ++ [instr.LABEL_ k K B] = L₀ at hp
    cases hp
    case label_vals =>
      label_rule hL
      exact ⟨_, _, .vals _ rfl, by simp⟩
    case br_label_zero =>
      label_rule hL
      exact ⟨_, _, .br_zero _ _ _ _ (by assumption) (by assumption) (by app_rfl), by simp⟩
    case br_label_succ =>
      label_rule hL
      refine ⟨_, _, .br_succ _ _ _ (by assumption) (by app_rfl), ?_⟩
      simp
    case return_label =>
      label_rule hL
      exact ⟨_, _, .ret _ _ (by app_rfl), by simp⟩
    case trap_label =>
      label_rule hL
      exact ⟨_, _, .trap rfl, by simp⟩
    all_goals list_contra hL
  case read z₀ L L' hr _ _ =>
    intro z ws k K B hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hcfg : config.mk_config z₀ (ws.map instr_val ++ [instr.LABEL_ k K B]) = c at hr
    cases hr
    case return_call_ref_label =>
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨rfl, hL⟩ := hcfg
      label_rule hL
      exact ⟨_, _, .return_call_ref _ _ _ (by app_rfl), by simp⟩
    case throw_ref_label =>
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨rfl, hL⟩ := hcfg
      label_rule hL
      exact ⟨_, _, .throw _ rfl, by simp⟩
    all_goals
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨-, hL⟩ := hcfg
      list_contra hL
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws k K B hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split rfl hc hinner
    obtain ⟨z'', L'', hl, heq⟩ := ih z₀ ws₂ k K B rfl
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨_, L'', hl, by simp⟩
  case ctxt_label z₀ k' K' B₀ z' B' hinner _ _ _ _ _ =>
    intro z ws k K B hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hL⟩ := hc
    label_rule hL.symm
    exact ⟨_, _, .ctxt hinner, by simp⟩
  all_goals
    intro z ws k K B hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    list_contra hc

/-- A step of the label `LABEL_ k K B` behind the values `ws` is a `LabelStep`. -/
theorem Step.redex_label {z : state} {ws : List val} {k : n} {K B : List instr} {c' : config}
    (h : Step (.mk_config z (ws.map instr_val ++ [.LABEL_ k K B])) c') :
    ∃ z' L'', LabelStep z k K B z' L'' ∧ c' = .mk_config z' (ws.map instr_val ++ L'') :=
  Step.redex_label_aux h z ws k K B rfl

/-! ## Configurations without steps -/

theorem Step.not_vals {z : state} {ws : List val} {c' : config}
    (h : Step (.mk_config z (ws.map instr_val)) c') : False := by
  obtain ⟨ws', i, t, hL, hi⟩ := Step.has_nonval h
  simp only [instrsOf_mk] at hL
  have := congrArg (List.find? (fun x => (toVal x).isNone)) hL
  rw [find_nonval_vals, find_nonval_cons _ _ _ hi] at this
  cases this

theorem Step.not_br {z : state} {ws : List val} {l : labelidx} {t : List instr} {c' : config}
    (h : Step (.mk_config z (ws.map instr_val ++ .BR l :: t)) c') : False := by
  rcases Step.inv rfl h with ⟨z', L'', hs, -⟩ | ⟨hb, -⟩
  · obtain ⟨_, _, _, _, hp, _⟩ := Step.redex_pure rfl hs
    exact Step_pure.br_redex hp
  · rcases hb with h | h <;> cases h

theorem Step.not_ret {z : state} {ws : List val} {t : List instr} {c' : config}
    (h : Step (.mk_config z (ws.map instr_val ++ .RETURN :: t)) c') : False := by
  rcases Step.inv rfl h with ⟨z', L'', hs, -⟩ | ⟨hb, -⟩
  · obtain ⟨_, _, _, _, hp, _⟩ := Step.redex_pure rfl hs
    exact Step_pure.return_redex hp
  · rcases hb with h | h <;> cases h

theorem Step.redex_return_call_ref_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (yy : typeuse),
      c = .mk_config z (ws.map instr_val ++ [.RETURN_CALL_REF yy]) → False := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro z ws yy hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hL : ws.map instr_val ++ [instr.RETURN_CALL_REF yy] = L₀ at hp
    cases hp <;> list_contra hL
  case read z₀ L L' hr _ _ =>
    intro z ws yy hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    generalize hcfg : config.mk_config z₀ (ws.map instr_val ++ [instr.RETURN_CALL_REF yy]) = c at hr
    cases hr
    all_goals
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨-, hL⟩ := hcfg
      list_contra hL
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws yy hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split rfl hc hinner
    exact ih z₀ ws₂ yy rfl
  all_goals
    intro z ws yy hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    list_contra hc

theorem Step.not_return_call_ref {z : state} {ws : List val} {yy : typeuse} {t : List instr}
    {c' : config} (h : Step (.mk_config z (ws.map instr_val ++ .RETURN_CALL_REF yy :: t)) c') :
    False := by
  rcases Step.inv rfl h with ⟨z', L'', hs, -⟩ | ⟨hb, -⟩
  · exact Step.redex_return_call_ref_aux hs z ws yy rfl
  · rcases hb with h | h <;> cases h

theorem Step.not_trap {z : state} {c' : config} (h : Step (.mk_config z [.TRAP]) c') : False := by
  have h' : Step (.mk_config z (([] : List val).map instr_val ++ .TRAP :: [])) c' := h
  obtain ⟨ws', t', -, hlen⟩ := Step.trap_succ h'
  simp at hlen

theorem Step.not_throw {z : state} {a : addr} {c' : config}
    (h : Step (.mk_config z [.REF_EXN_ADDR a, .THROW_REF]) c') : False := by
  have h' : Step (.mk_config z ([val.REF_EXN_ADDR a].map instr_val ++ .THROW_REF :: [])) c' := h
  obtain ⟨ws', t', -, hl, hlen⟩ := Step.throw_succ (a := a) (by simp) h'
  cases ws' with
  | nil => simp at hl
  | cons _ _ => simp at hlen

end SpecTecWP
