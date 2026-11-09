import SpecTecWP.Inversion

/-!
# Steps of a redex, by its last instruction

A redex `ws.map instr_val ++ [i]` steps by a rule whose left side ends in `i`, possibly framed
by a prefix of the values `ws`. `Step.redex_pure` makes this precise for the instructions
whose rules all belong to `Step_pure`: a step of the redex is a `Step_pure` step of a suffix
`ws₂.map instr_val ++ [i]`, with the values `ws₁` in front, where `ws = ws₁ ++ ws₂`.
-/

namespace SpecTecWP

theorem instr_val_injective : Function.Injective instr_val := by
  intro v w h
  have := congrArg toVal h
  simpa using this

theorem map_instr_val_inj : ∀ {ws ws' : List val}, ws.map instr_val = ws'.map instr_val → ws = ws'
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | w :: ws, w' :: ws', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [instr_val_injective h.1, map_instr_val_inj h.2]

/-- A step through `ctxt_instrs` of a redex frames a step of a shorter redex. -/
theorem ctxt_split {vals ws : List val} {L₀ L₁ : List instr} {i : instr} {z z' : state}
    {L₀' : List instr} (hi : toVal i = none)
    (hL : vals.map instr_val ++ (L₀ ++ L₁) = ws.map instr_val ++ [i])
    (hs : Step (.mk_config z L₀) (.mk_config z' L₀')) :
    ∃ ws₂, ws = vals ++ ws₂ ∧ L₀ = ws₂.map instr_val ++ [i] ∧ L₁ = [] := by
  obtain ⟨ws₀, i₀, t₀, hL₀, hi₀⟩ := Step.has_nonval hs
  simp only [instrsOf_mk] at hL₀
  subst hL₀
  have h' : (vals ++ ws₀).map instr_val ++ i₀ :: (t₀ ++ L₁) = ws.map instr_val ++ i :: [] := by
    simpa using hL
  obtain ⟨rfl, rfl, ht⟩ := vals_cons_inj h' hi₀ hi
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp ht
  exact ⟨ws₀, rfl, rfl, rfl⟩

/-- The instructions whose reduction rules all belong to `Step_pure`. -/
def pureOnly : instr → Bool
  | .NOP | .UNREACHABLE | .DROP | .SELECT _ | .BR_IF _ | .BR_TABLE _ _
  | .UNOP _ _ | .BINOP _ _ | .TESTOP _ _ | .RELOP _ _ | .CVTOP _ _ _ | .LOCAL_TEE _
  | .TRAP | .BR _ | .RETURN => true
  | _ => false

/-- The instructions whose reduction rules all belong to `Step_read`. -/
def readOnly : instr → Bool
  | .LOCAL_GET _ | .GLOBAL_GET _ | .BLOCK _ _ | .LOOP _ _ | .THROW_REF => true
  | _ => false

theorem toVal_of_readOnly {i : instr} (h : readOnly i = true) : toVal i = none := by
  cases i <;> simp_all [readOnly, toVal]

theorem toVal_of_pureOnly {i : instr} (h : pureOnly i = true) : toVal i = none := by
  cases i <;> simp_all [pureOnly, toVal]

/-- A rule whose left side ends in an instruction other than `i` does not step the redex
`ws ++ [i]`. -/
macro "last_contra" hL:ident : tactic => `(tactic| (
  have h' := congrArg List.getLast? $hL
  simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
    Option.some_or, List.getLast?_cons, List.getLastD_cons, List.getLastD_nil,
    Option.some.injEq] at h'
  subst h'
  simp [pureOnly] at *))

/-- A prefix of values does not contain the first non-value instruction. -/
theorem find_nonval_vals_append (vs : List val) (rest : List instr) :
    (vs.map instr_val ++ rest).find? (fun x => (toVal x).isNone) =
      rest.find? (fun x => (toVal x).isNone) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.find?_cons, ih]

/-- The first non-value instruction of a list of values followed by `i` is `i`. -/
theorem find_nonval_redex (ws : List val) (i : instr) (hi : toVal i = none) :
    (ws.map instr_val ++ [i]).find? (fun x => (toVal x).isNone) = some i := by
  rw [find_nonval_vals_append]; simp [hi]

/-- A rule whose left side has a first non-value instruction other than `i` does not step
the redex `ws ++ [i]`. -/
macro "first_contra" hL:ident hpure:ident : tactic => `(tactic| (
  have h' := congrArg (List.find? (fun x => (toVal x).isNone)) $hL
  rw [find_nonval_redex _ _ (toVal_of_pureOnly $hpure), find_nonval_vals_append] at h'
  simp [List.find?_cons, toVal] at h'
  subst h'
  simp [pureOnly] at $hpure:ident))

/-- A step of a redex of a pure instruction is a `Step_pure` step of a suffix of the redex. -/
theorem Step.redex_pure_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (i : instr), c = .mk_config z (ws.map instr_val ++ [i]) →
      pureOnly i = true →
      ∃ (ws₁ ws₂ : List val) (L'' : List instr), ws = ws₁ ++ ws₂ ∧
        Step_pure (ws₂.map instr_val ++ [i]) L'' ∧
        c' = .mk_config z (ws₁.map instr_val ++ L'') := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro z ws i hc hpure
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨[], ws, L', rfl, hp, by simp⟩
  case read z₀ L L' hr _ _ =>
    intro z ws i hc hpure
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hcfg : config.mk_config z₀ (ws.map instr_val ++ [i]) = c at hr
    cases hr
    all_goals
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨-, hcfg⟩ := hcfg
      first | last_contra hcfg | first_contra hcfg hpure
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws i hc hpure
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split (toVal_of_pureOnly hpure) hc hinner
    obtain ⟨ws₁', ws₂', L'', rfl, hp, heq⟩ := ih z₀ ws₂ i rfl hpure
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨vals ++ ws₁', ws₂', L'', by simp, hp, by simp⟩
  all_goals
    intro z ws i hc hpure
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    exfalso
    last_contra hc

theorem Step.redex_pure {z : state} {ws : List val} {i : instr} {c' : config}
    (hpure : pureOnly i = true) (h : Step (.mk_config z (ws.map instr_val ++ [i])) c') :
    ∃ (ws₁ ws₂ : List val) (L'' : List instr), ws = ws₁ ++ ws₂ ∧
      Step_pure (ws₂.map instr_val ++ [i]) L'' ∧
      c' = .mk_config z (ws₁.map instr_val ++ L'') :=
  Step.redex_pure_aux h z ws i rfl hpure

/-- `last_contra` and `first_contra` for a classifier `p`. -/
macro "last_contra'" hL:ident p:ident : tactic => `(tactic| (
  have h' := congrArg List.getLast? $hL
  simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
    Option.some_or, List.getLast?_cons, List.getLastD_cons, List.getLastD_nil,
    Option.some.injEq] at h'
  subst h'
  simp [$p:ident] at *))

macro "first_contra'" hL:ident hp:ident p:ident hnone:term : tactic => `(tactic| (
  have h' := congrArg (List.find? (fun x => (toVal x).isNone)) $hL
  rw [find_nonval_redex _ _ $hnone, find_nonval_vals_append] at h'
  simp [List.find?_cons, toVal] at h'
  subst h'
  simp [$p:ident] at $hp:ident))

/-- A step of a redex of a reading instruction is a `Step_read` step of a suffix of the
redex. -/
theorem Step.redex_read_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (i : instr), c = .mk_config z (ws.map instr_val ++ [i]) →
      readOnly i = true →
      ∃ (ws₁ ws₂ : List val) (L'' : List instr), ws = ws₁ ++ ws₂ ∧
        Step_read (.mk_config z (ws₂.map instr_val ++ [i])) L'' ∧
        c' = .mk_config z (ws₁.map instr_val ++ L'') := by
  induction h
  case read z₀ L L' hr _ _ =>
    intro z ws i hc hread
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨[], ws, L', rfl, hr, by simp⟩
  case pure z₀ L L' hp _ _ =>
    intro z ws i hc hread
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hL : ws.map instr_val ++ [i] = L at hp
    cases hp
    all_goals first
      | last_contra' hL readOnly
      | first_contra' hL hread readOnly (toVal_of_readOnly hread)
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws i hc hread
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split (toVal_of_readOnly hread) hc hinner
    obtain ⟨ws₁', ws₂', L'', rfl, hr, heq⟩ := ih z₀ ws₂ i rfl hread
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨vals ++ ws₁', ws₂', L'', by simp, hr, by simp⟩
  all_goals
    intro z ws i hc hread
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    exfalso
    last_contra' hc readOnly

theorem Step.redex_read {z : state} {ws : List val} {i : instr} {c' : config}
    (hread : readOnly i = true) (h : Step (.mk_config z (ws.map instr_val ++ [i])) c') :
    ∃ (ws₁ ws₂ : List val) (L'' : List instr), ws = ws₁ ++ ws₂ ∧
      Step_read (.mk_config z (ws₂.map instr_val ++ [i])) L'' ∧
      c' = .mk_config z (ws₁.map instr_val ++ L'') :=
  Step.redex_read_aux h z ws i rfl hread

end SpecTecWP
