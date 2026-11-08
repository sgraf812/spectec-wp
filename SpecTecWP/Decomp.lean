import SpecTecWP.Basic

/-!
# Redexes of the base reduction rules

Every rule of `Step_pure` and `Step_read` rewrites a *redex*: a sequence of values followed by
one instruction that is not a value. Two rules are the exception. `trap_instrs` rewrites
`vs ++ TRAP :: rest` to `[TRAP]`, and `throw_ref_instrs` rewrites
`vs ++ [REF.EXN_ADDR a, THROW_REF] ++ rest` to `[REF.EXN_ADDR a, THROW_REF]`.
-/

namespace SpecTecWP

/-- `toVal i` is the value that `i` denotes, if `i` is a value instruction. -/
def toVal : instr → Option val
  | .CONST nt c => some (.CONST nt c)
  | .VCONST vt c => some (.VCONST vt c)
  | .REF_I31_NUM i => some (.REF_I31_NUM i)
  | .REF_NULL_ADDR => some .REF_NULL_ADDR
  | .REF_STRUCT_ADDR a => some (.REF_STRUCT_ADDR a)
  | .REF_ARRAY_ADDR a => some (.REF_ARRAY_ADDR a)
  | .REF_FUNC_ADDR a => some (.REF_FUNC_ADDR a)
  | .REF_EXN_ADDR a => some (.REF_EXN_ADDR a)
  | .REF_HOST_ADDR a => some (.REF_HOST_ADDR a)
  | .REF_EXTERN r => some (.REF_EXTERN r)
  | _ => none

@[simp] theorem toVal_instr_val (v : val) : toVal (instr_val v) = some v := by
  cases v <;> rfl

theorem instr_val_of_toVal {i : instr} {v : val} (h : toVal i = some v) : instr_val v = i := by
  cases i <;> simp [toVal] at h <;> subst h <;> rfl

/-- `L` is a sequence of values followed by one non-value instruction. -/
def Redex (L : List instr) : Prop :=
  ∃ (ws : List val) (i : instr), L = ws.map instr_val ++ [i] ∧ toVal i = none

/-- Split a redex into its values and its last instruction. -/
def splitRedex : List instr → Option (List val × instr)
  | [] => none
  | [i] => match toVal i with
    | none => some ([], i)
    | some _ => none
  | i :: rest => match toVal i, splitRedex rest with
    | some v, some (ws, j) => some (v :: ws, j)
    | _, _ => none

theorem splitRedex_sound : ∀ {L : List instr} {ws : List val} {i : instr},
    splitRedex L = some (ws, i) → L = ws.map instr_val ++ [i] ∧ toVal i = none
  | [], _, _, h => by simp [splitRedex] at h
  | [j], ws, i, h => by
    simp only [splitRedex] at h
    split at h <;> simp_all
  | j :: k :: rest, ws, i, h => by
    simp only [splitRedex] at h
    split at h
    · next v ws' j' hj hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hrest, hi⟩ := splitRedex_sound hs
      refine ⟨?_, hi⟩
      rw [List.map_cons, instr_val_of_toVal hj, List.cons_append, ← hrest]
    · simp at h

theorem Redex.of_split {L : List instr} {p : List val × instr}
    (h : splitRedex L = some p) : Redex L :=
  ⟨p.1, p.2, splitRedex_sound (L := L) (ws := p.1) (i := p.2) h⟩

theorem Redex.vals_append (ws : List val) (i : instr) (hi : toVal i = none) :
    Redex (ws.map instr_val ++ [i]) := ⟨ws, i, rfl, hi⟩

@[simp] theorem toVal_instr_ref (r : ref) : toVal (instr_ref r) = some (val_ref r) := by
  cases r <;> rfl

theorem Redex.single {i : instr} (h : toVal i = none) : Redex [i] := ⟨[], i, rfl, h⟩

theorem Redex.cons {x : instr} {L : List instr} (hx : (toVal x).isSome = true)
    (h : Redex L) : Redex (x :: L) := by
  obtain ⟨ws, i, rfl, hi⟩ := h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hx
  exact ⟨w :: ws, i, by simp [instr_val_of_toVal hw], hi⟩

theorem Redex.map_append (ws : List val) {L : List instr} (h : Redex L) :
    Redex (ws.map instr_val ++ L) := by
  obtain ⟨ws', i, rfl, hi⟩ := h
  exact ⟨ws ++ ws', i, by simp, hi⟩

/-- Peel one value off the front of a redex. -/
macro "redex_cons" : tactic => `(tactic| refine Redex.cons
  (by first | rfl | simp only [toVal_instr_val, toVal_instr_ref, Option.isSome_some]) ?_)

/-- The redex form of the left side of a base rule. -/
macro "redex" : tactic => `(tactic| first
  | exact Redex.of_split rfl
  | exact Redex.vals_append _ _ rfl
  | (repeat redex_cons); exact Redex.single rfl
  | (refine Redex.map_append _ ?_; (repeat redex_cons); exact Redex.single rfl))

theorem ne_nil_of_bne {α : Type} [BEq α] {l : List α} (h : (l != []) = true) : l ≠ [] := by
  rintro rfl; contradiction

theorem ne_nil_or_of_bne {α β : Type} [BEq α] [BEq β] {l : List α} {r : List β}
    (h : ((l != []) || (r != [])) = true) : l ≠ [] ∨ r ≠ [] := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact .inl (ne_nil_of_bne h)
  · exact .inr (ne_nil_of_bne h)

/-- The left side of every `Step_pure` rule is a redex, except for `trap_instrs`. -/
theorem Step_pure.lhs {L L' : List instr} (h : Step_pure L L') :
    Redex L ∨ ∃ ws rest, L = ws.map instr_val ++ .TRAP :: rest ∧ L' = [.TRAP] ∧
      (ws ≠ [] ∨ rest ≠ []) := by
  cases h
  case trap_instrs val_lst instr_lst hne _ _ _ =>
    right
    exact ⟨val_lst, instr_lst, by simp, rfl, ne_nil_or_of_bne hne⟩
  all_goals (left; redex)

/-- The instruction sequence of a configuration. -/
def instrsOf : config → List instr
  | .mk_config _ is => is

@[simp] theorem instrsOf_mk (z : state) (is : List instr) : instrsOf (.mk_config z is) = is := rfl

/-- The left side of every `Step_read` rule is a redex, except for `throw_ref_instrs`. -/
theorem Step_read.lhs {c : config} {L' : List instr} (h : Step_read c L') :
    Redex (instrsOf c) ∨ ∃ ws a rest, instrsOf c = ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: rest ∧
      L' = [.REF_EXN_ADDR a, .THROW_REF] ∧ (ws ≠ [] ∨ rest ≠ []) := by
  cases h
  case throw_ref_instrs z val_lst a instr_lst hne _ _ _ =>
    right
    exact ⟨val_lst, a, instr_lst, by simp, rfl, ne_nil_or_of_bne hne⟩
  all_goals (left; simp only [instrsOf_mk]; redex)

/-- The left side of every `Step` rule other than `pure`, `read` and `ctxt_instrs` is a redex. -/
theorem Step.lhs_base {c c' : config} (h : Step c c') :
    (∃ z L L', c = .mk_config z L ∧ c' = .mk_config z L' ∧ Step_pure L L') ∨
    (∃ z L', c' = .mk_config z L' ∧ Step_read c L') ∨
    (∃ z vals L₀ L₁ z' L₀', c = .mk_config z (vals.map instr_val ++ (L₀ ++ L₁)) ∧
      c' = .mk_config z' (vals.map instr_val ++ (L₀' ++ L₁)) ∧
      Step (.mk_config z L₀) (.mk_config z' L₀') ∧ (vals ≠ [] ∨ L₁ ≠ [])) ∨
    Redex (instrsOf c) := by
  cases h
  case pure z L L' hp _ _ => exact .inl ⟨z, L, L', rfl, rfl, hp⟩
  case read z L L' hr _ _ => exact .inr (.inl ⟨z, L', rfl, hr⟩)
  case ctxt_instrs z vals L₀ L₁ z' L₀' hs hne _ _ _ _ =>
    exact .inr (.inr (.inl ⟨z, vals, L₀, L₁, z', L₀', rfl, rfl, hs, ne_nil_or_of_bne hne⟩))
  all_goals (right; right; right; simp only [instrsOf_mk]; redex)

end SpecTecWP
