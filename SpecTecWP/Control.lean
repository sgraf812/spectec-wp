import SpecTecWP.Label

/-!
# Control flow

`Safe.label` transports `Safe` of the body of a label `LABEL_ k K B` to `Safe` of the label
behind the stack `vs`. The postconditions of the body are `Label.post` and `Label.epost`: the
body's values `bs` end as the stack `bs ++ vs`, `br 0` with the stack `bs` continues with `K`
on the stack `bs.take k ++ vs`, and `br (l + 1)` leaves the label as `br l`.
-/

namespace SpecTecWP

/-! ## Well-formedness of label configurations -/

theorem wf_val_of_wf_instr {v : val} (h : wf_instr (instr_val v)) : wf_val v := by
  cases v <;> cases h <;> constructor <;> assumption

theorem wf_label_iff {k : n} {K B : List instr} :
    wf_instr (.LABEL_ k K B) ↔ (∀ i ∈ K, wf_instr i) ∧ ∀ i ∈ B, wf_instr i := by
  constructor
  · intro h; cases h with | instr_case_112 _ _ _ hK hB => exact ⟨hK, hB⟩
  · rintro ⟨hK, hB⟩; exact .instr_case_112 _ _ _ hK hB

theorem wf_lab_iff {z : state} {vs : Stack} {k : n} {K B : List instr} :
    wf_config (cfg z vs [.LABEL_ k K B]) ↔ wf_state z ∧
      (∀ i ∈ vs.reverse.map instr_val, wf_instr i) ∧ (∀ i ∈ K, wf_instr i) ∧
      ∀ i ∈ B, wf_instr i := by
  rw [cfg_eq, wf_config_iff]
  constructor
  · rintro ⟨hs, h⟩
    have hl := wf_label_iff.mp (h (.LABEL_ k K B) (by simp))
    exact ⟨hs, fun i hi => h i (List.mem_append_left _ hi), hl.1, hl.2⟩
  · rintro ⟨hs, hv, hK, hB⟩
    refine ⟨hs, fun i hi => ?_⟩
    rcases List.mem_append.mp hi with hi | hi
    · exact hv i hi
    · simp only [List.mem_singleton] at hi; subst hi; exact wf_label_iff.mpr ⟨hK, hB⟩

/-- A step of the body is a step of the label. -/
theorem Step.lab {z z' : state} {vs : Stack} {k : n} {K B B' : List instr}
    (h : Step (.mk_config z B) (.mk_config z' B')) (hwf : wf_config (cfg z vs [.LABEL_ k K B])) :
    Step (cfg z vs [.LABEL_ k K B]) (cfg z' vs [.LABEL_ k K B']) := by
  obtain ⟨-, -, hK, -⟩ := wf_lab_iff.mp hwf
  have ht := wf_config_iff.mp (Step.wf_target h)
  rw [cfg_eq] at hwf
  have h1 : wf_config (.mk_config z [.LABEL_ k K B]) := wf_config_append_right hwf
  have h2 : wf_config (.mk_config z' [.LABEL_ k K B']) :=
    wf_config_iff.mpr ⟨ht.1, by simpa using wf_label_iff.mpr ⟨hK, ht.2⟩⟩
  rw [cfg_eq, cfg_eq]
  exact Step.under vs.reverse
    (.ctxt_label z k K B z' B' h h1 h2 (Step.wf_source h) (Step.wf_target h)) hwf

/-- A `Step_pure` step of the label is a step of the label behind the stack. -/
theorem Step.lab_pure {z : state} {vs : Stack} {k : n} {K B L : List instr}
    (hp : Step_pure [.LABEL_ k K B] L) (hwf : wf_config (cfg z vs [.LABEL_ k K B]))
    (hL : ∀ i ∈ L, wf_instr i) :
    Step (cfg z vs [.LABEL_ k K B]) (.mk_config z (vs.reverse.map instr_val ++ L)) := by
  obtain ⟨hs, -⟩ := wf_lab_iff.mp hwf
  rw [cfg_eq] at hwf ⊢
  exact Step.under vs.reverse
    (.pure z _ _ hp (wf_config_append_right hwf) (wf_config_iff.mpr ⟨hs, hL⟩)) hwf

/-! ## The first non-value instruction -/

/-- The first non-value instruction of a list. -/
def fnv (L : List instr) : Option instr := L.find? (fun x => (toVal x).isNone)

theorem fnv_vals_append (ws : List val) (L : List instr) :
    fnv (ws.map instr_val ++ L) = fnv L := find_nonval_vals_append ws L
theorem fnv_vals (ws : List val) : fnv (ws.map instr_val) = none := find_nonval_vals ws
theorem fnv_ref_exn (a : addr) (t : List instr) : fnv (.REF_EXN_ADDR a :: t) = fnv t := rfl
theorem fnv_br (l : labelidx) (t : List instr) : fnv (.BR l :: t) = some (.BR l) := rfl
theorem fnv_ret (t : List instr) : fnv (.RETURN :: t) = some .RETURN := rfl
theorem fnv_rcr (yy : typeuse) (t : List instr) :
    fnv (.RETURN_CALL_REF yy :: t) = some (.RETURN_CALL_REF yy) := rfl
theorem fnv_trap (t : List instr) : fnv (.TRAP :: t) = some .TRAP := rfl
theorem fnv_throw (t : List instr) : fnv (.THROW_REF :: t) = some .THROW_REF := rfl

/-- Closes a goal with a hypothesis `h` that equates two lists with different first
non-value instructions. -/
macro "body_contra" h:term : tactic => `(tactic| (
  have h' := congrArg fnv $h
  simp only [code_eq, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append, List.append_nil, fnv_vals_append, fnv_vals, fnv_ref_exn, fnv_br, fnv_ret,
    fnv_rcr, fnv_trap, fnv_throw, reduceCtorEq, Option.some.injEq] at h'))

theorem take_of_reverse {bs A C : List val} {k : Nat} (h : bs.reverse = A ++ C)
    (hC : C.length = k) : C = (bs.take k).reverse := by
  have hb : bs = C.reverse ++ A.reverse := by
    rw [← List.reverse_reverse bs, h, List.reverse_append]
  rw [hb, List.take_left' (by simpa using hC), List.reverse_reverse]

/-! ## `Safe` of a label from `Safe` of its body -/

/-- The postcondition of the body of a label behind the stack `vs`. -/
def Label.post (vs : Stack) (Q : Assn) : Assn := fun z bs => Q z (bs ++ vs)

/-- The exception postcondition of the body of `LABEL_ k K B` behind the stack `vs`. -/
def Label.epost (k : n) (K : List instr) (vs : Stack) (Q : Assn) (E : EAssn) : EAssn
  | .br (.mk_uN 0) bs => fun z => k ≤ bs.length ∧ Code.wp K Q E z (bs.take k ++ vs)
  | .br (.mk_uN (l + 1)) bs => E (.br (.mk_uN l) (bs ++ vs))
  | .ret bs => E (.ret (bs ++ vs))
  | .throw a => E (.throw a)
  | .trap => E .trap

theorem Safe.label_trap {k : n} {K : List instr} {vs : Stack} {Q : Assn} {E : EAssn}
    {z : state} (he : E .trap z) :
    ∀ (m : Nat) (ws : List val) (t : List instr), ws.length + t.length = m →
      wf_config (cfg z vs [.LABEL_ k K (ws.map instr_val ++ .TRAP :: t)]) →
      Safe Q E (cfg z vs [.LABEL_ k K (ws.map instr_val ++ .TRAP :: t)]) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro ws t hm hwf
  obtain ⟨hs, -, hK, hB⟩ := wf_lab_iff.mp hwf
  have hT : wf_instr .TRAP := hB _ (by simp)
  refine .step _ ?_ ?_
  · by_cases hbase : ws = [] ∧ t = []
    · obtain ⟨rfl, rfl⟩ := hbase
      exact ⟨_, Step.lab_pure (.trap_label k K (wf_label_iff.mpr ⟨hK, by simpa using hT⟩) hT)
        hwf (by simpa using hT)⟩
    · have hne : ws ≠ [] ∨ t ≠ [] := by
        by_cases h : ws = [] <;> simp_all
      have hp : Step_pure (ws.map instr_val ++ .TRAP :: t) [.TRAP] :=
        .trap_instrs ws t hne
          (fun v hv => wf_val_of_wf_instr (hB _ (List.mem_append_left _ (List.mem_map_of_mem hv))))
          (fun i hi => hB i (List.mem_append_right _ (List.mem_cons_of_mem _ hi))) hT
      exact ⟨_, Step.lab (.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hB⟩)
        (wf_config_iff.mpr ⟨hs, by simpa using hT⟩)) hwf⟩
  · intro c'' hs''
    have hs₀ := hs''
    rw [cfg_eq] at hs''
    obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
    cases hl with
    | ctxt hb =>
      obtain ⟨ws', t', heq, hlen⟩ := Step.trap_succ hb
      simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have := ih _ (by omega) ws' t' rfl (by rw [cfg_eq]; exact Step.wf_target hs₀)
      rwa [cfg_eq] at this
    | trap _ =>
      have := Safe.exit (Q := Q) z _ _ (.trap vs []) he
      simpa [code_eq] using this
    | vals _ hB' => body_contra hB'
    | br_zero _ _ _ _ _ _ hB' => body_contra hB'
    | br_succ _ _ _ _ hB' => body_contra hB'
    | ret _ _ hB' => body_contra hB'
    | return_call_ref _ _ _ hB' => body_contra hB'
    | throw _ hB' => body_contra hB'

theorem Safe.label_throw {k : n} {K : List instr} {vs : Stack} {Q : Assn} {E : EAssn}
    {z : state} {a : addr} (he : E (.throw a) z) :
    ∀ (m : Nat) (ws : List val) (t : List instr), ws.length + t.length = m →
      wf_config (cfg z vs [.LABEL_ k K (ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: t)]) →
      Safe Q E (cfg z vs [.LABEL_ k K (ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: t)]) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro ws t hm hwf
  obtain ⟨hs, -, hK, hB⟩ := wf_lab_iff.mp hwf
  have hR : wf_instr (.REF_EXN_ADDR a) := hB _ (by simp)
  have hT : wf_instr .THROW_REF := hB _ (by simp)
  have hRT : ∀ i ∈ [instr.REF_EXN_ADDR a, .THROW_REF], wf_instr i := by
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  refine .step _ ?_ ?_
  · by_cases hbase : ws = [] ∧ t = []
    · obtain ⟨rfl, rfl⟩ := hbase
      have h1 : wf_config (.mk_config z [.LABEL_ k K [.REF_EXN_ADDR a, .THROW_REF]]) := by
        rw [cfg_eq] at hwf; exact wf_config_append_right hwf
      have hstep : Step (.mk_config z [.LABEL_ k K [.REF_EXN_ADDR a, .THROW_REF]])
          (.mk_config z [.REF_EXN_ADDR a, .THROW_REF]) :=
        .read z _ _ (.throw_ref_label z k K a h1 hR hT) h1 (wf_config_iff.mpr ⟨hs, hRT⟩)
      have := Step.under vs.reverse hstep (by rwa [cfg_eq] at hwf)
      rw [cfg_eq]
      exact ⟨_, this⟩
    · have hne : ws ≠ [] ∨ t ≠ [] := by
        by_cases h : ws = [] <;> simp_all
      have hwb : wf_config (.mk_config z (ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: t)) :=
        wf_config_iff.mpr ⟨hs, hB⟩
      have hstep : Step (.mk_config z (ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: t))
          (.mk_config z [.REF_EXN_ADDR a, .THROW_REF]) :=
        .read z _ _ (.throw_ref_instrs z ws a t hne hwb hR hT) hwb (wf_config_iff.mpr ⟨hs, hRT⟩)
      exact ⟨_, Step.lab hstep hwf⟩
  · intro c'' hs''
    have hs₀ := hs''
    rw [cfg_eq] at hs''
    obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
    cases hl with
    | ctxt hb =>
      rw [show ws.map instr_val ++ .REF_EXN_ADDR a :: .THROW_REF :: t =
        (ws ++ [val.REF_EXN_ADDR a]).map instr_val ++ .THROW_REF :: t by simp [instr_val]] at hb
      obtain ⟨ws', t', heq, hlast, hlen⟩ := Step.throw_succ (a := a) (by simp) hb
      obtain ⟨ws₀, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have := ih _ (by omega) ws₀ t' rfl (by
        rw [cfg_eq]
        have := Step.wf_target hs₀
        simpa [instr_val] using this)
      rw [cfg_eq] at this
      simpa [instr_val] using this
    | throw a' hB' =>
      have hl := congrArg List.length hB'
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hl
      obtain ⟨rfl, rfl⟩ : ws = [] ∧ t = [] := by
        constructor <;> apply List.eq_nil_of_length_eq_zero <;> omega
      have := Safe.exit (Q := Q) z _ _ (.throw vs a []) he
      simpa [code_eq] using this
    | trap hB' => body_contra hB'
    | vals _ hB' => body_contra hB'
    | br_zero _ _ _ _ _ _ hB' => body_contra hB'
    | br_succ _ _ _ _ hB' => body_contra hB'
    | ret _ _ hB' => body_contra hB'
    | return_call_ref _ _ _ hB' => body_contra hB'

/-- `Safe` of the body of a label gives `Safe` of the label behind the stack `vs`. -/
theorem Safe.label {k : n} {K : List instr} {vs : Stack} {Q : Assn} {E : EAssn} {c : config}
    (h : Safe (Label.post vs Q) (Label.epost k K vs Q E) c) :
    ∀ z B, c = .mk_config z B → wf_config (cfg z vs [.LABEL_ k K B]) →
      Safe Q E (cfg z vs [.LABEL_ k K B]) := by
  induction h with
  | vals z bs hq =>
    intro z' B hc hwf
    simp only [cfg, config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hBv : code bs [] = bs.reverse.map instr_val := by simp [code_eq]
    obtain ⟨hs, -, hK, hB⟩ := wf_lab_iff.mp hwf
    refine .step _ ⟨_, Step.lab_pure (L := code bs []) ?_ hwf hB⟩ ?_
    · rw [hBv]
      exact .label_vals k K bs.reverse
        (wf_label_iff.mpr ⟨hK, fun i hi => hB i (by rw [hBv]; exact hi)⟩)
    · intro c'' hs''
      rw [cfg_eq] at hs''
      obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
      cases hl with
      | ctxt hb => rw [hBv] at hb; exact (Step.not_vals hb).elim
      | vals _ _ =>
        have := Safe.vals (E := E) z (bs ++ vs) hq
        rw [cfg_eq] at this
        simpa [code_eq] using this
      | br_zero _ _ _ _ _ _ hB' => body_contra hB'
      | br_succ _ _ _ _ hB' => body_contra hB'
      | ret _ _ hB' => body_contra hB'
      | return_call_ref _ _ _ hB' => body_contra hB'
      | trap hB' => body_contra hB'
      | throw _ hB' => body_contra hB'
  | exit z B₀ e hx he =>
    intro z' B hc hwf
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨hs, -, hK, hB⟩ := wf_lab_iff.mp hwf
    cases hx with
    | br bs l rest =>
      obtain ⟨l⟩ := l
      have hBv : code bs (.BR (.mk_uN l) :: rest) =
          bs.reverse.map instr_val ++ .BR (.mk_uN l) :: rest := code_eq _ _
      cases l with
      | zero =>
        obtain ⟨hk, hKwp⟩ := he
        have eB : code bs (.BR (.mk_uN 0) :: rest) =
            ((((bs.drop k).reverse.map instr_val ++ (bs.take k).reverse.map instr_val) ++
              [.BR (.mk_uN 0)]) ++ rest) := by
          rw [code_eq]
          simp only [List.append_assoc, List.singleton_append]
          rw [← List.append_assoc, ← List.map_append, ← List.reverse_append, List.take_append_drop]
        have hw'' : ∀ i ∈ (bs.take k).reverse.map instr_val ++ K, wf_instr i := by
          intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact hB i (by rw [eB]; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hi)))
          · exact hK i hi
        refine .step _ ⟨_, Step.lab_pure (L := (bs.take k).reverse.map instr_val ++ K) ?_ hwf hw''⟩ ?_
        · rw [eB]
          exact .br_label_zero k K _ _ _ _ rfl
            (wf_label_iff.mpr ⟨hK, fun i hi => hB i (by rw [eB]; exact hi)⟩)
            (by simp only [List.length_reverse, List.length_take]; exact (Nat.min_eq_left hk).symm)
            (by simp only [List.length_reverse, List.length_take]; exact Nat.min_eq_left hk)
        · intro c'' hs''
          have hs₀ := hs''
          rw [cfg_eq] at hs''
          obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
          cases hl with
          | ctxt hb => rw [hBv] at hb; exact (Step.not_br hb).elim
          | br_zero vs'' ws l' rest' _ hlen hB' =>
            rw [hBv, ← List.map_append] at hB'
            obtain ⟨hrev, -, -⟩ := vals_cons_inj hB' rfl rfl
            obtain rfl := take_of_reverse hrev hlen
            have e : config.mk_config z (vs.reverse.map instr_val ++
                ((bs.take k).reverse.map instr_val ++ K)) = cfg z (bs.take k ++ vs) K := by
              simp [cfg_eq]
            rw [e]
            exact hKwp (by rw [← e]; exact Step.wf_target hs₀)
          | br_succ ws l' rest' hpos hB' =>
            rw [hBv] at hB'
            obtain ⟨-, hl', -⟩ := vals_cons_inj hB' rfl rfl
            cases hl'
            simp [proj_uN_0] at hpos
          | vals _ hB' => body_contra hB'
          | ret _ _ hB' => body_contra hB'
          | return_call_ref _ _ _ hB' => body_contra hB'
          | trap hB' => body_contra hB'
          | throw _ hB' => body_contra hB'
      | succ l =>
        have eB : code bs (.BR (.mk_uN (l + 1)) :: rest) =
            (bs.reverse.map instr_val ++ [.BR (.mk_uN (l + 1))]) ++ rest := by simp [code_eq]
        have hwBR : wf_instr (.BR (.mk_uN (l + 1))) := hB _ (by simp [code_eq])
        have hwBR' : wf_instr (.BR (.mk_uN (Int.toNat (Int.ofNat (proj_uN_0 (.mk_uN (l + 1))) -
            Int.ofNat 1)))) := by
          cases hwBR with
          | instr_case_7 _ hu =>
            cases hu with
            | uN_case_0 _ hb hpos =>
              refine .instr_case_7 _ (.uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩ hpos)
              have := hb.2
              simp only [proj_uN_0, toNat_pred, Nat.add_sub_cancel]
              exact Nat.le_of_succ_le this
        have hw'' : ∀ i ∈ bs.reverse.map instr_val ++
            [.BR (.mk_uN (Int.toNat (Int.ofNat (proj_uN_0 (.mk_uN (l + 1))) - Int.ofNat 1)))],
            wf_instr i := by
          intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact hB i (by rw [hBv]; exact List.mem_append_left _ hi)
          · simp only [List.mem_singleton] at hi; subst hi; exact hwBR'
        refine .step _ ⟨_, Step.lab_pure ?_ hwf hw''⟩ ?_
        · rw [eB]
          exact .br_label_succ k K _ _ _ (by simp [proj_uN_0])
            (wf_label_iff.mpr ⟨hK, fun i hi => hB i (by rw [eB]; exact hi)⟩) hwBR'
            (by simp [proj_uN_0])
        · intro c'' hs''
          rw [cfg_eq] at hs''
          obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
          cases hl with
          | ctxt hb => rw [hBv] at hb; exact (Step.not_br hb).elim
          | br_succ ws l' rest' _ hB' =>
            rw [hBv] at hB'
            obtain ⟨rfl, hl', -⟩ := vals_cons_inj hB' rfl rfl
            cases hl'
            have := Safe.exit (Q := Q) z _ _ (.br (bs ++ vs) (.mk_uN l) []) he
            simpa [code_eq, proj_uN_0] using this
          | br_zero _ _ l' _ hl0 _ hB' =>
            rw [hBv, ← List.map_append] at hB'
            obtain ⟨-, hl', -⟩ := vals_cons_inj hB' rfl rfl
            cases hl'
            simp [proj_uN_0] at hl0
          | vals _ hB' => body_contra hB'
          | ret _ _ hB' => body_contra hB'
          | return_call_ref _ _ _ hB' => body_contra hB'
          | trap hB' => body_contra hB'
          | throw _ hB' => body_contra hB'
    | ret bs rest =>
      have hBv : code bs (.RETURN :: rest) = bs.reverse.map instr_val ++ .RETURN :: rest :=
        code_eq _ _
      have eB : code bs (.RETURN :: rest) = (bs.reverse.map instr_val ++ [.RETURN]) ++ rest := by
        simp [code_eq]
      have hw'' : ∀ i ∈ bs.reverse.map instr_val ++ [.RETURN], wf_instr i := by
        intro i hi
        exact hB i (by rw [eB]; exact List.mem_append_left _ hi)
      refine .step _ ⟨_, Step.lab_pure ?_ hwf hw''⟩ ?_
      · rw [eB]
        exact .return_label k K _ _ (wf_label_iff.mpr ⟨hK, fun i hi => hB i (by rw [eB]; exact hi)⟩)
          (hB _ (by simp [code_eq]))
      · intro c'' hs''
        rw [cfg_eq] at hs''
        obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
        cases hl with
        | ctxt hb => rw [hBv] at hb; exact (Step.not_ret hb).elim
        | ret ws rest' hB' =>
          rw [hBv] at hB'
          obtain ⟨rfl, -, -⟩ := vals_cons_inj hB' rfl rfl
          have := Safe.exit (Q := Q) z _ _ (.ret (bs ++ vs) []) he
          simpa [code_eq] using this
        | vals _ hB' => body_contra hB'
        | br_zero _ _ _ _ _ _ hB' => body_contra hB'
        | br_succ _ _ _ _ hB' => body_contra hB'
        | return_call_ref _ _ _ hB' => body_contra hB'
        | trap hB' => body_contra hB'
        | throw _ hB' => body_contra hB'
    | throw bs a rest =>
      have := Safe.label_throw (k := k) (K := K) (vs := vs) (Q := Q) (E := E) he _ bs.reverse rest rfl
        (by rwa [code_eq] at hwf)
      rwa [code_eq]
    | trap bs rest =>
      have := Safe.label_trap (k := k) (K := K) (vs := vs) (Q := Q) (E := E) he _ bs.reverse rest rfl
        (by rwa [code_eq] at hwf)
      rwa [code_eq]
  | step c hprog _ ih =>
    intro z B hc hwf
    subst hc
    obtain ⟨⟨z₁, B₁⟩, hs⟩ := hprog
    refine .step _ ⟨_, Step.lab hs hwf⟩ ?_
    intro c'' hs''
    have hs₀ := hs''
    rw [cfg_eq] at hs''
    obtain ⟨z', L'', hl, rfl⟩ := Step.redex_label hs''
    cases hl with
    | ctxt hb =>
      have := ih _ hb z' _ rfl (by rw [cfg_eq]; exact Step.wf_target hs₀)
      rwa [cfg_eq] at this
    | vals _ hB => subst hB; exact (Step.not_vals hs).elim
    | br_zero _ _ _ _ _ _ hB =>
      subst hB; rw [← List.map_append] at hs; exact (Step.not_br hs).elim
    | br_succ _ _ _ _ hB => subst hB; exact (Step.not_br hs).elim
    | ret _ _ hB => subst hB; exact (Step.not_ret hs).elim
    | return_call_ref _ _ _ hB => subst hB; exact (Step.not_return_call_ref hs).elim
    | trap hB => subst hB; exact (Step.not_trap hs).elim
    | throw _ hB => subst hB; exact (Step.not_throw hs).elim

/-! ## `block` and `loop` -/

theorem Step_read.block_redex {z : state} {ws : List val} {B L : List instr}
    (h : Step_read (.mk_config z (ws.map instr_val ++ [.BLOCK (._RESULT none) B])) L) :
    ws = [] ∧ L = [.LABEL_ 0 [] B] := by
  generalize hc : config.mk_config z (ws.map instr_val ++ [.BLOCK (._RESULT none) B]) = c at h
  cases h
  case block z' vm vals bt B' k t₁ t₂ var hbt hvar _ _ _ _ hm₁ hm₂ hk _ =>
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hL⟩ := hc
    obtain ⟨rfl, hi, -⟩ := vals_cons_inj hL rfl rfl
    simp only [instr.BLOCK.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    cases hbt
    cases hvar
    have hv : ws = [] := List.eq_nil_of_length_eq_zero (hm₁.symm.trans hm₂)
    subst hv
    subst hk
    exact ⟨rfl, rfl⟩
  all_goals
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hL⟩ := hc
    list_contra hL

theorem Step_read.loop_redex {z : state} {ws : List val} {B L : List instr}
    (h : Step_read (.mk_config z (ws.map instr_val ++ [.LOOP (._RESULT none) B])) L) :
    ws = [] ∧ L = [.LABEL_ 0 [.LOOP (._RESULT none) B] B] := by
  generalize hc : config.mk_config z (ws.map instr_val ++ [.LOOP (._RESULT none) B]) = c at h
  cases h
  case loop z' vm vals bt B' t₁ k t₂ var hbt hvar _ _ _ _ hm₁ hm₂ _ _ =>
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hL⟩ := hc
    obtain ⟨rfl, hi, -⟩ := vals_cons_inj hL rfl rfl
    simp only [instr.LOOP.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    cases hbt
    cases hvar
    have hv : ws = [] := List.eq_nil_of_length_eq_zero (hm₁.symm.trans hm₂)
    subst hv
    have hvm : vm = 0 := hm₁
    subst hvm
    exact ⟨rfl, rfl⟩
  all_goals
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hL⟩ := hc
    list_contra hL

theorem wf_instrtype_nil : wf_instrtype (.mk_instrtype (.mk_list []) [] (.mk_list [])) :=
  .instrtype_case_0 _ _ _ (by simp [proj_list_0]) (fun _ hx => by cases hx) (fun _ hx => by cases hx)
    (by simp [proj_list_0]) (fun _ hx => by cases hx)

/-- `block` with the empty block type runs its body on the empty stack inside a label of
arity `0` with the empty continuation. -/
theorem Code.wp_block {B : List instr} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (h : Code.wp B (Label.post vs Q) (Label.epost 0 [] vs Q E) z []) :
    Code.wp [.BLOCK (._RESULT none) B] Q E z vs := by
  intro hwf
  have hwf' := hwf
  rw [cfg_eq] at hwf'
  obtain ⟨hs, hi⟩ := wf_config_iff.mp hwf'
  have hwB : wf_instr (.BLOCK (._RESULT none) B) := hi _ (by simp)
  have hB : ∀ i ∈ B, wf_instr i := by cases hwB; assumption
  have hvals : ∀ i ∈ vs.reverse.map instr_val, wf_instr i :=
    fun i h => hi i (List.mem_append_left _ h)
  have hwfL : wf_config (cfg z vs [.LABEL_ 0 [] B]) :=
    wf_lab_iff.mpr ⟨hs, hvals, by simp, hB⟩
  have hw1 : wf_config (.mk_config z [.BLOCK (._RESULT none) B]) :=
    wf_config_iff.mpr ⟨hs, by simpa using hwB⟩
  have hr : Step_read (.mk_config z (([] : List val).map instr_val ++ [.BLOCK (._RESULT none) B]))
      [.LABEL_ 0 [] (([] : List val).map instr_val ++ B)] :=
    .block z 0 [] (._RESULT none) B 0 [] [] _ (.fun_blocktype__case_1 z none) rfl
      wf_instrtype_nil hw1 (wf_label_iff.mpr ⟨by simp, by simpa using hB⟩) wf_instrtype_nil
      rfl rfl rfl rfl
  have hstep : Step (.mk_config z [.BLOCK (._RESULT none) B]) (.mk_config z [.LABEL_ 0 [] B]) :=
    .read z _ _ hr hw1 (wf_config_iff.mpr ⟨hs, by simpa using wf_label_iff.mpr ⟨by simp, hB⟩⟩)
  refine .step _ ⟨_, Step.under vs.reverse hstep hwf'⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z (vs.reverse.map instr_val ++ [.BLOCK (._RESULT none) B])) c' := hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hr', rfl⟩ := Step.redex_read rfl hs''
  obtain ⟨rfl, rfl⟩ := Step_read.block_redex hr'
  simp only [List.append_nil] at hsplit
  subst hsplit
  have hb := h (by rw [cfg_eq]; simpa using wf_config_iff.mpr ⟨hs, hB⟩)
  have := Safe.label hb z B (by simp [cfg_eq]) hwfL
  rwa [cfg_eq] at this

/-- `loop` with the empty block type runs its body on the empty stack inside a label of arity
`0` whose continuation is the loop. -/
theorem Code.wp_loop {B : List instr} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (h : Code.wp B (Label.post vs Q) (Label.epost 0 [.LOOP (._RESULT none) B] vs Q E) z []) :
    Code.wp [.LOOP (._RESULT none) B] Q E z vs := by
  intro hwf
  have hwf' := hwf
  rw [cfg_eq] at hwf'
  obtain ⟨hs, hi⟩ := wf_config_iff.mp hwf'
  have hwB : wf_instr (.LOOP (._RESULT none) B) := hi _ (by simp)
  have hB : ∀ i ∈ B, wf_instr i := by cases hwB; assumption
  have hvals : ∀ i ∈ vs.reverse.map instr_val, wf_instr i :=
    fun i h => hi i (List.mem_append_left _ h)
  have hK : ∀ i ∈ [instr.LOOP (._RESULT none) B], wf_instr i := by simpa using hwB
  have hwfL : wf_config (cfg z vs [.LABEL_ 0 [.LOOP (._RESULT none) B] B]) :=
    wf_lab_iff.mpr ⟨hs, hvals, hK, hB⟩
  have hw1 : wf_config (.mk_config z [.LOOP (._RESULT none) B]) := wf_config_iff.mpr ⟨hs, hK⟩
  have hr : Step_read (.mk_config z (([] : List val).map instr_val ++ [.LOOP (._RESULT none) B]))
      [.LABEL_ 0 [.LOOP (._RESULT none) B] (([] : List val).map instr_val ++ B)] :=
    .loop z 0 [] (._RESULT none) B [] 0 [] _ (.fun_blocktype__case_1 z none) rfl
      wf_instrtype_nil hw1 (wf_label_iff.mpr ⟨hK, by simpa using hB⟩) wf_instrtype_nil
      rfl rfl rfl rfl
  have hstep : Step (.mk_config z [.LOOP (._RESULT none) B])
      (.mk_config z [.LABEL_ 0 [.LOOP (._RESULT none) B] B]) :=
    .read z _ _ hr hw1 (wf_config_iff.mpr ⟨hs, by simpa using wf_label_iff.mpr ⟨hK, hB⟩⟩)
  refine .step _ ⟨_, Step.under vs.reverse hstep hwf'⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z (vs.reverse.map instr_val ++ [.LOOP (._RESULT none) B])) c' := hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hr', rfl⟩ := Step.redex_read rfl hs''
  obtain ⟨rfl, rfl⟩ := Step_read.loop_redex hr'
  simp only [List.append_nil] at hsplit
  subst hsplit
  have hb := h (by rw [cfg_eq]; simpa using wf_config_iff.mpr ⟨hs, hB⟩)
  have := Safe.label hb z B (by simp [cfg_eq]) hwfL
  rwa [cfg_eq] at this

/-- The exception postcondition of the body of a loop with the invariant `inv` and the variant
`var`, entered in state `z₀` behind the stack `vs`: `br 0` restarts the loop, so it must
restore `inv` and decrease `var`. -/
def Loop.epost (inv : Assn) (var : state → Stack → Nat) (z₀ : state) (vs : Stack) (E : EAssn) :
    EAssn
  | .br (.mk_uN 0) _ => fun z => inv z vs ∧ var z vs < var z₀ vs
  | .br (.mk_uN (l + 1)) bs => E (.br (.mk_uN l) (bs ++ vs))
  | .ret bs => E (.ret (bs ++ vs))
  | .throw a => E (.throw a)
  | .trap => E .trap

/-- The loop rule: a loop terminates from every state that satisfies the invariant. -/
theorem Code.wp_loop_inv {B : List instr} {Q : Assn} {E : EAssn} {inv : Assn}
    {var : state → Stack → Nat}
    (step : ∀ z vs, inv z vs → Code.wp B (Label.post vs Q) (Loop.epost inv var z vs E) z [])
    {z : state} {vs : Stack} (hI : inv z vs) : Code.wp [.LOOP (._RESULT none) B] Q E z vs := by
  suffices key : ∀ m z, var z vs = m → inv z vs → Code.wp [.LOOP (._RESULT none) B] Q E z vs from
    key _ z rfl hI
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro z hm hI
  apply Code.wp_loop
  intro hwf
  refine Safe.mono (fun _ _ h => h) ?_ (step z vs hI hwf)
  intro e z' he
  rcases e with ⟨⟨_ | l⟩, bs⟩ | bs | a | _
  · obtain ⟨hI', hlt⟩ := he
    refine ⟨Nat.zero_le _, ?_⟩
    rw [List.take_zero, List.nil_append]
    exact ih _ (hm ▸ hlt) z' rfl hI'
  all_goals exact he

/-! ## `br` and `br_if` -/

theorem Code.wp_br {l : labelidx} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (h : E (.br l vs) z) : Code.wp [.BR l] Q E z vs := fun _ => .exit _ _ _ (.br vs l []) h

theorem Step_pure.br_if_redex {ws : List val} {l : labelidx} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.BR_IF l]) L) :
    ∃ c : num_, ws = [.CONST .I32 c] ∧
      ((proj_uN_0 (proj_num__0 c).get! ≠ 0 ∧ L = [.BR l]) ∨
        (proj_uN_0 (proj_num__0 c).get! = 0 ∧ L = [])) := by
  generalize hL : ws.map instr_val ++ [.BR_IF l] = L₀ at h
  cases h
  case br_if_true c l' _ hnz _ _ _ =>
    have hL' : ws.map instr_val ++ [.BR_IF l] = [val.CONST .I32 c].map instr_val ++ [.BR_IF l'] :=
      hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.BR_IF.injEq, and_true] at hlast
    subst hlast
    exact ⟨c, map_instr_val_inj hws, .inl ⟨hnz, rfl⟩⟩
  case br_if_false c l' _ hz _ _ =>
    have hL' : ws.map instr_val ++ [.BR_IF l] = [val.CONST .I32 c].map instr_val ++ [.BR_IF l'] :=
      hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.BR_IF.injEq, and_true] at hlast
    subst hlast
    exact ⟨c, map_instr_val_inj hws, .inr ⟨hz, rfl⟩⟩
  all_goals list_contra hL

theorem Code.wp_br_if {l : labelidx} {x : uN} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hT : proj_uN_0 x ≠ 0 → E (.br l vs) z) (hF : proj_uN_0 x = 0 → Q z vs) :
    Code.wp [.BR_IF l] Q E z (.CONST .I32 (.mk_num__0 .I32 x) :: vs) := by
  intro hwf
  have hlist : (val.CONST .I32 (.mk_num__0 .I32 x) :: vs).reverse.map instr_val ++ [.BR_IF l] =
      vs.reverse.map instr_val ++ [.CONST .I32 (.mk_num__0 .I32 x), .BR_IF l] := by
    simp [instr_val]
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwc : wf_instr (.CONST .I32 (.mk_num__0 .I32 x)) := hi _ (by simp)
  have hwi : wf_instr (.BR_IF l) := hi _ (by simp)
  have hwb : wf_instr (.BR l) := by cases hwi; constructor; assumption
  have hsplit_of : ∀ c', Step (.mk_config z (vs.reverse.map instr_val ++
      [.CONST .I32 (.mk_num__0 .I32 x), .BR_IF l])) c' →
      ∃ L'', ((proj_uN_0 x ≠ 0 ∧ L'' = [.BR l]) ∨ (proj_uN_0 x = 0 ∧ L'' = [])) ∧
        c' = .mk_config z (vs.reverse.map instr_val ++ L'') := by
    intro c' hs'
    have hs'' : Step (.mk_config z ((vs.reverse ++ [val.CONST .I32 (.mk_num__0 .I32 x)]).map
        instr_val ++ [.BR_IF l])) c' := by simpa [instr_val] using hs'
    obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
    obtain ⟨d, rfl, hd⟩ := Step_pure.br_if_redex hp'
    obtain ⟨rfl, hd'⟩ := split_one hsplit
    cases hd'
    exact ⟨L'', by simpa [proj_num__0] using hd, rfl⟩
  by_cases hx : proj_uN_0 x = 0
  · have hp : Step_pure [.CONST .I32 (.mk_num__0 .I32 x), .BR_IF l] [] :=
      .br_if_false _ l (by simp [proj_num__0]) (by simp [proj_num__0, hx]) hwc hwi
    refine .step _ ⟨_, Step.under vs.reverse (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩)
      (wf_config_iff.mpr ⟨hs, by simp⟩)) hwf⟩ ?_
    intro c' hs'
    obtain ⟨L'', hL'', rfl⟩ := hsplit_of c' hs'
    rcases hL'' with ⟨hnz, -⟩ | ⟨-, rfl⟩
    · exact absurd hx hnz
    · have := Safe.vals (E := E) z vs (hF hx)
      simpa [cfg_eq] using this
  · have hp : Step_pure [.CONST .I32 (.mk_num__0 .I32 x), .BR_IF l] [.BR l] :=
      .br_if_true _ l (by simp [proj_num__0]) (by simpa [proj_num__0] using hx) hwc hwi hwb
    refine .step _ ⟨_, Step.under vs.reverse (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩)
      (wf_config_iff.mpr ⟨hs, by simpa using hwb⟩)) hwf⟩ ?_
    intro c' hs'
    obtain ⟨L'', hL'', rfl⟩ := hsplit_of c' hs'
    rcases hL'' with ⟨-, rfl⟩ | ⟨hz, -⟩
    · exact .exit _ _ _ (.br vs l []) (hT hx)
    · exact absurd hz hx

end SpecTecWP
