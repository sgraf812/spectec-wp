import SpecTecWP.Instr

/-!
# Weakest preconditions of the local variable instructions
-/

namespace SpecTecWP

theorem Step.redex_local_set_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (x : idx),
      c = .mk_config z (ws.map instr_val ++ [.LOCAL_SET x]) →
      ∃ (ws₁ : List val) (v : val), ws = ws₁ ++ [v] ∧
        c' = .mk_config (with_local z x v) (ws₁.map instr_val) := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro z ws x hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hL : ws.map instr_val ++ [.LOCAL_SET x] = L₀ at hp
    cases hp <;> list_contra hL
  case read z₀ L L' hr _ _ =>
    intro z ws x hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hcfg : config.mk_config z₀ (ws.map instr_val ++ [.LOCAL_SET x]) = c at hr
    cases hr
    all_goals
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨-, hcfg⟩ := hcfg
      list_contra hcfg
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws x hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split rfl hc hinner
    obtain ⟨ws₁', v, rfl, heq⟩ := ih z₀ ws₂ x rfl
    simp only [config.mk_config.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨vals ++ ws₁', v, by simp, by simp⟩
  case local_set z₀ v x' _ _ =>
    intro z ws x hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    have hc' : [v].map instr_val ++ [.LOCAL_SET x'] = ws.map instr_val ++ [.LOCAL_SET x] := hc
    obtain ⟨hws, hlast⟩ := List.append_inj' hc' rfl
    simp only [List.cons.injEq, instr.LOCAL_SET.injEq, and_true] at hlast
    subst hlast
    exact ⟨[], v, by simpa using (map_instr_val_inj hws).symm, rfl⟩
  all_goals
    intro z ws x hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    exfalso
    list_contra hc

theorem Code.wp_local_set {x : idx} {v : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hwz : wf_state (with_local z x v)) (hQ : Q (with_local z x v) vs) :
    Code.wp [.LOCAL_SET x] Q E z (v :: vs) := by
  intro hwf
  have hlist : (v :: vs).reverse.map instr_val ++ [.LOCAL_SET x] =
      vs.reverse.map instr_val ++ [instr_val v, .LOCAL_SET x] := by simp
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hstep : Step (.mk_config z [instr_val v, .LOCAL_SET x]) (.mk_config (with_local z x v) []) :=
    .local_set z v x (wf_config_iff.mpr ⟨hs, hi⟩) (wf_config_iff.mpr ⟨hwz, by simp⟩)
  refine .step _ ⟨_, Step.under vs.reverse hstep hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z ((vs.reverse ++ [v]).map instr_val ++ [.LOCAL_SET x])) c' := by
    simpa using hs'
  obtain ⟨ws₁, w, hsplit, rfl⟩ := Step.redex_local_set_aux hs'' z _ x rfl
  obtain ⟨rfl, rfl⟩ := split_one hsplit
  have := Safe.vals (E := E) (with_local z x v) vs hQ
  simpa [cfg_eq] using this

theorem Step_read.local_get_redex {z : state} {ws : List val} {x : idx} {L : List instr}
    (h : Step_read (.mk_config z (ws.map instr_val ++ [.LOCAL_GET x])) L) :
    ws = [] ∧ ∃ v, fun_local z x = some v ∧ L = [instr_val v] := by
  generalize hc : config.mk_config z (ws.map instr_val ++ [.LOCAL_GET x]) = c at h
  cases h
  case local_get z' x' v hl _ _ _ =>
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    have hc' : ws.map instr_val ++ [.LOCAL_GET x] = ([] : List val).map instr_val ++ [.LOCAL_GET x'] :=
      hc
    obtain ⟨hws, hlast⟩ := List.append_inj' hc' rfl
    simp only [List.cons.injEq, instr.LOCAL_GET.injEq, and_true] at hlast
    subst hlast
    exact ⟨map_instr_val_inj hws, v, hl, rfl⟩
  all_goals
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    list_contra hc

theorem Code.wp_local_get {x : idx} {v : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (hl : fun_local z x = some v) (hwv : wf_val v) (hQ : Q z (v :: vs)) :
    Code.wp [.LOCAL_GET x] Q E z vs := by
  intro hwf
  rw [cfg_eq] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwfR : wf_config (.mk_config z [.LOCAL_GET x]) := wf_config_iff.mpr ⟨hs, hi⟩
  have hr : Step_read (.mk_config z [.LOCAL_GET x]) [instr_val v] :=
    .local_get z x v hl hwv (by simp [Forall, hl, hwv]) hwfR
  have hstep := Step.read z _ _ hr hwfR
    (wf_config_iff.mpr ⟨hs, by simpa using wf_instr_of_wf_val hwv⟩)
  refine .step _ ⟨_, Step.under vs.reverse hstep hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z (vs.reverse.map instr_val ++ [.LOCAL_GET x])) c' := hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hr', rfl⟩ := Step.redex_read rfl hs''
  obtain ⟨rfl, w, hw, rfl⟩ := Step_read.local_get_redex hr'
  simp only [List.append_nil] at hsplit
  subst hsplit
  rw [hl] at hw
  cases hw
  have := Safe.vals (E := E) z (v :: vs) hQ
  simpa [cfg_eq] using this

theorem Step_pure.local_tee_redex {ws : List val} {x : idx} {L : List instr}
    (h : Step_pure (ws.map instr_val ++ [.LOCAL_TEE x]) L) :
    ∃ v, ws = [v] ∧ L = [instr_val v, instr_val v, .LOCAL_SET x] := by
  generalize hL : ws.map instr_val ++ [.LOCAL_TEE x] = L₀ at h
  cases h
  case local_tee v x' _ _ _ =>
    have hL' : ws.map instr_val ++ [.LOCAL_TEE x] = [v].map instr_val ++ [.LOCAL_TEE x'] := hL
    obtain ⟨hws, hlast⟩ := List.append_inj' hL' rfl
    simp only [List.cons.injEq, instr.LOCAL_TEE.injEq, and_true] at hlast
    subst hlast
    exact ⟨v, map_instr_val_inj hws, rfl⟩
  all_goals list_contra hL

theorem Code.wp_local_tee {x : idx} {v : val} {Q : Assn} {E : EAssn} {z : state} {vs : Stack}
    (h : Code.wp [.LOCAL_SET x] Q E z (v :: v :: vs)) :
    Code.wp [.LOCAL_TEE x] Q E z (v :: vs) := by
  intro hwf
  have hlist : (v :: vs).reverse.map instr_val ++ [.LOCAL_TEE x] =
      vs.reverse.map instr_val ++ [instr_val v, .LOCAL_TEE x] := by simp
  rw [cfg_eq, hlist] at hwf ⊢
  obtain ⟨hs, hi⟩ := wf_redex hwf
  have hwv : wf_val v := by
    have := hi (instr_val v) (by simp)
    cases v <;> cases this <;> constructor <;> assumption
  have hwset : wf_instr (.LOCAL_SET x) := by
    have := hi (.LOCAL_TEE x) (by simp)
    cases this; constructor; assumption
  have hp : Step_pure [instr_val v, .LOCAL_TEE x] [instr_val v, instr_val v, .LOCAL_SET x] :=
    .local_tee v x hwv (hi _ (by simp)) hwset
  have hwft : wf_config (.mk_config z [instr_val v, instr_val v, .LOCAL_SET x]) :=
    wf_config_iff.mpr ⟨hs, by simp [wf_instr_of_wf_val hwv, hwset]⟩
  refine .step _ ⟨_, Step.under vs.reverse
    (Step.pure z _ _ hp (wf_config_iff.mpr ⟨hs, hi⟩) hwft) hwf⟩ ?_
  intro c' hs'
  have hs'' : Step (.mk_config z ((vs.reverse ++ [v]).map instr_val ++ [.LOCAL_TEE x])) c' := by
    simpa using hs'
  obtain ⟨ws₁, ws₂, L'', hsplit, hp', rfl⟩ := Step.redex_pure rfl hs''
  obtain ⟨w, rfl, rfl⟩ := Step_pure.local_tee_redex hp'
  obtain ⟨rfl, rfl⟩ := split_one hsplit
  have hwf' : wf_config (cfg z (v :: v :: vs) [.LOCAL_SET x]) := by
    have := Step.wf_target hs'
    simpa [cfg_eq] using this
  have := h hwf'
  simpa [cfg_eq] using this

end SpecTecWP
