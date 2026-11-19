import SpecTecWP.Exits

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

/-- A partial function is defined on its domain: `$zsize(I32) = 32`. -/
example : zsize .I32 = some 32 := rfl

/-- `$funcsxa` keeps every function address: its `otherwise` clause applies only to an
external address that is not a function. -/
theorem not_funcsxa_skip : ¬ fun_funcsxa [.FUNC 5] [] := by
  intro h
  generalize hx : ([.FUNC 5] : List externaddr) = xs at h
  generalize hy : ([] : List funcaddr) = ys at h
  cases h with
  | fun_funcsxa_case_0 => simp at hx
  | fun_funcsxa_case_1 a xa var_0 _ => simp at hy
  | fun_funcsxa_case_2 v xa var_0 hneg _ =>
    simp only [List.singleton_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact hneg (.fun_funcsxa_case_1 5 [] [])

/-! The hand-written integer operations on concrete values (WebAssembly 3.0, 4.3). -/
example : iclz_ 32 (.mk_uN 1) = .mk_uN 31 := by decide
example : ishr_ 32 .S (.mk_uN 0xFFFFFFF0) (.mk_uN 4) = .mk_uN 0xFFFFFFFF := by decide
example : ishr_ 32 .U (.mk_uN 0xFFFFFFF0) (.mk_uN 36) = .mk_uN 0x0FFFFFFF := by decide
example : ilt_ 32 .S (.mk_uN 0xFFFFFFFF) (.mk_uN 0) = .mk_uN 1 := by decide
example : ilt_ 32 .U (.mk_uN 0xFFFFFFFF) (.mk_uN 0) = .mk_uN 0 := by decide
example : wrap__ 64 32 (.mk_uN 0x100000005) = .mk_uN 5 := by decide
example : extend__ 8 32 .S (.mk_uN 0x80) = .mk_uN 0xFFFFFF80 := by decide
example : iadd_sat_ 8 .S (.mk_uN 0x7F) (.mk_uN 1) = .mk_uN 0x7F := by decide
example : truncz (-7/2) = -3 := by unfold truncz Builtins.truncz; decide +kernel
example : ibytes_ 32 (.mk_uN 0x01020304) = [.mk_byte 4, .mk_byte 3, .mk_byte 2, .mk_byte 1] := by
  decide

/-- An unsigned remainder by zero has no result, so `i32.rem_u` traps: the second clause of
`$irem_` divides by `i_2`, which is undefined at `0`. -/
theorem not_irem_by_zero : ¬ fun_irem_ 32 .U (.mk_uN 5) (.mk_uN 0) (some (.mk_uN 5)) := by
  intro h
  generalize hr : (some (.mk_uN 5) : Option iN) = r at h
  cases h with
  | fun_irem__case_0 => simp at hr
  | fun_irem__case_1 =>
    simp only [proj_uN_0] at *
    exact absurd rfl ‹Rat.ofInt (Int.ofNat 0) ≠ 0›

/-! ## Out-of-bounds `store` -/

section Store

open SpecTecWP

/-- A step of `vals ++ [STORE nt none x ao]` traps on the top two values, or writes the
memory within its bounds. -/
theorem Step.redex_store_aux {c c' : config} (h : Step c c') :
    ∀ (z : state) (ws : List val) (nt : numtype) (x : idx) (ao : memarg),
      c = .mk_config z (ws.map instr_val ++ [.STORE nt none x ao]) →
      (∃ ws₁ a b, ws = ws₁ ++ [a, b] ∧ c' = .mk_config z (ws₁.map instr_val ++ [.TRAP])) ∨
      (∃ z' L n, c' = .mk_config z' L ∧
        n + Int.toNat (Rat.floor (Rat.ofInt (Int.ofNat (size nt)) / Rat.ofInt (Int.ofNat 8))) ≤
          (((sof z).MEMS)[(((fof z).MODULE).MEMS)[proj_uN_0 x]!]!).BYTES.length) := by
  induction h
  case pure z₀ L L' hp _ _ =>
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hL : ws.map instr_val ++ [.STORE nt none x ao] = L₀ at hp
    cases hp <;> list_contra hL
  case read z₀ L L' hr _ _ =>
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exfalso
    generalize hcfg : config.mk_config z₀ (ws.map instr_val ++ [.STORE nt none x ao]) = c at hr
    cases hr
    all_goals
      simp only [config.mk_config.injEq] at hcfg
      obtain ⟨-, hcfg⟩ := hcfg
      list_contra hcfg
  case ctxt_instrs z₀ vals L₀ L₁ z' L₀' hinner _ _ _ _ _ ih =>
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨ws₂, rfl, rfl, rfl⟩ := ctxt_split rfl hc hinner
    rcases ih z₀ ws₂ nt x ao rfl with ⟨ws₁, a, b, rfl, heq⟩ | ⟨z'', L, n, heq, hle⟩
    · simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact .inl ⟨vals ++ ws₁, a, b, by simp, by simp⟩
    · simp only [config.mk_config.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact .inr ⟨_, _, n, rfl, hle⟩
  case store_num_oob =>
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hL⟩ := hc
    have hlen := congrArg List.length hL
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen
    match ws, hlen with
    | [a, b], _ => exact .inl ⟨[], a, b, rfl, rfl⟩
  case store_num_val =>
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨rfl, hL⟩ := hc
    have hlast := congrArg List.getLast? hL
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, Option.some.injEq, instr.STORE.injEq, true_and] at hlast
    obtain ⟨rfl, rfl, rfl⟩ := hlast
    exact .inr ⟨_, _, _, rfl, ‹_ + _ ≤ _›⟩
  all_goals
    intro z ws nt x ao hc
    simp only [config.mk_config.injEq] at hc
    obtain ⟨-, hc⟩ := hc
    exfalso
    list_contra hc

def mem0 : meminst := { TYPE := .PAGE .I32 (.mk_limits (.mk_uN 0) none), BYTES := [] }
def z0 : state :=
  .mk_state { (default : store) with MEMS := [mem0] }
    { LOCALS := [], MODULE := { (default : moduleinst) with MEMS := [0] } }
def i0 : num_ := .mk_num__0 .I32 (.mk_uN 0)
def ao0 : memarg := { ALIGN := .mk_uN 0, OFFSET := .mk_uN 0 }

/-- `i32.store` of `0` at address `0` into an empty memory traps: it has no other
successor. Before the definedness premises of `$with_mem`, it also stepped to a state whose
memory had grown to four bytes. -/
theorem oob_store_traps (c' : config)
    (h : Step (.mk_config z0 [.CONST .I32 i0, .CONST .I32 i0, .STORE .I32 none (.mk_uN 0) ao0]) c') :
    c' = .mk_config z0 [.TRAP] := by
  rcases Step.redex_store_aux h z0 [.CONST .I32 i0, .CONST .I32 i0] .I32 (.mk_uN 0) ao0 rfl with
    ⟨ws₁, a, b, hws, rfl⟩ | ⟨z', L, n, -, hle⟩
  · have hlen := congrArg List.length hws
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    obtain rfl : ws₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    rfl
  · have e : Int.toNat (Rat.floor (Rat.ofInt (Int.ofNat (size .I32)) / Rat.ofInt (Int.ofNat 8))) = 4 := by
      decide +kernel
    rw [e] at hle
    have : (((sof z0).MEMS)[(((fof z0).MODULE).MEMS)[proj_uN_0 (uN.mk_uN 0)]!]!).BYTES.length = 0 := rfl
    omega

end Store

/-! ## Well-formedness of `list(X)`

`syntax list(syntax X) = X* -- if |X*| < 2^32` has a premise and well-formed elements. A
`rectype` is a `list(subtype)`, so a `rectype` whose subtype refers to type index `2^32` is not
well formed. Before the well-formedness predicates looked into `list(X)`, `rectype` had no
predicate at all. -/

theorem rectype_checks_elements :
    ¬ wf_rectype (.REC (.mk_list [.SUB none [._IDX (.mk_uN (2 ^ 32))] (.STRUCT (.mk_list []))])) := by
  intro h
  cases h
  rename_i hall
  have hs := hall (.SUB none [._IDX (.mk_uN (2 ^ 32))] (.STRUCT (.mk_list []))) (by simp [proj_list_0])
  cases hs
  rename_i hts _
  have ht := hts (._IDX (.mk_uN (2 ^ 32))) (by simp)
  cases ht
  rename_i hw
  cases hw
  simp_all

end SpecTecWP.Regression
