import SpecTecWP.Wasm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

@[simp, grind =] theorem wf_uN_mk_iff (N i : Nat) : wf_uN N (.mk_uN i) ↔ i < 2 ^ N := by
  have := Nat.two_pow_pos N
  constructor
  · intro h; cases h; generalize 2 ^ N = p at *; simp only [Int.ofNat_eq_natCast] at *; omega
  · intro h; exact .uN_case_0 _ _ ⟨by omega, by generalize 2 ^ N = p at *; simp only [Int.ofNat_eq_natCast] at *; omega⟩
      (by generalize 2 ^ N = p at *; simp only [Int.ofNat_eq_natCast] at *; omega)

@[simp, grind .] theorem mod_two_pow_lt (x N : Nat) : x % 2 ^ N < 2 ^ N := Nat.mod_lt _ (Nat.two_pow_pos N)

@[grind .] theorem bool_le_one (b : Bool) : Builtins.bool b ≤ 1 := by
  cases b <;> simp [Builtins.bool]

@[grind .] theorem tmod_lt_of_nonneg (a p : Int) (hp : 0 < p) (ha : 0 ≤ a) : Int.tmod a p < p := by
  rw [Int.tmod_eq_emod_of_nonneg ha]; exact Int.emod_lt_of_pos a hp

@[grind .] theorem tmod_nonneg_of_nonneg (a p : Int) (hp : 0 < p) (ha : 0 ≤ a) : 0 ≤ Int.tmod a p := by
  rw [Int.tmod_eq_emod_of_nonneg ha]; exact Int.emod_nonneg a (by omega)

/-- Closes a goal `wf_T x` once the function relations among the hypotheses are taken apart. -/
macro "wf_tac" : tactic => `(tactic| (
  subst_vars
  first
    | (simp_all [Forall]; done)
    | (simp_all [Forall] <;> grind [Forall])
    | grind [Forall]
    | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

attribute [grind cases] wf_arrayinst wf_binop_ wf_bit wf_blocktype wf_bshape wf_byte wf_callframe wf_catch wf_char wf_comptype wf_config wf_context wf_cvtop__ wf_cvtop__Fnn_1_Fnn_2 wf_cvtop__Fnn_1_Inn_2 wf_cvtop__Inn_1_Fnn_2 wf_cvtop__Inn_1_Inn_2 wf_data wf_datainst wf_datamode wf_decl wf_deftype wf_dim wf_elem wf_eleminst wf_elemmode wf_exninst wf_export wf_exportinst wf_externidx wf_externtype wf_fN wf_fNmag wf_fieldtype wf_fieldval wf_frame wf_free wf_func wf_funccode wf_funcinst wf_global wf_globalinst wf_globaltype wf_heaptype wf_idctxt wf_import wf_instr wf_instrtype wf_ishape wf_label wf_lane_ wf_limits wf_lit_ wf_loadop_ wf_loadop_Inn wf_local wf_localtype wf_mem wf_memarg wf_meminst wf_memtype wf_module wf_moduleinst wf_moduletype wf_name wf_nonfuncs wf_num wf_num_ wf_oktypeidx wf_packval wf_rectype wf_ref wf_reftype wf_relaxed2 wf_relaxed4 wf_relop_ wf_result wf_sN wf_shape wf_start wf_state wf_storagetype wf_store wf_storeop_ wf_storeop_Inn wf_structinst wf_subtype wf_symdots wf_sz wf_table wf_tableinst wf_tabletype wf_tag wf_taginst wf_testop_ wf_type wf_typeuse wf_typevar wf_uN wf_unop_ wf_unop_Inn wf_val wf_valtype wf_vbinop_ wf_vbinop_Jnn_M wf_vcvtop__ wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 wf_vcvtop__Fnn_1_M_1_Inn_2_M_2 wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 wf_vec wf_vextbinop__ wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 wf_vextternop__ wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 wf_vextunop__ wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 wf_vloadop_ wf_vrelop_ wf_vrelop_Jnn_M wf_vshiftop_ wf_vswizzlop_ wf_vternop_ wf_vtestop_ wf_vunop_ wf_vunop_Jnn_M
attribute [grind intro] wf_arrayinst wf_binop_ wf_bit wf_blocktype wf_bshape wf_byte wf_callframe wf_catch wf_char wf_comptype wf_config wf_context wf_cvtop__ wf_cvtop__Fnn_1_Fnn_2 wf_cvtop__Fnn_1_Inn_2 wf_cvtop__Inn_1_Fnn_2 wf_cvtop__Inn_1_Inn_2 wf_data wf_datainst wf_datamode wf_decl wf_deftype wf_dim wf_elem wf_eleminst wf_elemmode wf_exninst wf_export wf_exportinst wf_externidx wf_externtype wf_fN wf_fNmag wf_fieldtype wf_fieldval wf_frame wf_free wf_func wf_funccode wf_funcinst wf_global wf_globalinst wf_globaltype wf_heaptype wf_idctxt wf_import wf_instr wf_instrtype wf_ishape wf_label wf_lane_ wf_limits wf_lit_ wf_loadop_ wf_loadop_Inn wf_local wf_localtype wf_mem wf_memarg wf_meminst wf_memtype wf_module wf_moduleinst wf_moduletype wf_name wf_nonfuncs wf_num wf_num_ wf_oktypeidx wf_packval wf_rectype wf_ref wf_reftype wf_relaxed2 wf_relaxed4 wf_relop_ wf_result wf_sN wf_shape wf_start wf_state wf_storagetype wf_store wf_storeop_ wf_storeop_Inn wf_structinst wf_subtype wf_symdots wf_sz wf_table wf_tableinst wf_tabletype wf_tag wf_taginst wf_testop_ wf_type wf_typeuse wf_typevar wf_uN wf_unop_ wf_unop_Inn wf_val wf_valtype wf_vbinop_ wf_vbinop_Jnn_M wf_vcvtop__ wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 wf_vcvtop__Fnn_1_M_1_Inn_2_M_2 wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 wf_vec wf_vextbinop__ wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 wf_vextternop__ wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 wf_vextunop__ wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 wf_vloadop_ wf_vrelop_ wf_vrelop_Jnn_M wf_vshiftop_ wf_vswizzlop_ wf_vternop_ wf_vtestop_ wf_vunop_ wf_vunop_Jnn_M

def fnat_is_wf : Prop :=
  ∀ (v_N : N) (nat : Nat) (ret_val : fN), (ret_val = (fnat v_N nat)) →
    (wf_fN v_N ret_val)

@[grind]
theorem funcsxx_is_wf :
    ∀ (var_0_lst : (List externidx)) (ret_val_lst : (List typeidx)) (var_0 : (List typeidx)), (fun_funcsxx var_0_lst var_0) →
    Forall (fun (var_0 : externidx) => (wf_externidx var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : typeidx) => (wf_uN 32 ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem globalsxx_is_wf :
    ∀ (var_0_lst : (List externidx)) (ret_val_lst : (List globalidx)) (var_0 : (List globalidx)), (fun_globalsxx var_0_lst var_0) →
    Forall (fun (var_0 : externidx) => (wf_externidx var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : globalidx) => (wf_uN 32 ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem tablesxx_is_wf :
    ∀ (var_0_lst : (List externidx)) (ret_val_lst : (List tableidx)) (var_0 : (List tableidx)), (fun_tablesxx var_0_lst var_0) →
    Forall (fun (var_0 : externidx) => (wf_externidx var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : tableidx) => (wf_uN 32 ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem memsxx_is_wf :
    ∀ (var_0_lst : (List externidx)) (ret_val_lst : (List memidx)) (var_0 : (List memidx)), (fun_memsxx var_0_lst var_0) →
    Forall (fun (var_0 : externidx) => (wf_externidx var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : memidx) => (wf_uN 32 ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem tagsxx_is_wf :
    ∀ (var_0_lst : (List externidx)) (ret_val_lst : (List tagidx)) (var_0 : (List tagidx)), (fun_tagsxx var_0_lst var_0) →
    Forall (fun (var_0 : externidx) => (wf_externidx var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : tagidx) => (wf_uN 32 ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind ←]
theorem wf_free_append (a b : free) (ha : wf_free a) (hb : wf_free b) :
    wf_free (a ++ b) := by
  rw [show a ++ b = _append_free a b from rfl]
  cases ha; cases hb
  constructor <;> simp_all [Forall, _append_free] <;> (rintro x (h | h) <;> simp_all)

@[grind]
theorem free_opt_is_wf :
    ∀ (var_0_opt : (Option free)) (ret_val : free), Forall (fun (var_0 : free) => (wf_free var_0)) (Option.toList var_0_opt) →
    (ret_val = (free_opt var_0_opt)) →
    (wf_free ret_val) := by
  intro var_0_opt ret_val h0 h1
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_opt]; done) | (simp_all [Forall, free_opt] <;> grind [Forall, free_opt]) | grind [Forall, free_opt] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_opt]; done) | omega | decide); done))

@[grind]
theorem free_list_is_wf :
    ∀ (var_0_lst : (List free)) (ret_val : free) (var_0 : free), (fun_free_list var_0_lst var_0) →
    Forall (fun (var_0 : free) => (wf_free var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_free ret_val) := by
  intro var_0_lst ret_val var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem free_typeidx_is_wf :
    ∀ (v_typeidx : typeidx) (ret_val : free), (wf_uN 32 v_typeidx) →
    (ret_val = (free_typeidx v_typeidx)) →
    (wf_free ret_val) := by
  intro v_typeidx ret_val h0 h1
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_typeidx]; done) | (simp_all [Forall, free_typeidx] <;> grind [Forall, free_typeidx]) | grind [Forall, free_typeidx] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_typeidx]; done) | omega | decide); done))

def free_funcidx_is_wf : Prop :=
  ∀ (v_funcidx : funcidx) (ret_val : free), (wf_uN 32 v_funcidx) →
    (ret_val = (free_funcidx v_funcidx)) →
    (wf_free ret_val)

def free_globalidx_is_wf : Prop :=
  ∀ (v_globalidx : globalidx) (ret_val : free), (wf_uN 32 v_globalidx) →
    (ret_val = (free_globalidx v_globalidx)) →
    (wf_free ret_val)

def free_tableidx_is_wf : Prop :=
  ∀ (v_tableidx : tableidx) (ret_val : free), (wf_uN 32 v_tableidx) →
    (ret_val = (free_tableidx v_tableidx)) →
    (wf_free ret_val)

def free_memidx_is_wf : Prop :=
  ∀ (v_memidx : memidx) (ret_val : free), (wf_uN 32 v_memidx) →
    (ret_val = (free_memidx v_memidx)) →
    (wf_free ret_val)

def free_elemidx_is_wf : Prop :=
  ∀ (v_elemidx : elemidx) (ret_val : free), (wf_uN 32 v_elemidx) →
    (ret_val = (free_elemidx v_elemidx)) →
    (wf_free ret_val)

def free_dataidx_is_wf : Prop :=
  ∀ (v_dataidx : dataidx) (ret_val : free), (wf_uN 32 v_dataidx) →
    (ret_val = (free_dataidx v_dataidx)) →
    (wf_free ret_val)

def free_localidx_is_wf : Prop :=
  ∀ (v_localidx : localidx) (ret_val : free), (wf_uN 32 v_localidx) →
    (ret_val = (free_localidx v_localidx)) →
    (wf_free ret_val)

def free_labelidx_is_wf : Prop :=
  ∀ (v_labelidx : labelidx) (ret_val : free), (wf_uN 32 v_labelidx) →
    (ret_val = (free_labelidx v_labelidx)) →
    (wf_free ret_val)

def free_tagidx_is_wf : Prop :=
  ∀ (v_tagidx : tagidx) (ret_val : free), (wf_uN 32 v_tagidx) →
    (ret_val = (free_tagidx v_tagidx)) →
    (wf_free ret_val)

def free_externidx_is_wf : Prop :=
  ∀ (v_externidx : externidx) (ret_val : free), (wf_externidx v_externidx) →
    (ret_val = (free_externidx v_externidx)) →
    (wf_free ret_val)

def ANYREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (ANYREF )) →
    (wf_reftype ret_val)

def EQREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (EQREF )) →
    (wf_reftype ret_val)

def I31REF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (I31REF )) →
    (wf_reftype ret_val)

def STRUCTREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (STRUCTREF )) →
    (wf_reftype ret_val)

def ARRAYREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (ARRAYREF )) →
    (wf_reftype ret_val)

def FUNCREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (FUNCREF )) →
    (wf_reftype ret_val)

def EXNREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (EXNREF )) →
    (wf_reftype ret_val)

def EXTERNREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (EXTERNREF )) →
    (wf_reftype ret_val)

def NULLREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (NULLREF )) →
    (wf_reftype ret_val)

def NULLFUNCREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (NULLFUNCREF )) →
    (wf_reftype ret_val)

def NULLEXNREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (NULLEXNREF )) →
    (wf_reftype ret_val)

def NULLEXTERNREF_is_wf : Prop :=
  ∀ (ret_val : reftype), (ret_val = (NULLEXTERNREF )) →
    (wf_reftype ret_val)

def unpack_is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (ret_val : valtype), (wf_storagetype v_storagetype) →
    (ret_val = (unpack v_storagetype)) →
    (wf_valtype ret_val)

def diffrt_is_wf : Prop :=
  ∀ (v_reftype : reftype) (reftype_0 : reftype) (ret_val : reftype), (wf_reftype v_reftype) →
    (wf_reftype reftype_0) →
    (ret_val = (diffrt v_reftype reftype_0)) →
    (wf_reftype ret_val)

def tagsxt_is_wf : Prop :=
  ∀ (var_0_lst : (List externtype)) (ret_val_lst : (List tagtype)) (var_0 : (List tagtype)), (fun_tagsxt var_0_lst var_0) →
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : tagtype) => (wf_typeuse ret_val)) ret_val_lst

def globalsxt_is_wf : Prop :=
  ∀ (var_0_lst : (List externtype)) (ret_val_lst : (List globaltype)) (var_0 : (List globaltype)), (fun_globalsxt var_0_lst var_0) →
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : globaltype) => (wf_globaltype ret_val)) ret_val_lst

def memsxt_is_wf : Prop :=
  ∀ (var_0_lst : (List externtype)) (ret_val_lst : (List memtype)) (var_0 : (List memtype)), (fun_memsxt var_0_lst var_0) →
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : memtype) => (wf_memtype ret_val)) ret_val_lst

def tablesxt_is_wf : Prop :=
  ∀ (var_0_lst : (List externtype)) (ret_val_lst : (List tabletype)) (var_0 : (List tabletype)), (fun_tablesxt var_0_lst var_0) →
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : tabletype) => (wf_tabletype ret_val)) ret_val_lst

def subst_typevar_is_wf : Prop :=
  ∀ (v_typevar : typevar) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : typeuse) (var_0 : (Option typeuse)), (fun_subst_typevar v_typevar var_0_lst var_1_lst var_0) →
    (wf_typevar v_typevar) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_typeuse ret_val)

def minus_recs_is_wf : Prop :=
  ∀ (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : ((List typevar) × (List typeuse))), Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    ((minus_recs var_0_lst var_1_lst) ≠ none) →
    (ret_val = (Option.get! (minus_recs var_0_lst var_1_lst))) →
    Forall (fun (iter : typevar) => (wf_typevar iter)) (Prod.fst ret_val) →
    Forall (fun (iter : typeuse) => (wf_typeuse iter)) (Prod.snd ret_val)

def subst_typeuse_is_wf : Prop :=
  ∀ (v_typeuse : typeuse) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : typeuse) (var_0 : typeuse), (fun_subst_typeuse v_typeuse var_0_lst var_1_lst var_0) →
    (wf_typeuse v_typeuse) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_typeuse ret_val)

def subst_heaptype_is_wf : Prop :=
  ∀ (v_heaptype : heaptype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : heaptype) (var_0 : heaptype), (fun_subst_heaptype v_heaptype var_0_lst var_1_lst var_0) →
    (wf_heaptype v_heaptype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_heaptype ret_val)

def subst_reftype_is_wf : Prop :=
  ∀ (v_reftype : reftype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : reftype) (var_0 : reftype), (fun_subst_reftype v_reftype var_0_lst var_1_lst var_0) →
    (wf_reftype v_reftype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_reftype ret_val)

def subst_valtype_is_wf : Prop :=
  ∀ (v_valtype : valtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : valtype) (var_0 : valtype), (fun_subst_valtype v_valtype var_0_lst var_1_lst var_0) →
    (wf_valtype v_valtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_valtype ret_val)

def subst_storagetype_is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : storagetype) (var_0 : storagetype), (fun_subst_storagetype v_storagetype var_0_lst var_1_lst var_0) →
    (wf_storagetype v_storagetype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_storagetype ret_val)

def subst_fieldtype_is_wf : Prop :=
  ∀ (v_fieldtype : fieldtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : fieldtype) (var_0 : fieldtype), (fun_subst_fieldtype v_fieldtype var_0_lst var_1_lst var_0) →
    (wf_fieldtype v_fieldtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_fieldtype ret_val)

def subst_comptype_is_wf : Prop :=
  ∀ (v_comptype : comptype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : comptype) (var_0 : comptype), (fun_subst_comptype v_comptype var_0_lst var_1_lst var_0) →
    (wf_comptype v_comptype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_comptype ret_val)

def subst_subtype_is_wf : Prop :=
  ∀ (v_subtype : subtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : subtype) (var_0 : subtype), (fun_subst_subtype v_subtype var_0_lst var_1_lst var_0) →
    (wf_subtype v_subtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_subtype ret_val)

def subst_tagtype_is_wf : Prop :=
  ∀ (v_tagtype : tagtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : tagtype) (var_0 : tagtype), (fun_subst_tagtype v_tagtype var_0_lst var_1_lst var_0) →
    (wf_typeuse v_tagtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_typeuse ret_val)

def subst_globaltype_is_wf : Prop :=
  ∀ (v_globaltype : globaltype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : globaltype) (var_0 : globaltype), (fun_subst_globaltype v_globaltype var_0_lst var_1_lst var_0) →
    (wf_globaltype v_globaltype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_globaltype ret_val)

def subst_memtype_is_wf : Prop :=
  ∀ (v_memtype : memtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : memtype), (wf_memtype v_memtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = (subst_memtype v_memtype var_0_lst var_1_lst)) →
    (wf_memtype ret_val)

def subst_tabletype_is_wf : Prop :=
  ∀ (v_tabletype : tabletype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : tabletype) (var_0 : tabletype), (fun_subst_tabletype v_tabletype var_0_lst var_1_lst var_0) →
    (wf_tabletype v_tabletype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_tabletype ret_val)

def subst_externtype_is_wf : Prop :=
  ∀ (v_externtype : externtype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : externtype) (var_0 : externtype), (fun_subst_externtype v_externtype var_0_lst var_1_lst var_0) →
    (wf_externtype v_externtype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_externtype ret_val)

def subst_moduletype_is_wf : Prop :=
  ∀ (v_moduletype : moduletype) (var_0_lst : (List typevar)) (var_1_lst : (List typeuse)) (ret_val : moduletype) (var_0 : moduletype), (fun_subst_moduletype v_moduletype var_0_lst var_1_lst var_0) →
    (wf_moduletype v_moduletype) →
    Forall (fun (var_0 : typevar) => (wf_typevar var_0)) var_0_lst →
    Forall (fun (var_1 : typeuse) => (wf_typeuse var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_moduletype ret_val)

def subst_all_valtype_is_wf : Prop :=
  ∀ (v_valtype : valtype) (var_0_lst : (List typeuse)) (ret_val : valtype) (var_0 : valtype), (fun_subst_all_valtype v_valtype var_0_lst var_0) →
    (wf_valtype v_valtype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_valtype ret_val)

def subst_all_reftype_is_wf : Prop :=
  ∀ (v_reftype : reftype) (var_0_lst : (List typeuse)) (ret_val : reftype) (var_0 : reftype), (fun_subst_all_reftype v_reftype var_0_lst var_0) →
    (wf_reftype v_reftype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_reftype ret_val)

def subst_all_tagtype_is_wf : Prop :=
  ∀ (v_tagtype : tagtype) (var_0_lst : (List typeuse)) (ret_val : tagtype) (var_0 : tagtype), (fun_subst_all_tagtype v_tagtype var_0_lst var_0) →
    (wf_typeuse v_tagtype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_typeuse ret_val)

def subst_all_globaltype_is_wf : Prop :=
  ∀ (v_globaltype : globaltype) (var_0_lst : (List typeuse)) (ret_val : globaltype) (var_0 : globaltype), (fun_subst_all_globaltype v_globaltype var_0_lst var_0) →
    (wf_globaltype v_globaltype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_globaltype ret_val)

def subst_all_memtype_is_wf : Prop :=
  ∀ (v_memtype : memtype) (var_0_lst : (List typeuse)) (ret_val : memtype) (var_0 : memtype), (fun_subst_all_memtype v_memtype var_0_lst var_0) →
    (wf_memtype v_memtype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_memtype ret_val)

def subst_all_tabletype_is_wf : Prop :=
  ∀ (v_tabletype : tabletype) (var_0_lst : (List typeuse)) (ret_val : tabletype) (var_0 : tabletype), (fun_subst_all_tabletype v_tabletype var_0_lst var_0) →
    (wf_tabletype v_tabletype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_tabletype ret_val)

def subst_all_externtype_is_wf : Prop :=
  ∀ (v_externtype : externtype) (var_0_lst : (List typeuse)) (ret_val : externtype) (var_0 : externtype), (fun_subst_all_externtype v_externtype var_0_lst var_0) →
    (wf_externtype v_externtype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_externtype ret_val)

def subst_all_moduletype_is_wf : Prop :=
  ∀ (v_moduletype : moduletype) (var_0_lst : (List typeuse)) (ret_val : moduletype) (var_0 : moduletype), (fun_subst_all_moduletype v_moduletype var_0_lst var_0) →
    (wf_moduletype v_moduletype) →
    Forall (fun (var_0 : typeuse) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_moduletype ret_val)

def unrolldt_is_wf : Prop :=
  ∀ (v_deftype : deftype) (ret_val : subtype) (var_0 : subtype), (fun_unrolldt v_deftype var_0) →
    (wf_deftype v_deftype) →
    (ret_val = var_0) →
    (wf_subtype ret_val)

@[grind]
theorem free_addrtype_is_wf :
    ∀ (v_addrtype : addrtype) (ret_val : free), (ret_val = (free_addrtype v_addrtype)) →
    (wf_free ret_val) := by
  intro v_addrtype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_addrtype]; done) | (simp_all [Forall, free_addrtype] <;> grind [Forall, free_addrtype]) | grind [Forall, free_addrtype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_addrtype]; done) | omega | decide); done))

@[grind]
theorem free_numtype_is_wf :
    ∀ (v_numtype : numtype) (ret_val : free), (ret_val = (free_numtype v_numtype)) →
    (wf_free ret_val) := by
  intro v_numtype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_numtype]; done) | (simp_all [Forall, free_numtype] <;> grind [Forall, free_numtype]) | grind [Forall, free_numtype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_numtype]; done) | omega | decide); done))

@[grind]
theorem free_packtype_is_wf :
    ∀ (v_packtype : packtype) (ret_val : free), (ret_val = (free_packtype v_packtype)) →
    (wf_free ret_val) := by
  intro v_packtype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_packtype]; done) | (simp_all [Forall, free_packtype] <;> grind [Forall, free_packtype]) | grind [Forall, free_packtype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_packtype]; done) | omega | decide); done))

@[grind]
theorem free_lanetype_is_wf :
    ∀ (v_lanetype : lanetype) (ret_val : free), (ret_val = (free_lanetype v_lanetype)) →
    (wf_free ret_val) := by
  intro v_lanetype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_lanetype]; done) | (simp_all [Forall, free_lanetype] <;> grind [Forall, free_lanetype]) | grind [Forall, free_lanetype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_lanetype]; done) | omega | decide); done))

@[grind]
theorem free_vectype_is_wf :
    ∀ (v_vectype : vectype) (ret_val : free), (ret_val = (free_vectype v_vectype)) →
    (wf_free ret_val) := by
  intro v_vectype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_vectype]; done) | (simp_all [Forall, free_vectype] <;> grind [Forall, free_vectype]) | grind [Forall, free_vectype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_vectype]; done) | omega | decide); done))

@[grind]
theorem free_consttype_is_wf :
    ∀ (v_consttype : consttype) (ret_val : free), (ret_val = (free_consttype v_consttype)) →
    (wf_free ret_val) := by
  intro v_consttype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_consttype]; done) | (simp_all [Forall, free_consttype] <;> grind [Forall, free_consttype]) | grind [Forall, free_consttype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_consttype]; done) | omega | decide); done))

@[grind]
theorem free_absheaptype_is_wf :
    ∀ (v_absheaptype : absheaptype) (ret_val : free), (ret_val = (free_absheaptype v_absheaptype)) →
    (wf_free ret_val) := by
  intro v_absheaptype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_absheaptype]; done) | (simp_all [Forall, free_absheaptype] <;> grind [Forall, free_absheaptype]) | grind [Forall, free_absheaptype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_absheaptype]; done) | omega | decide); done))

@[grind]
theorem free_typevar_is_wf :
    ∀ (v_typevar : typevar) (ret_val : free), (wf_typevar v_typevar) →
    (ret_val = (free_typevar v_typevar)) →
    (wf_free ret_val) := by
  intro v_typevar ret_val h0 h1
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_typevar]; done) | (simp_all [Forall, free_typevar] <;> grind [Forall, free_typevar]) | grind [Forall, free_typevar] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_typevar]; done) | omega | decide); done))

def free_heaptype_is_wf : Prop :=
  ∀ (v_heaptype : heaptype) (ret_val : free) (var_0 : free), (fun_free_heaptype v_heaptype var_0) →
    (wf_heaptype v_heaptype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_reftype_is_wf : Prop :=
  ∀ (v_reftype : reftype) (ret_val : free) (var_0 : free), (fun_free_reftype v_reftype var_0) →
    (wf_reftype v_reftype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_typeuse_is_wf : Prop :=
  ∀ (v_typeuse : typeuse) (ret_val : free) (var_0 : free), (fun_free_typeuse v_typeuse var_0) →
    (wf_typeuse v_typeuse) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_valtype_is_wf : Prop :=
  ∀ (v_valtype : valtype) (ret_val : free) (var_0 : free), (fun_free_valtype v_valtype var_0) →
    (wf_valtype v_valtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_resulttype_is_wf : Prop :=
  ∀ (v_resulttype : resulttype) (ret_val : free) (var_0 : free), (fun_free_resulttype v_resulttype var_0) →
    ((List.length (List.map (fun (X_17398 : valtype) => X_17398) (proj_list_0 valtype v_resulttype))) < (2 ^ 32)) →
    Forall (fun (iter : valtype) => (wf_valtype iter)) (proj_list_0 valtype v_resulttype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_storagetype_is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (ret_val : free) (var_0 : free), (fun_free_storagetype v_storagetype var_0) →
    (wf_storagetype v_storagetype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_fieldtype_is_wf : Prop :=
  ∀ (v_fieldtype : fieldtype) (ret_val : free) (var_0 : free), (fun_free_fieldtype v_fieldtype var_0) →
    (wf_fieldtype v_fieldtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_comptype_is_wf : Prop :=
  ∀ (v_comptype : comptype) (ret_val : free) (var_0 : free), (fun_free_comptype v_comptype var_0) →
    (wf_comptype v_comptype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_subtype_is_wf : Prop :=
  ∀ (v_subtype : subtype) (ret_val : free) (var_0 : free), (fun_free_subtype v_subtype var_0) →
    (wf_subtype v_subtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_rectype_is_wf : Prop :=
  ∀ (v_rectype : rectype) (ret_val : free) (var_0 : free), (fun_free_rectype v_rectype var_0) →
    (wf_rectype v_rectype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_deftype_is_wf : Prop :=
  ∀ (v_deftype : deftype) (ret_val : free) (var_0 : free), (fun_free_deftype v_deftype var_0) →
    (wf_deftype v_deftype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_tagtype_is_wf : Prop :=
  ∀ (v_tagtype : tagtype) (ret_val : free) (var_0 : free), (fun_free_tagtype v_tagtype var_0) →
    (wf_typeuse v_tagtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_globaltype_is_wf : Prop :=
  ∀ (v_globaltype : globaltype) (ret_val : free) (var_0 : free), (fun_free_globaltype v_globaltype var_0) →
    (wf_globaltype v_globaltype) →
    (ret_val = var_0) →
    (wf_free ret_val)

@[grind]
theorem free_memtype_is_wf :
    ∀ (v_memtype : memtype) (ret_val : free), (wf_memtype v_memtype) →
    (ret_val = (free_memtype v_memtype)) →
    (wf_free ret_val) := by
  intro v_memtype ret_val h0 h1
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_memtype]; done) | (simp_all [Forall, free_memtype] <;> grind [Forall, free_memtype]) | grind [Forall, free_memtype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_memtype]; done) | omega | decide); done))

def free_tabletype_is_wf : Prop :=
  ∀ (v_tabletype : tabletype) (ret_val : free) (var_0 : free), (fun_free_tabletype v_tabletype var_0) →
    (wf_tabletype v_tabletype) →
    (ret_val = var_0) →
    (wf_free ret_val)

@[grind]
theorem free_datatype_is_wf :
    ∀ (v_datatype : datatype) (ret_val : free), (ret_val = (free_datatype v_datatype)) →
    (wf_free ret_val) := by
  intro v_datatype ret_val h0
  subst_vars
  (subst_vars; first | (simp_all [Forall, free_datatype]; done) | (simp_all [Forall, free_datatype] <;> grind [Forall, free_datatype]) | grind [Forall, free_datatype] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, free_datatype]; done) | omega | decide); done))

def free_elemtype_is_wf : Prop :=
  ∀ (v_elemtype : elemtype) (ret_val : free) (var_0 : free), (fun_free_elemtype v_elemtype var_0) →
    (wf_reftype v_elemtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_externtype_is_wf : Prop :=
  ∀ (v_externtype : externtype) (ret_val : free) (var_0 : free), (fun_free_externtype v_externtype var_0) →
    (wf_externtype v_externtype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_moduletype_is_wf : Prop :=
  ∀ (v_moduletype : moduletype) (ret_val : free) (var_0 : free), (fun_free_moduletype v_moduletype var_0) →
    (wf_moduletype v_moduletype) →
    (ret_val = var_0) →
    (wf_free ret_val)

@[grind]
theorem dim_is_wf :
    ∀ (v_shape : shape) (ret_val : dim), (wf_shape v_shape) →
    (ret_val = (fun_dim v_shape)) →
    (wf_dim ret_val) := by
  intro v_shape ret_val h0 h1
  subst_vars
  (subst_vars; first | (simp_all [Forall, fun_dim]; done) | (simp_all [Forall, fun_dim] <;> grind [Forall, fun_dim]) | grind [Forall, fun_dim] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, fun_dim]; done) | omega | decide); done))

def memarg0_is_wf : Prop :=
  ∀ (ret_val : memarg), (ret_val = (memarg0 )) →
    (wf_memarg ret_val)

def const_is_wf : Prop :=
  ∀ (v_consttype : consttype) (v_lit_ : lit_) (ret_val : instr), (wf_lit_ (storagetype_consttype v_consttype) v_lit_) →
    ((const v_consttype v_lit_) ≠ none) →
    (ret_val = (Option.get! (const v_consttype v_lit_))) →
    (wf_instr ret_val)

def free_shape_is_wf : Prop :=
  ∀ (v_shape : shape) (ret_val : free), (wf_shape v_shape) →
    (ret_val = (free_shape v_shape)) →
    (wf_free ret_val)

def free_blocktype_is_wf : Prop :=
  ∀ (v_blocktype : blocktype) (ret_val : free) (var_0 : free), (fun_free_blocktype v_blocktype var_0) →
    (wf_blocktype v_blocktype) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_catch_is_wf : Prop :=
  ∀ (v_catch : «catch») (ret_val : free), (wf_catch v_catch) →
    (ret_val = (free_catch v_catch)) →
    (wf_free ret_val)

def shift_labelidxs_is_wf : Prop :=
  ∀ (var_0_lst : (List labelidx)) (ret_val_lst : (List labelidx)) (var_0 : (List labelidx)), (fun_shift_labelidxs var_0_lst var_0) →
    Forall (fun (var_0 : labelidx) => (wf_uN 32 var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : labelidx) => (wf_uN 32 ret_val)) ret_val_lst

def free_instr_is_wf : Prop :=
  ∀ (v_instr : instr) (ret_val : free) (var_0 : free), (fun_free_instr v_instr var_0) →
    (wf_instr v_instr) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_block_is_wf : Prop :=
  ∀ (var_0_lst : (List instr)) (ret_val : free) (var_0 : free), (fun_free_block var_0_lst var_0) →
    Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_expr_is_wf : Prop :=
  ∀ (v_expr : expr) (ret_val : free) (var_0 : free), (fun_free_expr v_expr var_0) →
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_type_is_wf : Prop :=
  ∀ (v_type : type) (ret_val : free) (var_0 : free), (fun_free_type v_type var_0) →
    (wf_type v_type) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_tag_is_wf : Prop :=
  ∀ (v_tag : tag) (ret_val : free) (var_0 : free), (fun_free_tag v_tag var_0) →
    (wf_tag v_tag) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_global_is_wf : Prop :=
  ∀ (v_global : global) (ret_val : free) (var_0 : free), (fun_free_global v_global var_0) →
    (wf_global v_global) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_mem_is_wf : Prop :=
  ∀ (v_mem : mem) (ret_val : free), (wf_mem v_mem) →
    (ret_val = (free_mem v_mem)) →
    (wf_free ret_val)

def free_table_is_wf : Prop :=
  ∀ (v_table : table) (ret_val : free) (var_0 : free), (fun_free_table v_table var_0) →
    (wf_table v_table) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_local_is_wf : Prop :=
  ∀ (v_local : «local») (ret_val : free) (var_0 : free), (fun_free_local v_local var_0) →
    (wf_local v_local) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_func_is_wf : Prop :=
  ∀ (v_func : func) (ret_val : free) (var_0 : free), (fun_free_func v_func var_0) →
    (wf_func v_func) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_datamode_is_wf : Prop :=
  ∀ (v_datamode : datamode) (ret_val : free) (var_0 : free), (fun_free_datamode v_datamode var_0) →
    (wf_datamode v_datamode) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_data_is_wf : Prop :=
  ∀ (v_data : data) (ret_val : free) (var_0 : free), (fun_free_data v_data var_0) →
    (wf_data v_data) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_elemmode_is_wf : Prop :=
  ∀ (v_elemmode : elemmode) (ret_val : free) (var_0 : free), (fun_free_elemmode v_elemmode var_0) →
    (wf_elemmode v_elemmode) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_elem_is_wf : Prop :=
  ∀ (v_elem : elem) (ret_val : free) (var_0 : free), (fun_free_elem v_elem var_0) →
    (wf_elem v_elem) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_start_is_wf : Prop :=
  ∀ (v_start : start) (ret_val : free), (wf_start v_start) →
    (ret_val = (free_start v_start)) →
    (wf_free ret_val)

def free_import_is_wf : Prop :=
  ∀ (v_import : «import») (ret_val : free) (var_0 : free), (fun_free_import v_import var_0) →
    (wf_import v_import) →
    (ret_val = var_0) →
    (wf_free ret_val)

def free_export_is_wf : Prop :=
  ∀ (v_export : «export») (ret_val : free), (wf_export v_export) →
    (ret_val = (free_export v_export)) →
    (wf_free ret_val)

def free_module_is_wf : Prop :=
  ∀ (v_module : module) (ret_val : free) (var_0 : free), (fun_free_module v_module var_0) →
    (wf_module v_module) →
    (ret_val = var_0) →
    (wf_free ret_val)

def funcidx_module_is_wf : Prop :=
  ∀ (v_module : module) (ret_val_lst : (List funcidx)) (var_0 : (List funcidx)), (fun_funcidx_module v_module var_0) →
    (wf_module v_module) →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : funcidx) => (wf_uN 32 ret_val)) ret_val_lst

def dataidx_funcs_is_wf : Prop :=
  ∀ (var_0_lst : (List func)) (ret_val_lst : (List dataidx)) (var_0 : (List dataidx)), (fun_dataidx_funcs var_0_lst var_0) →
    Forall (fun (var_0 : func) => (wf_func var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : dataidx) => (wf_uN 32 ret_val)) ret_val_lst

def with_locals_is_wf : Prop :=
  ∀ (v_context : context) (var_0_lst : (List localidx)) (var_1_lst : (List localtype)) (ret_val : context) (var_0 : (Option context)), (fun_with_locals v_context var_0_lst var_1_lst var_0) →
    (wf_context v_context) →
    Forall (fun (var_0 : localidx) => (wf_uN 32 var_0)) var_0_lst →
    Forall (fun (var_1 : localtype) => (wf_localtype var_1)) var_1_lst →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_context ret_val)

def clos_valtype_is_wf : Prop :=
  ∀ (v_context : context) (v_valtype : valtype) (ret_val : valtype) (var_0 : valtype), (fun_clos_valtype v_context v_valtype var_0) →
    (wf_context v_context) →
    (wf_valtype v_valtype) →
    (ret_val = var_0) →
    (wf_valtype ret_val)

def clos_tagtype_is_wf : Prop :=
  ∀ (v_context : context) (v_tagtype : tagtype) (ret_val : tagtype) (var_0 : tagtype), (fun_clos_tagtype v_context v_tagtype var_0) →
    (wf_context v_context) →
    (wf_typeuse v_tagtype) →
    (ret_val = var_0) →
    (wf_typeuse ret_val)

def clos_externtype_is_wf : Prop :=
  ∀ (v_context : context) (v_externtype : externtype) (ret_val : externtype) (var_0 : externtype), (fun_clos_externtype v_context v_externtype var_0) →
    (wf_context v_context) →
    (wf_externtype v_externtype) →
    (ret_val = var_0) →
    (wf_externtype ret_val)

def clos_moduletype_is_wf : Prop :=
  ∀ (v_context : context) (v_moduletype : moduletype) (ret_val : moduletype) (var_0 : moduletype), (fun_clos_moduletype v_context v_moduletype var_0) →
    (wf_context v_context) →
    (wf_moduletype v_moduletype) →
    (ret_val = var_0) →
    (wf_moduletype ret_val)

def unrollht__is_wf : Prop :=
  ∀ (v_context : context) (v_heaptype : heaptype) (ret_val : subtype) (var_0 : subtype), (fun_unrollht_ v_context v_heaptype var_0) →
    (wf_context v_context) →
    (wf_heaptype v_heaptype) →
    (ret_val = var_0) →
    (wf_subtype ret_val)

def default__is_wf : Prop :=
  ∀ (v_valtype : valtype) (ret_val_opt : (Option val)) (var_0 : (Option (Option val))), (fun_default_ v_valtype var_0) →
    (wf_valtype v_valtype) →
    (var_0 ≠ none) →
    (ret_val_opt = (Option.get! var_0)) →
    Forall (fun (ret_val : val) => (wf_val ret_val)) (Option.toList ret_val_opt)

def funcidx_nonfuncs_is_wf : Prop :=
  ∀ (v_nonfuncs : nonfuncs) (ret_val_lst : (List funcidx)) (var_0 : (List funcidx)), (fun_funcidx_nonfuncs v_nonfuncs var_0) →
    (wf_nonfuncs v_nonfuncs) →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : funcidx) => (wf_uN 32 ret_val)) ret_val_lst

def R_fmadd_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_fmadd )) →
    (wf_relaxed2 ret_val)

def R_fmin_is_wf : Prop :=
  ∀ (ret_val : relaxed4), (ret_val = (R_fmin )) →
    (wf_relaxed4 ret_val)

def R_fmax_is_wf : Prop :=
  ∀ (ret_val : relaxed4), (ret_val = (R_fmax )) →
    (wf_relaxed4 ret_val)

def R_idot_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_idot )) →
    (wf_relaxed2 ret_val)

def R_iq15mulr_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_iq15mulr )) →
    (wf_relaxed2 ret_val)

def R_trunc_u_is_wf : Prop :=
  ∀ (ret_val : relaxed4), (ret_val = (R_trunc_u )) →
    (wf_relaxed4 ret_val)

def R_trunc_s_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_trunc_s )) →
    (wf_relaxed2 ret_val)

def R_swizzle_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_swizzle )) →
    (wf_relaxed2 ret_val)

def R_laneselect_is_wf : Prop :=
  ∀ (ret_val : relaxed2), (ret_val = (R_laneselect )) →
    (wf_relaxed2 ret_val)

def s33_to_u32_is_wf : Prop :=
  ∀ (v_s33 : s33) (ret_val : u32), (wf_sN 33 v_s33) →
    (ret_val = (s33_to_u32 v_s33)) →
    (wf_uN 32 ret_val)

def ibits__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val_lst : (List bit)), (wf_uN v_N v_iN) →
    (ret_val_lst = (ibits_ v_N v_iN)) →
    Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst

def fbits__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List bit)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fbits_ v_N v_fN)) →
    Forall (fun (ret_val : bit) => (wf_bit ret_val)) ret_val_lst

def ibytes__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val_lst : (List byte)), (wf_uN v_N v_iN) →
    (ret_val_lst = (ibytes_ v_N v_iN)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def fbytes__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List byte)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fbytes_ v_N v_fN)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def nbytes__is_wf : Prop :=
  ∀ (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : (List byte)), (wf_num_ v_numtype v_num_) →
    (ret_val_lst = (nbytes_ v_numtype v_num_)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def vbytes__is_wf : Prop :=
  ∀ (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : (List byte)), (wf_uN (vsize v_vectype) v_vec_) →
    (ret_val_lst = (vbytes_ v_vectype v_vec_)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def zbytes__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val_lst : (List byte)), (wf_storagetype v_storagetype) →
    (wf_lit_ v_storagetype v_lit_) →
    (ret_val_lst = (zbytes_ v_storagetype v_lit_)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def cbytes__is_wf : Prop :=
  ∀ (v_Cnn : Cnn) (v_lit_ : lit_) (ret_val_lst : (List byte)), (wf_lit_ (storagetype_Cnn v_Cnn) v_lit_) →
    (ret_val_lst = (cbytes_ v_Cnn v_lit_)) →
    Forall (fun (ret_val : byte) => (wf_byte ret_val)) ret_val_lst

def inv_ibits__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List bit)) (ret_val : iN), Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst →
    (ret_val = (inv_ibits_ v_N var_0_lst)) →
    (wf_uN v_N ret_val)

def inv_fbits__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List bit)) (ret_val : fN), Forall (fun (var_0 : bit) => (wf_bit var_0)) var_0_lst →
    (ret_val = (inv_fbits_ v_N var_0_lst)) →
    (wf_fN v_N ret_val)

def inv_ibytes__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List byte)) (ret_val : iN), Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_ibytes_ v_N var_0_lst)) →
    (wf_uN v_N ret_val)

def inv_fbytes__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List byte)) (ret_val : fN), Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_fbytes_ v_N var_0_lst)) →
    (wf_fN v_N ret_val)

def inv_nbytes__is_wf : Prop :=
  ∀ (v_numtype : numtype) (var_0_lst : (List byte)) (ret_val : num_), Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_nbytes_ v_numtype var_0_lst)) →
    (wf_num_ v_numtype ret_val)

def inv_vbytes__is_wf : Prop :=
  ∀ (v_vectype : vectype) (var_0_lst : (List byte)) (ret_val : vec_), Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_vbytes_ v_vectype var_0_lst)) →
    (wf_uN (vsize v_vectype) ret_val)

def inv_zbytes__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (var_0_lst : (List byte)) (ret_val : lit_), (wf_storagetype v_storagetype) →
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_zbytes_ v_storagetype var_0_lst)) →
    (wf_lit_ v_storagetype ret_val)

def inv_cbytes__is_wf : Prop :=
  ∀ (v_Cnn : Cnn) (var_0_lst : (List byte)) (ret_val : lit_), Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (inv_cbytes_ v_Cnn var_0_lst)) →
    (wf_lit_ (storagetype_Cnn v_Cnn) ret_val)

def zero_is_wf : Prop :=
  ∀ (v_lanetype : lanetype) (ret_val : lane_) (var_0 : lane_), (fun_zero v_lanetype var_0) →
    (ret_val = var_0) →
    (wf_lane_ v_lanetype ret_val)

def ineg__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (ineg_ v_N v_iN)) →
    (0 ≤ (Int.tmod ((Int.ofNat (2 ^ v_N)) - (Int.ofNat (proj_uN_0 v_iN))) (Int.ofNat (2 ^ v_N)))) →
    ((Int.ofNat (2 ^ v_N)) ≠ 0) →
    (wf_uN v_N ret_val)

def iabs__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (iabs_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def iclz__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (iclz_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def ictz__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (ictz_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def ipopcnt__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (ipopcnt_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def iextend__is_wf : Prop :=
  ∀ (v_N : N) (v_M : M) (v_sx : sx) (v_iN : iN) (ret_val : iN) (var_0 : iN), (fun_iextend_ v_N v_M v_sx v_iN var_0) →
    (wf_uN v_N v_iN) →
    (ret_val = var_0) →
    (wf_uN v_N ret_val)

def iadd__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iadd_ v_N v_iN iN_0)) →
    ((2 ^ v_N) ≠ 0) →
    (wf_uN v_N ret_val)

def isub__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (isub_ v_N v_iN iN_0)) →
    (0 ≤ (Int.tmod ((Int.ofNat ((2 ^ v_N) + (proj_uN_0 v_iN))) - (Int.ofNat (proj_uN_0 iN_0))) (Int.ofNat (2 ^ v_N)))) →
    ((Int.ofNat (2 ^ v_N)) ≠ 0) →
    (wf_uN v_N ret_val)

def imul__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (imul_ v_N v_iN iN_0)) →
    ((2 ^ v_N) ≠ 0) →
    (wf_uN v_N ret_val)

def irem__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : (Option iN)) (var_0 : (Option iN)), (fun_irem_ v_N v_sx v_iN iN_0 var_0) →
    (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val_opt = var_0) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (Option.toList ret_val_opt)

def imin__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (imin_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def imax__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (imax_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def iadd_sat__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iadd_sat_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def isub_sat__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (isub_sat_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def iq15mulr_sat__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iq15mulr_sat_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def irelaxed_q15mulr__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_lst : (List iN)), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val_lst = (irelaxed_q15mulr_ v_N v_sx v_iN iN_0)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def iavgr__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iavgr_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def inot__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (inot_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def irev__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (ret_val = (irev_ v_N v_iN)) →
    (wf_uN v_N ret_val)

def iand__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iand_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def iandnot__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (iandnot_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def ior__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ior_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def ixor__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ixor_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def ishl__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ishl_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def ishr__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ishr_ v_N v_sx v_iN iN_0)) →
    (wf_uN v_N ret_val)

def irotl__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (irotl_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def irotr__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (irotr_ v_N v_iN iN_0)) →
    (wf_uN v_N ret_val)

def ibitselect__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (wf_uN v_N iN_1) →
    (ret_val = (ibitselect_ v_N v_iN iN_0 iN_1)) →
    (wf_uN v_N ret_val)

def irelaxed_laneselect__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val_lst : (List iN)), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (wf_uN v_N iN_1) →
    (ret_val_lst = (irelaxed_laneselect_ v_N v_iN iN_0 iN_1)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def ieqz__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (ret_val = (ieqz_ v_N v_iN)) →
    (wf_uN 32 ret_val)

def inez__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (ret_val = (inez_ v_N v_iN)) →
    (wf_uN 32 ret_val)

def ieq__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ieq_ v_N v_iN iN_0)) →
    (wf_uN 32 ret_val)

def ine__is_wf : Prop :=
  ∀ (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ine_ v_N v_iN iN_0)) →
    (wf_uN 32 ret_val)

def ilt__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ilt_ v_N v_sx v_iN iN_0)) →
    (wf_uN 32 ret_val)

def igt__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (igt_ v_N v_sx v_iN iN_0)) →
    (wf_uN 32 ret_val)

def ile__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ile_ v_N v_sx v_iN iN_0)) →
    (wf_uN 32 ret_val)

def ige__is_wf : Prop :=
  ∀ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32), (wf_uN v_N v_iN) →
    (wf_uN v_N iN_0) →
    (ret_val = (ige_ v_N v_sx v_iN iN_0)) →
    (wf_uN 32 ret_val)

def fabs__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fabs_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fneg__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fneg_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fsqrt__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fsqrt_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fceil__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fceil_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def ffloor__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (ffloor_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def ftrunc__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (ftrunc_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fnearest__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (ret_val_lst = (fnearest_ v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fadd__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fadd_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fsub__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fsub_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fmul__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fmul_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fdiv__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fdiv_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fmin__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fmin_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fmax__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fmax_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fpmin__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fpmin_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fpmax__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fpmax_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def frelaxed_min__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (frelaxed_min_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def frelaxed_max__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (frelaxed_max_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def fcopysign__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val_lst = (fcopysign_ v_N v_fN fN_0)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def feq__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (feq_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def fne__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (fne_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def flt__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (flt_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def fgt__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (fgt_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def fle__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (fle_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def fge__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (ret_val = (fge_ v_N v_fN fN_0)) →
    (wf_uN 32 ret_val)

def frelaxed_madd__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (wf_fN v_N fN_1) →
    (ret_val_lst = (frelaxed_madd_ v_N v_fN fN_0 fN_1)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def frelaxed_nmadd__is_wf : Prop :=
  ∀ (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) (ret_val_lst : (List fN)), (wf_fN v_N v_fN) →
    (wf_fN v_N fN_0) →
    (wf_fN v_N fN_1) →
    (ret_val_lst = (frelaxed_nmadd_ v_N v_fN fN_0 fN_1)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def wrap___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN), (wf_uN v_M v_iN) →
    (ret_val = (wrap__ v_M v_N v_iN)) →
    (wf_uN v_N ret_val)

def extend___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN), (wf_uN v_M v_iN) →
    (ret_val = (extend__ v_M v_N v_sx v_iN)) →
    (wf_uN v_N ret_val)

def trunc___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (Option iN)), (wf_fN v_M v_fN) →
    (ret_val_opt = (trunc__ v_M v_N v_sx v_fN)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (Option.toList ret_val_opt)

def trunc_sat___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (Option iN)), (wf_fN v_M v_fN) →
    (ret_val_opt = (trunc_sat__ v_M v_N v_sx v_fN)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (Option.toList ret_val_opt)

def relaxed_trunc___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : (Option iN)), (wf_fN v_M v_fN) →
    (ret_val_opt = (relaxed_trunc__ v_M v_N v_sx v_fN)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) (Option.toList ret_val_opt)

def demote___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_M v_fN) →
    (ret_val_lst = (demote__ v_M v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def promote___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : (List fN)), (wf_fN v_M v_fN) →
    (ret_val_lst = (promote__ v_M v_N v_fN)) →
    Forall (fun (ret_val : fN) => (wf_fN v_N ret_val)) ret_val_lst

def convert___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : fN), (wf_uN v_M v_iN) →
    (ret_val = (convert__ v_M v_N v_sx v_iN)) →
    (wf_fN v_N ret_val)

def narrow___is_wf : Prop :=
  ∀ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN), (wf_uN v_M v_iN) →
    (ret_val = (narrow__ v_M v_N v_sx v_iN)) →
    (wf_uN v_N ret_val)

def reinterpret___is_wf : Prop :=
  ∀ (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_), (wf_num_ numtype_1 v_num_) →
    (ret_val = (reinterpret__ numtype_1 numtype_2 v_num_)) →
    (wf_num_ numtype_2 ret_val)

def lpacknum__is_wf : Prop :=
  ∀ (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_), (wf_num_ (lunpack v_lanetype) v_num_) →
    ((lpacknum_ v_lanetype v_num_) ≠ none) →
    (ret_val = (Option.get! (lpacknum_ v_lanetype v_num_))) →
    (wf_lane_ v_lanetype ret_val)

def cpacknum__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val : lit_), (wf_storagetype v_storagetype) →
    ((cunpack v_storagetype) ≠ none) →
    (wf_lit_ (storagetype_consttype (Option.get! (cunpack v_storagetype))) v_lit_) →
    ((cpacknum_ v_storagetype v_lit_) ≠ none) →
    (ret_val = (Option.get! (cpacknum_ v_storagetype v_lit_))) →
    (wf_lit_ v_storagetype ret_val)

def lunpacknum__is_wf : Prop :=
  ∀ (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_), (wf_lane_ v_lanetype v_lane_) →
    ((lunpacknum_ v_lanetype v_lane_) ≠ none) →
    (ret_val = (Option.get! (lunpacknum_ v_lanetype v_lane_))) →
    (wf_num_ (lunpack v_lanetype) ret_val)

def cunpacknum__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val : lit_), (wf_storagetype v_storagetype) →
    (wf_lit_ v_storagetype v_lit_) →
    ((cunpacknum_ v_storagetype v_lit_) ≠ none) →
    (ret_val = (Option.get! (cunpacknum_ v_storagetype v_lit_))) →
    ((cunpack v_storagetype) ≠ none) →
    (wf_lit_ (storagetype_consttype (Option.get! (cunpack v_storagetype))) ret_val)

def unop__is_wf : Prop :=
  ∀ (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : (List num_)) (var_0 : (Option (List num_))), (fun_unop_ v_numtype v_unop_ v_num_ var_0) →
    (wf_unop_ v_numtype v_unop_) →
    (wf_num_ v_numtype v_num_) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : num_) => (wf_num_ v_numtype ret_val)) ret_val_lst

def testop__is_wf : Prop :=
  ∀ (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : u32), (wf_testop_ v_numtype v_testop_) →
    (wf_num_ v_numtype v_num_) →
    ((fun_testop_ v_numtype v_testop_ v_num_) ≠ none) →
    (ret_val = (Option.get! (fun_testop_ v_numtype v_testop_ v_num_))) →
    (wf_uN 32 ret_val)

def relop__is_wf : Prop :=
  ∀ (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : u32), (wf_relop_ v_numtype v_relop_) →
    (wf_num_ v_numtype v_num_) →
    (wf_num_ v_numtype num__0) →
    ((fun_relop_ v_numtype v_relop_ v_num_ num__0) ≠ none) →
    (ret_val = (Option.get! (fun_relop_ v_numtype v_relop_ v_num_ num__0))) →
    (wf_uN 32 ret_val)

def cvtop___is_wf : Prop :=
  ∀ (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop__ : cvtop__) (v_num_ : num_) (ret_val_lst : (List num_)) (var_0 : (Option (List num_))), (fun_cvtop__ numtype_1 numtype_2 v_cvtop__ v_num_ var_0) →
    (wf_cvtop__ numtype_1 numtype_2 v_cvtop__) →
    (wf_num_ numtype_1 v_num_) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : num_) => (wf_num_ numtype_2 ret_val)) ret_val_lst

def lanes__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : (List lane_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (ret_val_lst = (lanes_ v_shape v_vec_)) →
    Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype v_shape) ret_val)) ret_val_lst

def inv_lanes__is_wf : Prop :=
  ∀ (v_shape : shape) (var_0_lst : (List lane_)) (ret_val : vec_), (wf_shape v_shape) →
    Forall (fun (var_0 : lane_) => (wf_lane_ (fun_lanetype v_shape) var_0)) var_0_lst →
    (ret_val = (inv_lanes_ v_shape var_0_lst)) →
    (wf_uN 128 ret_val)

def iswizzle_lane__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (v_iN : iN) (ret_val : iN), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    (wf_uN v_N v_iN) →
    (ret_val = (iswizzle_lane_ v_N var_0_lst v_iN)) →
    (wf_uN v_N ret_val)

def irelaxed_swizzle_lane__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (v_iN : iN) (ret_val : iN), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    (wf_uN v_N v_iN) →
    (ret_val = (irelaxed_swizzle_lane_ v_N var_0_lst v_iN)) →
    (wf_uN v_N ret_val)

def ivunop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> iN -> iN) (v_vec_ : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    ((ivunop_ v_shape f_ v_vec_) ≠ none) →
    (ret_val_lst = (Option.get! (ivunop_ v_shape f_ v_vec_))) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def fvunop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> fN -> (List fN)) (v_vec_ : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (ret_val_lst = (fvunop_ v_shape f_ v_vec_)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def ivbinop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> iN -> iN -> iN) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    ((ivbinop_ v_shape f_ v_vec_ vec__0) ≠ none) →
    (ret_val_lst = (Option.get! (ivbinop_ v_shape f_ v_vec_ vec__0))) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def ivbinopsx__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> sx -> iN -> iN -> iN) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    ((ivbinopsx_ v_shape f_ v_sx v_vec_ vec__0) ≠ none) →
    (ret_val_lst = (Option.get! (ivbinopsx_ v_shape f_ v_sx v_vec_ vec__0))) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def ivbinopsxnd__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> sx -> iN -> iN -> (List iN)) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val_lst = (ivbinopsxnd_ v_shape f_ v_sx v_vec_ vec__0)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def fvbinop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> fN -> fN -> (List fN)) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val_lst = (fvbinop_ v_shape f_ v_vec_ vec__0)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def ivternopnd__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> iN -> iN -> iN -> (List iN)) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (wf_uN 128 vec__1) →
    (ret_val_lst = (ivternopnd_ v_shape f_ v_vec_ vec__0 vec__1)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def fvternop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> fN -> fN -> fN -> (List fN)) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : (List vec_)), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (wf_uN 128 vec__1) →
    (ret_val_lst = (fvternop_ v_shape f_ v_vec_ vec__0 vec__1)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def ivrelop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> iN -> iN -> u32) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val = (ivrelop_ v_shape f_ v_vec_ vec__0)) →
    (wf_uN 128 ret_val)

def ivrelopsx__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> sx -> iN -> iN -> u32) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val = (ivrelopsx_ v_shape f_ v_sx v_vec_ vec__0)) →
    (wf_uN 128 ret_val)

def fvrelop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> fN -> fN -> u32) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val = (fvrelop_ v_shape f_ v_vec_ vec__0)) →
    (wf_uN 128 ret_val)

def ivshiftop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> iN -> iN -> iN) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 32 v_u32) →
    ((ivshiftop_ v_shape f_ v_vec_ v_u32) ≠ none) →
    (ret_val = (Option.get! (ivshiftop_ v_shape f_ v_vec_ v_u32))) →
    (wf_uN 128 ret_val)

def ivshiftopsx__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> sx -> iN -> iN -> iN) (v_sx : sx) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 32 v_u32) →
    ((ivshiftopsx_ v_shape f_ v_sx v_vec_ v_u32) ≠ none) →
    (ret_val = (Option.get! (ivshiftopsx_ v_shape f_ v_sx v_vec_ v_u32))) →
    (wf_uN 128 ret_val)

def ivbitmaskop__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vec_ : vec_) (ret_val : u32) (var_0 : u32), (fun_ivbitmaskop_ v_shape v_vec_ var_0) →
    (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (ret_val = var_0) →
    (wf_uN 32 ret_val)

def ivswizzlop__is_wf : Prop :=
  ∀ (v_shape : shape) (f_ : N -> (List iN) -> iN -> iN) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape v_shape) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    ((ivswizzlop_ v_shape f_ v_vec_ vec__0) ≠ none) →
    (ret_val = (Option.get! (ivswizzlop_ v_shape f_ v_vec_ vec__0))) →
    (wf_uN 128 ret_val)

def ivshufflop__is_wf : Prop :=
  ∀ (v_shape : shape) (var_0_lst : (List laneidx)) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape v_shape) →
    Forall (fun (var_0 : laneidx) => (wf_uN 8 var_0)) var_0_lst →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    ((ivshufflop_ v_shape var_0_lst v_vec_ vec__0) ≠ none) →
    (ret_val = (Option.get! (ivshufflop_ v_shape var_0_lst v_vec_ vec__0))) →
    (wf_uN 128 ret_val)

def vvunop__is_wf : Prop :=
  ∀ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val_lst : (List vec_)), (wf_uN (vsize v_vectype) v_vec_) →
    (ret_val_lst = (vvunop_ v_vectype v_vvunop v_vec_)) →
    Forall (fun (ret_val : vec_) => (wf_uN (vsize v_vectype) ret_val)) ret_val_lst

def vvbinop__is_wf : Prop :=
  ∀ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)), (wf_uN (vsize v_vectype) v_vec_) →
    (wf_uN (vsize v_vectype) vec__0) →
    (ret_val_lst = (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0)) →
    Forall (fun (ret_val : vec_) => (wf_uN (vsize v_vectype) ret_val)) ret_val_lst

def vvternop__is_wf : Prop :=
  ∀ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : (List vec_)), (wf_uN (vsize v_vectype) v_vec_) →
    (wf_uN (vsize v_vectype) vec__0) →
    (wf_uN (vsize v_vectype) vec__1) →
    (ret_val_lst = (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1)) →
    Forall (fun (ret_val : vec_) => (wf_uN (vsize v_vectype) ret_val)) ret_val_lst

def vunop__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : (List vec_)) (var_0 : (Option (List vec_))), (fun_vunop_ v_shape v_vunop_ v_vec_ var_0) →
    (wf_shape v_shape) →
    (wf_vunop_ v_shape v_vunop_) →
    (wf_uN 128 v_vec_) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def vbinop__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : (List vec_)) (var_0 : (Option (List vec_))), (fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0) →
    (wf_shape v_shape) →
    (wf_vbinop_ v_shape v_vbinop_) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def vternop__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vternop_ : vternop_) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : (List vec_)) (var_0 : (Option (List vec_))), (fun_vternop_ v_shape v_vternop_ v_vec_ vec__0 vec__1 var_0) →
    (wf_shape v_shape) →
    (wf_vternop_ v_shape v_vternop_) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (wf_uN 128 vec__1) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : vec_) => (wf_uN 128 ret_val)) ret_val_lst

def vrelop__is_wf : Prop :=
  ∀ (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0) →
    (wf_shape v_shape) →
    (wf_vrelop_ v_shape v_vrelop_) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def lcvtop___is_wf : Prop :=
  ∀ (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_lane_ : lane_) (ret_val_lst : (List lane_)) (var_0 : (Option (List lane_))), (fun_lcvtop__ shape_1 shape_2 v_vcvtop__ v_lane_ var_0) →
    (wf_shape shape_1) →
    (wf_shape shape_2) →
    (wf_vcvtop__ shape_1 shape_2 v_vcvtop__) →
    (wf_lane_ (fun_lanetype shape_1) v_lane_) →
    (var_0 ≠ none) →
    (ret_val_lst = (Option.get! var_0)) →
    Forall (fun (ret_val : lane_) => (wf_lane_ (fun_lanetype shape_2) ret_val)) ret_val_lst

def vcvtop___is_wf : Prop :=
  ∀ (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vcvtop__ shape_1 shape_2 v_vcvtop__ v_vec_ var_0) →
    (wf_shape shape_1) →
    (wf_shape shape_2) →
    (wf_vcvtop__ shape_1 shape_2 v_vcvtop__) →
    (wf_uN 128 v_vec_) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def vshiftop__is_wf : Prop :=
  ∀ (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vshiftop_ v_ishape v_vshiftop_ v_vec_ v_u32 var_0) →
    (wf_ishape v_ishape) →
    (wf_vshiftop_ v_ishape v_vshiftop_) →
    (wf_uN 128 v_vec_) →
    (wf_uN 32 v_u32) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def vbitmaskop__is_wf : Prop :=
  ∀ (v_ishape : ishape) (v_vec_ : vec_) (ret_val : u32) (var_0 : u32), (fun_vbitmaskop_ v_ishape v_vec_ var_0) →
    (wf_ishape v_ishape) →
    (wf_uN 128 v_vec_) →
    (ret_val = var_0) →
    (wf_uN 32 ret_val)

def vswizzlop__is_wf : Prop :=
  ∀ (v_bshape : bshape) (v_vswizzlop_ : vswizzlop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vswizzlop_ v_bshape v_vswizzlop_ v_vec_ vec__0 var_0) →
    (wf_bshape v_bshape) →
    (wf_vswizzlop_ v_bshape v_vswizzlop_) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def vshufflop__is_wf : Prop :=
  ∀ (v_bshape : bshape) (var_0_lst : (List laneidx)) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_bshape v_bshape) →
    Forall (fun (var_0 : laneidx) => (wf_uN 8 var_0)) var_0_lst →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    ((vshufflop_ v_bshape var_0_lst v_vec_ vec__0) ≠ none) →
    (ret_val = (Option.get! (vshufflop_ v_bshape var_0_lst v_vec_ vec__0))) →
    (wf_uN 128 ret_val)

def vnarrowop___is_wf : Prop :=
  ∀ (shape_1 : shape) (shape_2 : shape) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_), (fun_vnarrowop__ shape_1 shape_2 v_sx v_vec_ vec__0 var_0) →
    (wf_shape shape_1) →
    (wf_shape shape_2) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val = var_0) →
    (wf_uN 128 ret_val)

def ivadd_pairwise__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (ret_val_lst : (List iN)), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    (ret_val_lst = (ivadd_pairwise_ v_N var_0_lst)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def ivextunop___is_wf : Prop :=
  ∀ (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN)) (v_sx : sx) (v_vec_ : vec_) (ret_val : vec_), (wf_shape shape_1) →
    (wf_shape shape_2) →
    (wf_uN 128 v_vec_) →
    (ret_val = (ivextunop__ shape_1 shape_2 f_ v_sx v_vec_)) →
    (wf_uN 128 ret_val)

def vextunop___is_wf : Prop :=
  ∀ (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop__ : vextunop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vextunop__ ishape_1 ishape_2 v_vextunop__ v_vec_ var_0) →
    (wf_ishape ishape_1) →
    (wf_ishape ishape_2) →
    (wf_vextunop__ ishape_1 ishape_2 v_vextunop__) →
    (wf_uN 128 v_vec_) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def ivdot__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (var_1_lst : (List iN)) (ret_val_lst : (List iN)), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    Forall (fun (var_1 : iN) => (wf_uN v_N var_1)) var_1_lst →
    (ret_val_lst = (ivdot_ v_N var_0_lst var_1_lst)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def ivdot_sat__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (var_1_lst : (List iN)) (ret_val_lst : (List iN)), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    Forall (fun (var_1 : iN) => (wf_uN v_N var_1)) var_1_lst →
    (ret_val_lst = (ivdot_sat_ v_N var_0_lst var_1_lst)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def ivextbinop___is_wf : Prop :=
  ∀ (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN) -> (List iN)) (v_sx : sx) (sx_0 : sx) (v_laneidx : laneidx) (laneidx_0 : laneidx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_), (wf_shape shape_1) →
    (wf_shape shape_2) →
    (wf_uN 8 v_laneidx) →
    (wf_uN 8 laneidx_0) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (ret_val = (ivextbinop__ shape_1 shape_2 f_ v_sx sx_0 v_laneidx laneidx_0 v_vec_ vec__0)) →
    (wf_uN 128 ret_val)

def ivmul__is_wf : Prop :=
  ∀ (v_N : N) (var_0_lst : (List iN)) (var_1_lst : (List iN)) (ret_val_lst : (List iN)), Forall (fun (var_0 : iN) => (wf_uN v_N var_0)) var_0_lst →
    Forall (fun (var_1 : iN) => (wf_uN v_N var_1)) var_1_lst →
    (ret_val_lst = (ivmul_ v_N var_0_lst var_1_lst)) →
    Forall (fun (ret_val : iN) => (wf_uN v_N ret_val)) ret_val_lst

def vextbinop___is_wf : Prop :=
  ∀ (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop__ : vextbinop__) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vextbinop__ ishape_1 ishape_2 v_vextbinop__ v_vec_ vec__0 var_0) →
    (wf_ishape ishape_1) →
    (wf_ishape ishape_2) →
    (wf_vextbinop__ ishape_1 ishape_2 v_vextbinop__) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

def vextternop___is_wf : Prop :=
  ∀ (ishape_1 : ishape) (ishape_2 : ishape) (v_vextternop__ : vextternop__) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_) (var_0 : (Option vec_)), (fun_vextternop__ ishape_1 ishape_2 v_vextternop__ v_vec_ vec__0 vec__1 var_0) →
    (wf_ishape ishape_1) →
    (wf_ishape ishape_2) →
    (wf_vextternop__ ishape_1 ishape_2 v_vextternop__) →
    (wf_uN 128 v_vec_) →
    (wf_uN 128 vec__0) →
    (wf_uN 128 vec__1) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_uN 128 ret_val)

@[grind ←]
theorem wf_datainst_append (a b : datainst) (ha : wf_datainst a) (hb : wf_datainst b) :
    wf_datainst (a ++ b) := by
  rw [show a ++ b = _append_datainst a b from rfl]
  cases ha; cases hb
  constructor <;> simp_all [Forall, _append_datainst] <;> (rintro x (h | h) <;> simp_all)

def packfield__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (v_val : val) (ret_val : fieldval), (wf_storagetype v_storagetype) →
    (wf_val v_val) →
    ((packfield_ v_storagetype v_val) ≠ none) →
    (ret_val = (Option.get! (packfield_ v_storagetype v_val))) →
    (wf_fieldval ret_val)

def unpackfield__is_wf : Prop :=
  ∀ (v_storagetype : storagetype) (var_0_opt : (Option sx)) (v_fieldval : fieldval) (ret_val : val), (wf_storagetype v_storagetype) →
    (wf_fieldval v_fieldval) →
    ((unpackfield_ v_storagetype var_0_opt v_fieldval) ≠ none) →
    (ret_val = (Option.get! (unpackfield_ v_storagetype var_0_opt v_fieldval))) →
    (wf_val ret_val)

def store_is_wf : Prop :=
  ∀ (v_state : state) (ret_val : store), (wf_state v_state) →
    (ret_val = (fun_store v_state)) →
    (wf_store ret_val)

def frame_is_wf : Prop :=
  ∀ (v_state : state) (ret_val : frame), (wf_state v_state) →
    (ret_val = (fun_frame v_state)) →
    (wf_frame ret_val)

def moduleinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val : moduleinst), (wf_state v_state) →
    (ret_val = (fun_moduleinst v_state)) →
    (wf_moduleinst ret_val)

def taginst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List taginst)), (wf_state v_state) →
    (ret_val_lst = (fun_taginst v_state)) →
    Forall (fun (ret_val : taginst) => (wf_taginst ret_val)) ret_val_lst

def globalinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List globalinst)), (wf_state v_state) →
    (ret_val_lst = (fun_globalinst v_state)) →
    Forall (fun (ret_val : globalinst) => (wf_globalinst ret_val)) ret_val_lst

def meminst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List meminst)), (wf_state v_state) →
    (ret_val_lst = (fun_meminst v_state)) →
    Forall (fun (ret_val : meminst) => (wf_meminst ret_val)) ret_val_lst

def tableinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List tableinst)), (wf_state v_state) →
    (ret_val_lst = (fun_tableinst v_state)) →
    Forall (fun (ret_val : tableinst) => (wf_tableinst ret_val)) ret_val_lst

def funcinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List funcinst)), (wf_state v_state) →
    (ret_val_lst = (fun_funcinst v_state)) →
    Forall (fun (ret_val : funcinst) => (wf_funcinst ret_val)) ret_val_lst

def datainst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List datainst)), (wf_state v_state) →
    (ret_val_lst = (fun_datainst v_state)) →
    Forall (fun (ret_val : datainst) => (wf_datainst ret_val)) ret_val_lst

def eleminst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List eleminst)), (wf_state v_state) →
    (ret_val_lst = (fun_eleminst v_state)) →
    Forall (fun (ret_val : eleminst) => (wf_eleminst ret_val)) ret_val_lst

def structinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List structinst)), (wf_state v_state) →
    (ret_val_lst = (fun_structinst v_state)) →
    Forall (fun (ret_val : structinst) => (wf_structinst ret_val)) ret_val_lst

def arrayinst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List arrayinst)), (wf_state v_state) →
    (ret_val_lst = (fun_arrayinst v_state)) →
    Forall (fun (ret_val : arrayinst) => (wf_arrayinst ret_val)) ret_val_lst

def exninst_is_wf : Prop :=
  ∀ (v_state : state) (ret_val_lst : (List exninst)), (wf_state v_state) →
    (ret_val_lst = (fun_exninst v_state)) →
    Forall (fun (ret_val : exninst) => (wf_exninst ret_val)) ret_val_lst

def fof_is_wf : Prop :=
  ∀ (v_state : state) (ret_val : frame), (wf_state v_state) →
    (ret_val = (fof v_state)) →
    (wf_frame ret_val)

def sof_is_wf : Prop :=
  ∀ (v_state : state) (ret_val : store), (wf_state v_state) →
    (ret_val = (sof v_state)) →
    (wf_store ret_val)

def tag_is_wf : Prop :=
  ∀ (v_state : state) (v_tagidx : tagidx) (ret_val : taginst), (wf_state v_state) →
    (wf_uN 32 v_tagidx) →
    (ret_val = (fun_tag v_state v_tagidx)) →
    (((((fof v_state).MODULE).TAGS)[(proj_uN_0 v_tagidx)]!) < (List.length ((sof v_state).TAGS))) →
    ((proj_uN_0 v_tagidx) < (List.length (((fof v_state).MODULE).TAGS))) →
    (wf_taginst ret_val)

def global_is_wf : Prop :=
  ∀ (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst), (wf_state v_state) →
    (wf_uN 32 v_globalidx) →
    (ret_val = (fun_global v_state v_globalidx)) →
    (((((fof v_state).MODULE).GLOBALS)[(proj_uN_0 v_globalidx)]!) < (List.length ((sof v_state).GLOBALS))) →
    ((proj_uN_0 v_globalidx) < (List.length (((fof v_state).MODULE).GLOBALS))) →
    (wf_globalinst ret_val)

def mem_is_wf : Prop :=
  ∀ (v_state : state) (v_memidx : memidx) (ret_val : meminst), (wf_state v_state) →
    (wf_uN 32 v_memidx) →
    (ret_val = (fun_mem v_state v_memidx)) →
    (((((fof v_state).MODULE).MEMS)[(proj_uN_0 v_memidx)]!) < (List.length ((sof v_state).MEMS))) →
    ((proj_uN_0 v_memidx) < (List.length (((fof v_state).MODULE).MEMS))) →
    (wf_meminst ret_val)

def table_is_wf : Prop :=
  ∀ (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst), (wf_state v_state) →
    (wf_uN 32 v_tableidx) →
    (ret_val = (fun_table v_state v_tableidx)) →
    (((((fof v_state).MODULE).TABLES)[(proj_uN_0 v_tableidx)]!) < (List.length ((sof v_state).TABLES))) →
    ((proj_uN_0 v_tableidx) < (List.length (((fof v_state).MODULE).TABLES))) →
    (wf_tableinst ret_val)

def func_is_wf : Prop :=
  ∀ (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst), (wf_state v_state) →
    (wf_uN 32 v_funcidx) →
    (ret_val = (fun_func v_state v_funcidx)) →
    (((((fof v_state).MODULE).FUNCS)[(proj_uN_0 v_funcidx)]!) < (List.length ((sof v_state).FUNCS))) →
    ((proj_uN_0 v_funcidx) < (List.length (((fof v_state).MODULE).FUNCS))) →
    (wf_funcinst ret_val)

def data_is_wf : Prop :=
  ∀ (v_state : state) (v_dataidx : dataidx) (ret_val : datainst), (wf_state v_state) →
    (wf_uN 32 v_dataidx) →
    (ret_val = (fun_data v_state v_dataidx)) →
    (((((fof v_state).MODULE).DATAS)[(proj_uN_0 v_dataidx)]!) < (List.length ((sof v_state).DATAS))) →
    ((proj_uN_0 v_dataidx) < (List.length (((fof v_state).MODULE).DATAS))) →
    (wf_datainst ret_val)

def elem_is_wf : Prop :=
  ∀ (v_state : state) (v_tableidx : tableidx) (ret_val : eleminst), (wf_state v_state) →
    (wf_uN 32 v_tableidx) →
    (ret_val = (fun_elem v_state v_tableidx)) →
    (((((fof v_state).MODULE).ELEMS)[(proj_uN_0 v_tableidx)]!) < (List.length ((sof v_state).ELEMS))) →
    ((proj_uN_0 v_tableidx) < (List.length (((fof v_state).MODULE).ELEMS))) →
    (wf_eleminst ret_val)

def local_is_wf : Prop :=
  ∀ (v_state : state) (v_localidx : localidx) (ret_val_opt : (Option val)), (wf_state v_state) →
    (wf_uN 32 v_localidx) →
    (ret_val_opt = (fun_local v_state v_localidx)) →
    ((proj_uN_0 v_localidx) < (List.length ((fof v_state).LOCALS))) →
    Forall (fun (ret_val : val) => (wf_val ret_val)) (Option.toList ret_val_opt)

def with_local_is_wf : Prop :=
  ∀ (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_localidx) →
    (wf_val v_val) →
    (ret_val = (with_local v_state v_localidx v_val)) →
    ((proj_uN_0 v_localidx) < (List.length ((fof v_state).LOCALS))) →
    (wf_state ret_val)

def with_global_is_wf : Prop :=
  ∀ (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_globalidx) →
    (wf_val v_val) →
    (ret_val = (with_global v_state v_globalidx v_val)) →
    (((((fof v_state).MODULE).GLOBALS)[(proj_uN_0 v_globalidx)]!) < (List.length ((sof v_state).GLOBALS))) →
    ((proj_uN_0 v_globalidx) < (List.length (((fof v_state).MODULE).GLOBALS))) →
    (wf_state ret_val)

def with_table_is_wf : Prop :=
  ∀ (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_tableidx) →
    (wf_ref v_ref) →
    (ret_val = (with_table v_state v_tableidx nat v_ref)) →
    (((((fof v_state).MODULE).TABLES)[(proj_uN_0 v_tableidx)]!) < (List.length ((sof v_state).TABLES))) →
    (nat < (List.length ((((sof v_state).TABLES)[((((fof v_state).MODULE).TABLES)[(proj_uN_0 v_tableidx)]!)]!).REFS))) →
    ((proj_uN_0 v_tableidx) < (List.length (((fof v_state).MODULE).TABLES))) →
    (wf_state ret_val)

def with_tableinst_is_wf : Prop :=
  ∀ (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_tableidx) →
    (wf_tableinst v_tableinst) →
    (ret_val = (with_tableinst v_state v_tableidx v_tableinst)) →
    (((((fof v_state).MODULE).TABLES)[(proj_uN_0 v_tableidx)]!) < (List.length ((sof v_state).TABLES))) →
    ((proj_uN_0 v_tableidx) < (List.length (((fof v_state).MODULE).TABLES))) →
    (wf_state ret_val)

def with_mem_is_wf : Prop :=
  ∀ (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : (List byte)) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_memidx) →
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (with_mem v_state v_memidx nat nat_0 var_0_lst)) →
    (((((fof v_state).MODULE).MEMS)[(proj_uN_0 v_memidx)]!) < (List.length ((sof v_state).MEMS))) →
    (nat + nat_0 ≤ (List.length ((((sof v_state).MEMS)[((((fof v_state).MODULE).MEMS)[(proj_uN_0 v_memidx)]!)]!).BYTES))) →
    ((proj_uN_0 v_memidx) < (List.length (((fof v_state).MODULE).MEMS))) →
    (wf_state ret_val)

def with_meminst_is_wf : Prop :=
  ∀ (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_memidx) →
    (wf_meminst v_meminst) →
    (ret_val = (with_meminst v_state v_memidx v_meminst)) →
    (((((fof v_state).MODULE).MEMS)[(proj_uN_0 v_memidx)]!) < (List.length ((sof v_state).MEMS))) →
    ((proj_uN_0 v_memidx) < (List.length (((fof v_state).MODULE).MEMS))) →
    (wf_state ret_val)

def with_elem_is_wf : Prop :=
  ∀ (v_state : state) (v_elemidx : elemidx) (var_0_lst : (List ref)) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_elemidx) →
    Forall (fun (var_0 : ref) => (wf_ref var_0)) var_0_lst →
    (ret_val = (with_elem v_state v_elemidx var_0_lst)) →
    (((((fof v_state).MODULE).ELEMS)[(proj_uN_0 v_elemidx)]!) < (List.length ((sof v_state).ELEMS))) →
    ((proj_uN_0 v_elemidx) < (List.length (((fof v_state).MODULE).ELEMS))) →
    (wf_state ret_val)

def with_data_is_wf : Prop :=
  ∀ (v_state : state) (v_dataidx : dataidx) (var_0_lst : (List byte)) (ret_val : state), (wf_state v_state) →
    (wf_uN 32 v_dataidx) →
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = (with_data v_state v_dataidx var_0_lst)) →
    (((((fof v_state).MODULE).DATAS)[(proj_uN_0 v_dataidx)]!) < (List.length ((sof v_state).DATAS))) →
    ((proj_uN_0 v_dataidx) < (List.length (((fof v_state).MODULE).DATAS))) →
    (wf_state ret_val)

def with_struct_is_wf : Prop :=
  ∀ (v_state : state) (v_structaddr : structaddr) (nat : Nat) (v_fieldval : fieldval) (ret_val : state), (wf_state v_state) →
    (wf_fieldval v_fieldval) →
    (ret_val = (with_struct v_state v_structaddr nat v_fieldval)) →
    (v_structaddr < (List.length ((sof v_state).STRUCTS))) →
    (nat < (List.length ((((sof v_state).STRUCTS)[v_structaddr]!).FIELDS))) →
    (wf_state ret_val)

def with_array_is_wf : Prop :=
  ∀ (v_state : state) (v_arrayaddr : arrayaddr) (nat : Nat) (v_fieldval : fieldval) (ret_val : state), (wf_state v_state) →
    (wf_fieldval v_fieldval) →
    (ret_val = (with_array v_state v_arrayaddr nat v_fieldval)) →
    (v_arrayaddr < (List.length ((sof v_state).ARRAYS))) →
    (nat < (List.length ((((sof v_state).ARRAYS)[v_arrayaddr]!).FIELDS))) →
    (wf_state ret_val)

def add_structinst_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst : (List structinst)) (ret_val : state), (wf_state v_state) →
    Forall (fun (var_0 : structinst) => (wf_structinst var_0)) var_0_lst →
    (ret_val = (add_structinst v_state var_0_lst)) →
    (wf_state ret_val)

def add_arrayinst_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst : (List arrayinst)) (ret_val : state), (wf_state v_state) →
    Forall (fun (var_0 : arrayinst) => (wf_arrayinst var_0)) var_0_lst →
    (ret_val = (add_arrayinst v_state var_0_lst)) →
    (wf_state ret_val)

def add_exninst_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst : (List exninst)) (ret_val : state), (wf_state v_state) →
    Forall (fun (var_0 : exninst) => (wf_exninst var_0)) var_0_lst →
    (ret_val = (add_exninst v_state var_0_lst)) →
    (wf_state ret_val)

@[grind]
theorem growtable_is_wf :
    ∀ (v_tableinst : tableinst) (nat : Nat) (v_ref : ref) (ret_val : tableinst) (var_0 : (Option tableinst)), (fun_growtable v_tableinst nat v_ref var_0) →
    (wf_tableinst v_tableinst) →
    (wf_ref v_ref) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_tableinst ret_val) := by
  intro v_tableinst nat v_ref ret_val var_0 h0 h1 h2 h3 h4
  subst_vars
  cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done))

@[grind]
theorem growmem_is_wf :
    ∀ (v_meminst : meminst) (nat : Nat) (ret_val : meminst) (var_0 : (Option meminst)), (fun_growmem v_meminst nat var_0) →
    (wf_meminst v_meminst) →
    (var_0 ≠ none) →
    (ret_val = (Option.get! var_0)) →
    (wf_meminst ret_val) := by
  intro v_meminst nat ret_val var_0 h0 h1 h2 h3
  subst_vars
  cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done))

def inst_valtype_is_wf : Prop :=
  ∀ (v_moduleinst : moduleinst) (v_valtype : valtype) (ret_val : valtype) (var_0 : valtype), (fun_inst_valtype v_moduleinst v_valtype var_0) →
    (wf_moduleinst v_moduleinst) →
    (wf_valtype v_valtype) →
    (ret_val = var_0) →
    (wf_valtype ret_val)

def inst_reftype_is_wf : Prop :=
  ∀ (v_moduleinst : moduleinst) (v_reftype : reftype) (ret_val : reftype) (var_0 : reftype), (fun_inst_reftype v_moduleinst v_reftype var_0) →
    (wf_moduleinst v_moduleinst) →
    (wf_reftype v_reftype) →
    (ret_val = var_0) →
    (wf_reftype ret_val)

def inst_globaltype_is_wf : Prop :=
  ∀ (v_moduleinst : moduleinst) (v_globaltype : globaltype) (ret_val : globaltype) (var_0 : globaltype), (fun_inst_globaltype v_moduleinst v_globaltype var_0) →
    (wf_moduleinst v_moduleinst) →
    (wf_globaltype v_globaltype) →
    (ret_val = var_0) →
    (wf_globaltype ret_val)

def inst_memtype_is_wf : Prop :=
  ∀ (v_moduleinst : moduleinst) (v_memtype : memtype) (ret_val : memtype) (var_0 : memtype), (fun_inst_memtype v_moduleinst v_memtype var_0) →
    (wf_moduleinst v_moduleinst) →
    (wf_memtype v_memtype) →
    (ret_val = var_0) →
    (wf_memtype ret_val)

def inst_tabletype_is_wf : Prop :=
  ∀ (v_moduleinst : moduleinst) (v_tabletype : tabletype) (ret_val : tabletype) (var_0 : tabletype), (fun_inst_tabletype v_moduleinst v_tabletype var_0) →
    (wf_moduleinst v_moduleinst) →
    (wf_tabletype v_tabletype) →
    (ret_val = var_0) →
    (wf_tabletype ret_val)

def blocktype__is_wf : Prop :=
  ∀ (v_state : state) (v_blocktype : blocktype) (ret_val : instrtype) (var_0 : instrtype), (fun_blocktype_ v_state v_blocktype var_0) →
    (wf_state v_state) →
    (wf_blocktype v_blocktype) →
    (ret_val = var_0) →
    (wf_instrtype ret_val)

def alloctag_is_wf : Prop :=
  ∀ (v_store : store) (v_tagtype : tagtype) (ret_val : (store × tagaddr)) (var_0 : (store × tagaddr)), (fun_alloctag v_store v_tagtype var_0) →
    (wf_store v_store) →
    (wf_typeuse v_tagtype) →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def alloctags_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List tagtype)) (ret_val : (store × (List tagaddr))) (var_0 : (store × (List tagaddr))), (fun_alloctags v_store var_0_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : tagtype) => (wf_typeuse var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocglobal_is_wf : Prop :=
  ∀ (v_store : store) (v_globaltype : globaltype) (v_val : val) (ret_val : (store × globaladdr)) (var_0 : (store × globaladdr)), (fun_allocglobal v_store v_globaltype v_val var_0) →
    (wf_store v_store) →
    (wf_globaltype v_globaltype) →
    (wf_val v_val) →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocglobals_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List globaltype)) (var_1_lst : (List val)) (ret_val : (store × (List globaladdr))) (var_0 : (store × (List globaladdr))), (fun_allocglobals v_store var_0_lst var_1_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : globaltype) => (wf_globaltype var_0)) var_0_lst →
    Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocmem_is_wf : Prop :=
  ∀ (v_store : store) (v_memtype : memtype) (ret_val : (store × memaddr)) (var_0 : (store × memaddr)), (fun_allocmem v_store v_memtype var_0) →
    (wf_store v_store) →
    (wf_memtype v_memtype) →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocmems_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List memtype)) (ret_val : (store × (List memaddr))) (var_0 : (store × (List memaddr))), (fun_allocmems v_store var_0_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : memtype) => (wf_memtype var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def alloctable_is_wf : Prop :=
  ∀ (v_store : store) (v_tabletype : tabletype) (v_ref : ref) (ret_val : (store × tableaddr)) (var_0 : (store × tableaddr)), (fun_alloctable v_store v_tabletype v_ref var_0) →
    (wf_store v_store) →
    (wf_tabletype v_tabletype) →
    (wf_ref v_ref) →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def alloctables_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List tabletype)) (var_1_lst : (List ref)) (ret_val : (store × (List tableaddr))) (var_0 : (store × (List tableaddr))), (fun_alloctables v_store var_0_lst var_1_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : tabletype) => (wf_tabletype var_0)) var_0_lst →
    Forall (fun (var_1 : ref) => (wf_ref var_1)) var_1_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocfunc_is_wf : Prop :=
  ∀ (v_store : store) (v_deftype : deftype) (v_funccode : funccode) (v_moduleinst : moduleinst) (ret_val : (store × funcaddr)) (var_0 : (store × funcaddr)), (fun_allocfunc v_store v_deftype v_funccode v_moduleinst var_0) →
    (wf_store v_store) →
    (wf_deftype v_deftype) →
    (wf_funccode v_funccode) →
    (wf_moduleinst v_moduleinst) →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocfuncs_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List deftype)) (var_1_lst : (List funccode)) (var_2_lst : (List moduleinst)) (ret_val : (store × (List funcaddr))) (var_0 : (store × (List funcaddr))), (fun_allocfuncs v_store var_0_lst var_1_lst var_2_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : deftype) => (wf_deftype var_0)) var_0_lst →
    Forall (fun (var_1 : funccode) => (wf_funccode var_1)) var_1_lst →
    Forall (fun (var_2 : moduleinst) => (wf_moduleinst var_2)) var_2_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocdata_is_wf : Prop :=
  ∀ (v_store : store) (v_datatype : datatype) (var_0_lst : (List byte)) (ret_val : (store × dataaddr)) (var_0 : (store × dataaddr)), (fun_allocdata v_store v_datatype var_0_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocdatas_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List datatype)) (var_1_lst_lst : (List (List byte))) (ret_val : (store × (List dataaddr))) (var_0 : (store × (List dataaddr))), (fun_allocdatas v_store var_0_lst var_1_lst_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_1_lst : (List byte)) => Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1_lst) var_1_lst_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocelem_is_wf : Prop :=
  ∀ (v_store : store) (v_elemtype : elemtype) (var_0_lst : (List ref)) (ret_val : (store × elemaddr)) (var_0 : (store × elemaddr)), (fun_allocelem v_store v_elemtype var_0_lst var_0) →
    (wf_store v_store) →
    (wf_reftype v_elemtype) →
    Forall (fun (var_0 : ref) => (wf_ref var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

def allocelems_is_wf : Prop :=
  ∀ (v_store : store) (var_0_lst : (List elemtype)) (var_1_lst_lst : (List (List ref))) (ret_val : (store × (List elemaddr))) (var_0 : (store × (List elemaddr))), (fun_allocelems v_store var_0_lst var_1_lst_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : elemtype) => (wf_reftype var_0)) var_0_lst →
    Forall (fun (var_1_lst : (List ref)) => Forall (fun (var_1 : ref) => (wf_ref var_1)) var_1_lst) var_1_lst_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val))

@[grind]
theorem allocexport_is_wf :
    ∀ (v_moduleinst : moduleinst) (v_export : «export») (ret_val : exportinst), (wf_moduleinst v_moduleinst) →
    (wf_export v_export) →
    (ret_val = (allocexport v_moduleinst v_export)) →
    (wf_exportinst ret_val) := by
  intro v_moduleinst v_export ret_val h0 h1 h2
  subst_vars
  (subst_vars; first | (simp_all [Forall, allocexport]; done) | (simp_all [Forall, allocexport] <;> grind [Forall, allocexport]) | grind [Forall, allocexport] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, allocexport]; done) | omega | decide); done))

@[grind]
theorem allocexports_is_wf :
    ∀ (v_moduleinst : moduleinst) (var_0_lst : (List «export»)) (ret_val_lst : (List exportinst)), (wf_moduleinst v_moduleinst) →
    Forall (fun (var_0 : «export») => (wf_export var_0)) var_0_lst →
    (ret_val_lst = (allocexports v_moduleinst var_0_lst)) →
    Forall (fun (ret_val : exportinst) => (wf_exportinst ret_val)) ret_val_lst := by
  intro v_moduleinst var_0_lst ret_val_lst h0 h1 h2
  subst_vars
  (subst_vars; first | (simp_all [Forall, allocexports]; done) | (simp_all [Forall, allocexports] <;> grind [Forall, allocexports]) | grind [Forall, allocexports] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall, allocexports]; done) | omega | decide); done))

@[grind]
theorem allocmodule_is_wf :
    ∀ (v_store : store) (v_module : module) (var_0_lst : (List externaddr)) (var_1_lst : (List val)) (var_2_lst : (List ref)) (var_3_lst_lst : (List (List ref))) (ret_val : (store × moduleinst)) (var_0 : (store × moduleinst)), (fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst var_3_lst_lst var_0) →
    (wf_store v_store) →
    (wf_module v_module) →
    Forall (fun (var_1 : val) => (wf_val var_1)) var_1_lst →
    Forall (fun (var_2 : ref) => (wf_ref var_2)) var_2_lst →
    Forall (fun (var_3_lst : (List ref)) => Forall (fun (var_3 : ref) => (wf_ref var_3)) var_3_lst) var_3_lst_lst →
    (ret_val = var_0) →
    (wf_store (Prod.fst ret_val)) →
    (wf_moduleinst (Prod.snd ret_val)) := by
  intro v_store v_module var_0_lst var_1_lst var_2_lst var_3_lst_lst ret_val var_0 h0 h1 h2 h3 h4 h5 h6 h7
  subst_vars
  cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done))

def evalexprs_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst : (List expr)) (ret_val : (state × (List ref))) (var_0 : (state × (List ref))), (fun_evalexprs v_state var_0_lst var_0) →
    (wf_state v_state) →
    Forall (fun (var_0 : expr) => Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0) var_0_lst →
    (ret_val = var_0) →
    (wf_state (Prod.fst ret_val)) →
    Forall (fun (iter : ref) => (wf_ref iter)) (Prod.snd ret_val)

def evalexprss_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst_lst : (List (List expr))) (ret_val : (state × (List (List ref)))) (var_0 : (state × (List (List ref)))), (fun_evalexprss v_state var_0_lst_lst var_0) →
    (wf_state v_state) →
    Forall (fun (var_0_lst : (List expr)) => Forall (fun (var_0 : expr) => Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0) var_0_lst) var_0_lst_lst →
    (ret_val = var_0) →
    (wf_state (Prod.fst ret_val)) →
    Forall (fun (iter : (List ref)) => Forall (fun (iter : ref) => (wf_ref iter)) iter) (Prod.snd ret_val)

def evalglobals_is_wf : Prop :=
  ∀ (v_state : state) (var_0_lst : (List globaltype)) (var_1_lst : (List expr)) (ret_val : (state × (List val))) (var_0 : (state × (List val))), (fun_evalglobals v_state var_0_lst var_1_lst var_0) →
    (wf_state v_state) →
    Forall (fun (var_0 : globaltype) => (wf_globaltype var_0)) var_0_lst →
    Forall (fun (var_1 : expr) => Forall (fun (var_1 : instr) => (wf_instr var_1)) var_1) var_1_lst →
    (ret_val = var_0) →
    (wf_state (Prod.fst ret_val)) →
    Forall (fun (iter : val) => (wf_val iter)) (Prod.snd ret_val)

def invoke_is_wf : Prop :=
  ∀ (v_store : store) (v_funcaddr : funcaddr) (var_0_lst : (List val)) (ret_val : config) (var_0 : config), (fun_invoke v_store v_funcaddr var_0_lst var_0) →
    (wf_store v_store) →
    Forall (fun (var_0 : val) => (wf_val var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_config ret_val)

def ieee__is_wf : Prop :=
  ∀ (v_N : N) (rat : Rat) (ret_val : fNmag), (ret_val = (ieee_ v_N rat)) →
    (wf_fNmag v_N ret_val)

def concat_idctxt_is_wf : Prop :=
  ∀ (var_0_lst : (List idctxt)) (ret_val : idctxt) (var_0 : idctxt), (fun_concat_idctxt var_0_lst var_0) →
    Forall (fun (var_0 : idctxt) => (wf_idctxt var_0)) var_0_lst →
    (ret_val = var_0) →
    (wf_idctxt ret_val)

@[grind]
theorem importsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List «import»)) (var_0 : (List «import»)), (fun_importsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : «import») => (wf_import ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem tagsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List tag)) (var_0 : (List tag)), (fun_tagsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : tag) => (wf_tag ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem globalsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List global)) (var_0 : (List global)), (fun_globalsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : global) => (wf_global ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem memsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List mem)) (var_0 : (List mem)), (fun_memsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : mem) => (wf_mem ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem tablesd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List table)) (var_0 : (List table)), (fun_tablesd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : table) => (wf_table ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem funcsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List func)) (var_0 : (List func)), (fun_funcsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : func) => (wf_func ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem datasd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List data)) (var_0 : (List data)), (fun_datasd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : data) => (wf_data ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem elemsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List elem)) (var_0 : (List elem)), (fun_elemsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : elem) => (wf_elem ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem startsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List start)) (var_0 : (List start)), (fun_startsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : start) => (wf_start ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

@[grind]
theorem exportsd_is_wf :
    ∀ (var_0_lst : (List decl)) (ret_val_lst : (List «export»)) (var_0 : (List «export»)), (fun_exportsd var_0_lst var_0) →
    Forall (fun (var_0 : decl) => (wf_decl var_0)) var_0_lst →
    (ret_val_lst = var_0) →
    Forall (fun (ret_val : «export») => (wf_export ret_val)) ret_val_lst := by
  intro var_0_lst ret_val_lst var_0 h0 h1 h2
  subst_vars
  first
    | ((try revert h2); (try revert h1); induction h0 <;> intros <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))
    | (cases h0 <;> (subst_vars; first | (simp_all [Forall]; done) | (simp_all [Forall] <;> grind [Forall]) | grind [Forall] | ((repeat' constructor) <;> (first | assumption | (simp_all [Forall]; done) | omega | decide); done)))

def allocX_is_wf : Prop :=
  ∀ (r_X : Type 0) [Inhabited r_X] (Y : Type 0) [Inhabited Y] (v_store : store) (X_0 : r_X) (Y_0 : Y) (ret_val : (store × addr)), (wf_store v_store) →
    (ret_val = (allocX r_X Y v_store X_0 Y_0)) →
    (wf_store (Prod.fst ret_val))

def allocXs_is_wf : Prop :=
  ∀ (r_X : Type 0) [Inhabited r_X] (Y : Type 0) [Inhabited Y] (v_store : store) (var_0_lst : (List r_X)) (var_1_lst : (List Y)) (ret_val : (store × (List addr))), (wf_store v_store) →
    (ret_val = (allocXs r_X Y v_store var_0_lst var_1_lst)) →
    (wf_store (Prod.fst ret_val))

def instrdots_is_wf : Prop :=
  ∀ (ret_val_lst : (List instr)), (ret_val_lst = (instrdots )) →
    Forall (fun (ret_val : instr) => (wf_instr ret_val)) ret_val_lst
