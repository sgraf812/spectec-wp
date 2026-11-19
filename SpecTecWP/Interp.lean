import SpecTecWP.Wasm

set_option linter.unusedVariables false

/- Prelude of the interpreter -/

/-- The splits of a list into a prefix and a suffix. -/
def interp_splits {α : Type} : (l : List α) → List {p : List α × List α // p.1 ++ p.2 = l}
  | [] => [⟨([], []), rfl⟩]
  | x :: xs => ⟨([], x :: xs), rfl⟩ ::
      (interp_splits xs).map fun ⟨(a, b), h⟩ => ⟨(x :: a, b), by simp [← h]⟩

/-- The inverse of `List.map f`, from an inverse of `f`. -/
def interp_invMap {α β : Type} {f : α → β} (inv : (y : β) → Option {x : α // f x = y}) :
    (l : List β) → Option {xs : List α // List.map (fun x => f x) xs = l}
  | [] => some ⟨[], rfl⟩
  | y :: ys =>
    match inv y, interp_invMap inv ys with
    | some ⟨x, hx⟩, some ⟨xs, hxs⟩ => some ⟨x :: xs, by simp [hx, ← hxs]⟩
    | _, _ => none

/-- A proof of `Forall R xs`, from proofs of `R x` for each element. -/
def interp_allL {α : Type} {R : α → Prop} (f : (x : α) → List {_u : Unit // R x}) :
    (xs : List α) → List {_u : Unit // Forall R xs}
  | [] => [⟨(), fun _ h => by cases h⟩]
  | x :: xs =>
    match f x, interp_allL f xs with
    | ⟨_, hx⟩ :: _, ⟨_, hxs⟩ :: _ => [⟨(), fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hxs y hy⟩]
    | _, _ => []

def interp_inv_instr_val (y : instr) : Option {x : val // instr_val x = y} :=
  match y with
  | (.CONST x0 x1) => some ⟨(.CONST x0 x1), rfl⟩
  | (.VCONST x0 x1) => some ⟨(.VCONST x0 x1), rfl⟩
  | (.REF_I31_NUM x0) => some ⟨(.REF_I31_NUM x0), rfl⟩
  | .REF_NULL_ADDR => some ⟨.REF_NULL_ADDR, rfl⟩
  | (.REF_STRUCT_ADDR x0) => some ⟨(.REF_STRUCT_ADDR x0), rfl⟩
  | (.REF_ARRAY_ADDR x0) => some ⟨(.REF_ARRAY_ADDR x0), rfl⟩
  | (.REF_FUNC_ADDR x0) => some ⟨(.REF_FUNC_ADDR x0), rfl⟩
  | (.REF_EXN_ADDR x0) => some ⟨(.REF_EXN_ADDR x0), rfl⟩
  | (.REF_HOST_ADDR x0) => some ⟨(.REF_HOST_ADDR x0), rfl⟩
  | (.REF_EXTERN x0) => some ⟨(.REF_EXTERN x0), rfl⟩
  | _ => none

def interp_inv_instr_ref (y : instr) : Option {x : ref // instr_ref x = y} :=
  match y with
  | (.REF_I31_NUM x0) => some ⟨(.REF_I31_NUM x0), rfl⟩
  | .REF_NULL_ADDR => some ⟨.REF_NULL_ADDR, rfl⟩
  | (.REF_STRUCT_ADDR x0) => some ⟨(.REF_STRUCT_ADDR x0), rfl⟩
  | (.REF_ARRAY_ADDR x0) => some ⟨(.REF_ARRAY_ADDR x0), rfl⟩
  | (.REF_FUNC_ADDR x0) => some ⟨(.REF_FUNC_ADDR x0), rfl⟩
  | (.REF_EXN_ADDR x0) => some ⟨(.REF_EXN_ADDR x0), rfl⟩
  | (.REF_HOST_ADDR x0) => some ⟨(.REF_HOST_ADDR x0), rfl⟩
  | (.REF_EXTERN x0) => some ⟨(.REF_EXTERN x0), rfl⟩
  | _ => none

def interp_cand_proj_num__0 (y : iN) : List num_ :=
  (match y with
 | var_x => ([.I32, .I64] : List Inn).flatMap fun v_Inn => [(.mk_num__0 v_Inn var_x)])

def interp_inv_lanetype_numtype (y : lanetype) : Option {x : numtype // lanetype_numtype x = y} :=
  match y with
  | .I32 => some ⟨.I32, rfl⟩
  | .I64 => some ⟨.I64, rfl⟩
  | .F32 => some ⟨.F32, rfl⟩
  | .F64 => some ⟨.F64, rfl⟩
  | _ => none

def interp_inv_lanetype_packtype (y : lanetype) : Option {x : packtype // lanetype_packtype x = y} :=
  match y with
  | .I8 => some ⟨.I8, rfl⟩
  | .I16 => some ⟨.I16, rfl⟩
  | _ => none

def interp_inv_numtype_addrtype (y : numtype) : Option {x : addrtype // numtype_addrtype x = y} :=
  match y with
  | .I32 => some ⟨.I32, rfl⟩
  | .I64 => some ⟨.I64, rfl⟩
  | _ => none

def interp_inv_heaptype_deftype (y : heaptype) : Option {x : deftype // heaptype_deftype x = y} :=
  match y with
  | (._DEF x0 x1) => some ⟨(._DEF x0 x1), rfl⟩
  | _ => none

def interp_inv_heaptype_absheaptype (y : heaptype) : Option {x : absheaptype // heaptype_absheaptype x = y} :=
  match y with
  | .ANY => some ⟨.ANY, rfl⟩
  | .EQ => some ⟨.EQ, rfl⟩
  | .I31 => some ⟨.I31, rfl⟩
  | .STRUCT => some ⟨.STRUCT, rfl⟩
  | .ARRAY => some ⟨.ARRAY, rfl⟩
  | .NONE => some ⟨.NONE, rfl⟩
  | .FUNC => some ⟨.FUNC, rfl⟩
  | .NOFUNC => some ⟨.NOFUNC, rfl⟩
  | .EXN => some ⟨.EXN, rfl⟩
  | .NOEXN => some ⟨.NOEXN, rfl⟩
  | .EXTERN => some ⟨.EXTERN, rfl⟩
  | .NOEXTERN => some ⟨.NOEXTERN, rfl⟩
  | .BOT => some ⟨.BOT, rfl⟩
  | _ => none

def interp_inv_heaptype_typeuse (y : heaptype) : Option {x : typeuse // heaptype_typeuse x = y} :=
  match y with
  | (._IDX x0) => some ⟨(._IDX x0), rfl⟩
  | (._DEF x0 x1) => some ⟨(._DEF x0 x1), rfl⟩
  | (.REC x0) => some ⟨(.REC x0), rfl⟩
  | _ => none

def interp_inv_typeuse_deftype (y : typeuse) : Option {x : deftype // typeuse_deftype x = y} :=
  match y with
  | (._DEF x0 x1) => some ⟨(._DEF x0 x1), rfl⟩
  | _ => none

def interp_inv_storagetype_valtype (y : storagetype) : Option {x : valtype // storagetype_valtype x = y} :=
  match y with
  | .I32 => some ⟨.I32, rfl⟩
  | .I64 => some ⟨.I64, rfl⟩
  | .F32 => some ⟨.F32, rfl⟩
  | .F64 => some ⟨.F64, rfl⟩
  | .V128 => some ⟨.V128, rfl⟩
  | (.REF x0 x1) => some ⟨(.REF x0 x1), rfl⟩
  | .BOT => some ⟨.BOT, rfl⟩
  | _ => none

def interp_inv_storagetype_packtype (y : storagetype) : Option {x : packtype // storagetype_packtype x = y} :=
  match y with
  | .I8 => some ⟨.I8, rfl⟩
  | .I16 => some ⟨.I16, rfl⟩
  | _ => none

def interp_inv_valtype_numtype (y : valtype) : Option {x : numtype // valtype_numtype x = y} :=
  match y with
  | .I32 => some ⟨.I32, rfl⟩
  | .I64 => some ⟨.I64, rfl⟩
  | .F32 => some ⟨.F32, rfl⟩
  | .F64 => some ⟨.F64, rfl⟩
  | _ => none

def interp_inv_valtype_vectype (y : valtype) : Option {x : vectype // valtype_vectype x = y} :=
  match y with
  | .V128 => some ⟨.V128, rfl⟩
  | _ => none

def interp_inv_valtype_reftype (y : valtype) : Option {x : reftype // valtype_reftype x = y} :=
  match y with
  | (.REF x0 x1) => some ⟨(.REF x0 x1), rfl⟩
  | _ => none

def interp_wf_fNmag_ii_fNmag_case_0 (a0 : N) (a1 : fNmag) : List {o : Unit // (wf_fNmag a0 a1)} :=
  match a0, a1 with
 | v_N, (.NORM v_m v_exp) => ((if h_4605 : (v_m < (2 ^ (fun_M v_N))) then
((if h_4606 : (((Int.ofNat 2) - (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat (E v_N)) - (Int.ofNat 1)))))) <= v_exp) then
((if h_4607 : (v_exp <= ((Int.ofNat (2 ^ (Int.toNat ((Int.ofNat (E v_N)) - (Int.ofNat 1))))) - (Int.ofNat 1))) then
((if h_4608 : (0 ≤ ((Int.ofNat (E v_N)) - (Int.ofNat 1))) then
([⟨(), by subst_vars; first | (apply wf_fNmag.fNmag_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fNmag.fNmag_case_0]⟩])
else []))
else []))
else []))
else []))
 | _, _ => []

def interp_wf_fNmag_ii_fNmag_case_1 (a0 : N) (a1 : fNmag) : List {o : Unit // (wf_fNmag a0 a1)} :=
  match a0, a1 with
 | v_N, (.SUBNORM v_m) => ((if h_4609 : (v_m < (2 ^ (fun_M v_N))) then
(((fun (v_exp : exp) (h_4610 : (((Int.ofNat 2) - (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat (E v_N)) - (Int.ofNat 1)))))) : exp) = v_exp) => ((if h_4611 : (0 ≤ ((Int.ofNat (E v_N)) - (Int.ofNat 1))) then
([⟨(), by subst_vars; first | (apply wf_fNmag.fNmag_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fNmag.fNmag_case_1]⟩])
else []))) (((Int.ofNat 2) - (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat (E v_N)) - (Int.ofNat 1)))))) : exp) rfl))
else []))
 | _, _ => []

def interp_wf_fNmag_ii_fNmag_case_2 (a0 : N) (a1 : fNmag) : List {o : Unit // (wf_fNmag a0 a1)} :=
  match a0, a1 with
 | v_N, .INF => ([⟨(), by subst_vars; first | (apply wf_fNmag.fNmag_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fNmag.fNmag_case_2]⟩])
 | _, _ => []

def interp_wf_fNmag_ii_fNmag_case_3 (a0 : N) (a1 : fNmag) : List {o : Unit // (wf_fNmag a0 a1)} :=
  match a0, a1 with
 | v_N, (.NAN v_m) => ((if h_4612 : (1 <= v_m) then
((if h_4613 : (v_m < (2 ^ (fun_M v_N))) then
([⟨(), by subst_vars; first | (apply wf_fNmag.fNmag_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fNmag.fNmag_case_3]⟩])
else []))
else []))
 | _, _ => []

def interp_wf_fNmag_ii (a0 : N) (a1 : fNmag) : List {o : Unit // (wf_fNmag a0 a1)} :=
  interp_wf_fNmag_ii_fNmag_case_0 a0 a1 ++
  interp_wf_fNmag_ii_fNmag_case_1 a0 a1 ++
  interp_wf_fNmag_ii_fNmag_case_2 a0 a1 ++
  interp_wf_fNmag_ii_fNmag_case_3 a0 a1

def interp_wf_fN_ii_fN_case_0 (a0 : N) (a1 : fN) : List {o : Unit // (wf_fN a0 a1)} :=
  match a0, a1 with
 | v_N, (.POS var_0) => (((interp_wf_fNmag_ii (v_N) (var_0)).flatMap fun ⟨_, h_4247⟩ => ([⟨(), by subst_vars; first | (apply wf_fN.fN_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fN.fN_case_0]⟩])))
 | _, _ => []

def interp_wf_fN_ii_fN_case_1 (a0 : N) (a1 : fN) : List {o : Unit // (wf_fN a0 a1)} :=
  match a0, a1 with
 | v_N, (.NEG var_0) => (((interp_wf_fNmag_ii (v_N) (var_0)).flatMap fun ⟨_, h_4248⟩ => ([⟨(), by subst_vars; first | (apply wf_fN.fN_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fN.fN_case_1]⟩])))
 | _, _ => []

def interp_wf_fN_ii (a0 : N) (a1 : fN) : List {o : Unit // (wf_fN a0 a1)} :=
  interp_wf_fN_ii_fN_case_0 a0 a1 ++
  interp_wf_fN_ii_fN_case_1 a0 a1

def interp_fun_fzero_io_fun_fzero_case_0 (a0 : N) : List {o : fN // (fun_fzero a0 o)} :=
  match a0 with
 | v_N => (((interp_wf_fN_ii (v_N) ((.POS (.SUBNORM 0)))).flatMap fun ⟨_, h_4615⟩ => ([⟨(.POS (.SUBNORM 0)), by subst_vars; first | (apply fun_fzero.fun_fzero_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_fzero.fun_fzero_case_0]⟩])))

def interp_fun_fzero_io (a0 : N) : List {o : fN // (fun_fzero a0 o)} :=
  interp_fun_fzero_io_fun_fzero_case_0 a0

def interp_fun_zero_io_fun_zero_case_0 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .I32 => ([⟨(.mk_lane__0 .I32 (.mk_uN 0)), by subst_vars; first | (apply fun_zero.fun_zero_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_0]⟩])
 | _ => []

def interp_fun_zero_io_fun_zero_case_1 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .I64 => ([⟨(.mk_lane__0 .I64 (.mk_uN 0)), by subst_vars; first | (apply fun_zero.fun_zero_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_1]⟩])
 | _ => []

def interp_fun_zero_io_fun_zero_case_2 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .I8 => ([⟨(.mk_lane__0 .I8 (.mk_uN 0)), by subst_vars; first | (apply fun_zero.fun_zero_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_2]⟩])
 | _ => []

def interp_fun_zero_io_fun_zero_case_3 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .I16 => ([⟨(.mk_lane__0 .I16 (.mk_uN 0)), by subst_vars; first | (apply fun_zero.fun_zero_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_3]⟩])
 | _ => []

def interp_fun_zero_io_fun_zero_case_4 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .F32 => (((interp_fun_fzero_io ((size (numtype_Fnn .F32)))).flatMap fun ⟨o_353, h_4468⟩ => (match o_353 with
 | var_0 => ([⟨(.mk_lane__1 .F32 var_0), by subst_vars; first | (apply fun_zero.fun_zero_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_4]⟩]))))
 | _ => []

def interp_fun_zero_io_fun_zero_case_5 (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  match a0 with
 | .F64 => (((interp_fun_fzero_io ((size (numtype_Fnn .F64)))).flatMap fun ⟨o_354, h_4469⟩ => (match o_354 with
 | var_0 => ([⟨(.mk_lane__1 .F64 var_0), by subst_vars; first | (apply fun_zero.fun_zero_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zero.fun_zero_case_5]⟩]))))
 | _ => []

def interp_fun_zero_io (a0 : lanetype) : List {o : lane_ // (fun_zero a0 o)} :=
  interp_fun_zero_io_fun_zero_case_0 a0 ++
  interp_fun_zero_io_fun_zero_case_1 a0 ++
  interp_fun_zero_io_fun_zero_case_2 a0 ++
  interp_fun_zero_io_fun_zero_case_3 a0 ++
  interp_fun_zero_io_fun_zero_case_4 a0 ++
  interp_fun_zero_io_fun_zero_case_5 a0

def interp_wf_dim_i_dim_case_0 (a0 : dim) : List {o : Unit // (wf_dim a0)} :=
  match a0 with
 | (.mk_dim i) => ((if h_4273 : (((((i = 1) ∨ (i = 2)) ∨ (i = 4)) ∨ (i = 8)) ∨ (i = 16)) then
([⟨(), by subst_vars; first | (apply wf_dim.dim_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_dim.dim_case_0]⟩])
else []))

def interp_wf_dim_i (a0 : dim) : List {o : Unit // (wf_dim a0)} :=
  interp_wf_dim_i_dim_case_0 a0

def interp_wf_shape_i_shape_case_0 (a0 : shape) : List {o : Unit // (wf_shape a0)} :=
  match a0 with
 | (.X v_lanetype v_dim) => ((if h_1320 : (((lsize v_lanetype) * (proj_dim_0 v_dim)) = 128) then
(((interp_wf_dim_i (v_dim)).flatMap fun ⟨_, h_1321⟩ => ([⟨(), by subst_vars; first | (apply wf_shape.shape_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_shape.shape_case_0]⟩])))
else []))

def interp_wf_shape_i (a0 : shape) : List {o : Unit // (wf_shape a0)} :=
  interp_wf_shape_i_shape_case_0 a0

def interp_fun_halfop_iiio_fun_halfop_case_0 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4387 : (M_1 = M_1_0) then
((if h_4388 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_0]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_1 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4389 : (M_1 = M_1_0) then
((if h_4390 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_1]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_2 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4391 : (M_1 = M_1_0) then
((if h_4392 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_2]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_3 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4393 : (M_1 = M_1_0) then
((if h_4394 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_3]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_4 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4395 : (M_1 = M_1_0) then
((if h_4396 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_4]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_5 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4397 : (M_1 = M_1_0) then
((if h_4398 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_5]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_6 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4399 : (M_1 = M_1_0) then
((if h_4400 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_6]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_7 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4401 : (M_1 = M_1_0) then
((if h_4402 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_7]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_8 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4403 : (M_1 = M_1_0) then
((if h_4404 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_8]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_9 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4405 : (M_1 = M_1_0) then
((if h_4406 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_9]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_10 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4407 : (M_1 = M_1_0) then
((if h_4408 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_10]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_11 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4409 : (M_1 = M_1_0) then
((if h_4410 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_11]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_12 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4411 : (M_1 = M_1_0) then
((if h_4412 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_12]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_13 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4413 : (M_1 = M_1_0) then
((if h_4414 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_13]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_14 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4415 : (M_1 = M_1_0) then
((if h_4416 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_14]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_15 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4417 : (M_1 = M_1_0) then
((if h_4418 : (M_2 = M_2_0) then
([⟨(some (some v_half)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_15]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_16 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I32 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4419 : (M_1 = M_1_0) then
((if h_4420 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_16]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_17 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I64 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4421 : (M_1 = M_1_0) then
((if h_4422 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_17]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_18 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I8 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4423 : (M_1 = M_1_0) then
((if h_4424 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_18]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_19 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I16 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4425 : (M_1 = M_1_0) then
((if h_4426 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_19]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_20 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I32 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4427 : (M_1 = M_1_0) then
((if h_4428 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_20]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_21 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I64 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4429 : (M_1 = M_1_0) then
((if h_4430 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_21]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_22 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I8 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4431 : (M_1 = M_1_0) then
((if h_4432 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_22]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_23 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I16 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4433 : (M_1 = M_1_0) then
((if h_4434 : (M_2 = M_2_0) then
([⟨(some half_opt), by subst_vars; first | (apply fun_halfop.fun_halfop_case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_23]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_24 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I32 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4435 : (M_1 = M_1_0) then
((if h_4436 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_24]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_25 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I32 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4437 : (M_1 = M_1_0) then
((if h_4438 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_25]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_26 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I64 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4439 : (M_1 = M_1_0) then
((if h_4440 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_26]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_27 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I64 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4441 : (M_1 = M_1_0) then
((if h_4442 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_27]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_28 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I32 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4443 : (M_1 = M_1_0) then
((if h_4444 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_28]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_29 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I32 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4445 : (M_1 = M_1_0) then
((if h_4446 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_29]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_30 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I64 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4447 : (M_1 = M_1_0) then
((if h_4448 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_30]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_31 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I64 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4449 : (M_1 = M_1_0) then
((if h_4450 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_31]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_32 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F32 M_2_0 (.DEMOTE v_zero)) => ((if h_4451 : (M_1 = M_1_0) then
((if h_4452 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_32]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_33 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F32 M_2_0 (.DEMOTE v_zero)) => ((if h_4453 : (M_1 = M_1_0) then
((if h_4454 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_33]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_34 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F64 M_2_0 (.DEMOTE v_zero)) => ((if h_4455 : (M_1 = M_1_0) then
((if h_4456 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_34]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_35 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F64 M_2_0 (.DEMOTE v_zero)) => ((if h_4457 : (M_1 = M_1_0) then
((if h_4458 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_halfop.fun_halfop_case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_35]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_36 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F32 M_2_0 .PROMOTELOW) => ((if h_4459 : (M_1 = M_1_0) then
((if h_4460 : (M_2 = M_2_0) then
([⟨(some (some .LOW)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_36]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_37 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F32 M_2_0 .PROMOTELOW) => ((if h_4461 : (M_1 = M_1_0) then
((if h_4462 : (M_2 = M_2_0) then
([⟨(some (some .LOW)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_37]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_38 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F64 M_2_0 .PROMOTELOW) => ((if h_4463 : (M_1 = M_1_0) then
((if h_4464 : (M_2 = M_2_0) then
([⟨(some (some .LOW)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_38 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_38]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio_fun_halfop_case_39 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F64 M_2_0 .PROMOTELOW) => ((if h_4465 : (M_1 = M_1_0) then
((if h_4466 : (M_2 = M_2_0) then
([⟨(some (some .LOW)), by subst_vars; first | (apply fun_halfop.fun_halfop_case_39 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_halfop.fun_halfop_case_39]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_halfop_iiio (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option half)) // (fun_halfop a0 a1 a2 o)} :=
  interp_fun_halfop_iiio_fun_halfop_case_0 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_1 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_2 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_3 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_4 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_5 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_6 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_7 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_8 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_9 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_10 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_11 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_12 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_13 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_14 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_15 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_16 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_17 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_18 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_19 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_20 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_21 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_22 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_23 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_24 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_25 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_26 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_27 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_28 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_29 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_30 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_31 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_32 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_33 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_34 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_35 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_36 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_37 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_38 a0 a1 a2 ++
  interp_fun_halfop_iiio_fun_halfop_case_39 a0 a1 a2

def interp_fun_zeroop_iiio_fun_zeroop_case_0 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4306 : (M_1 = M_1_0) then
((if h_4307 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_0]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_1 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4308 : (M_1 = M_1_0) then
((if h_4309 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_1]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_2 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4310 : (M_1 = M_1_0) then
((if h_4311 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_2]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_3 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I32 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4312 : (M_1 = M_1_0) then
((if h_4313 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_3]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_4 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4314 : (M_1 = M_1_0) then
((if h_4315 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_4]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_5 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4316 : (M_1 = M_1_0) then
((if h_4317 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_5]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_6 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4318 : (M_1 = M_1_0) then
((if h_4319 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_6]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_7 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I64 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4320 : (M_1 = M_1_0) then
((if h_4321 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_7]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_8 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4322 : (M_1 = M_1_0) then
((if h_4323 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_8]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_9 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4324 : (M_1 = M_1_0) then
((if h_4325 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_9]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_10 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4326 : (M_1 = M_1_0) then
((if h_4327 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_10]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_11 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I8 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4328 : (M_1 = M_1_0) then
((if h_4329 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_11]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_12 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I32 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4330 : (M_1 = M_1_0) then
((if h_4331 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_12]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_13 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I64 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4332 : (M_1 = M_1_0) then
((if h_4333 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_13]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_14 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I8 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4334 : (M_1 = M_1_0) then
((if h_4335 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_14]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_15 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), (.mk_vcvtop___0 .I16 M_1_0 .I16 M_2_0 (.EXTEND v_half v_sx)) => ((if h_4336 : (M_1 = M_1_0) then
((if h_4337 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_15]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_16 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I32 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4338 : (M_1 = M_1_0) then
((if h_4339 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_16]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_17 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I64 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4340 : (M_1 = M_1_0) then
((if h_4341 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_17]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_18 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I8 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4342 : (M_1 = M_1_0) then
((if h_4343 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_18]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_19 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___1 .I16 M_1_0 .F32 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4344 : (M_1 = M_1_0) then
((if h_4345 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_19]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_20 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I32 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4346 : (M_1 = M_1_0) then
((if h_4347 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_20]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_21 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I64 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4348 : (M_1 = M_1_0) then
((if h_4349 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_21]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_22 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I8 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4350 : (M_1 = M_1_0) then
((if h_4351 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_22]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_23 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___1 .I16 M_1_0 .F64 M_2_0 (.CONVERT half_opt v_sx)) => ((if h_4352 : (M_1 = M_1_0) then
((if h_4353 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_23]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_24 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I32 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4354 : (M_1 = M_1_0) then
((if h_4355 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_24]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_25 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I32 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4356 : (M_1 = M_1_0) then
((if h_4357 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_25]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_26 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I64 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4358 : (M_1 = M_1_0) then
((if h_4359 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_26]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_27 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I64 M_2_0 (.TRUNC_SAT v_sx zero_opt)) => ((if h_4360 : (M_1 = M_1_0) then
((if h_4361 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_27]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_28 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I32 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4362 : (M_1 = M_1_0) then
((if h_4363 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_28]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_29 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I32 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4364 : (M_1 = M_1_0) then
((if h_4365 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_29]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_30 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F32 M_1_0 .I64 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4366 : (M_1 = M_1_0) then
((if h_4367 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_30]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_31 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), (.mk_vcvtop___2 .F64 M_1_0 .I64 M_2_0 (.RELAXED_TRUNC v_sx zero_opt)) => ((if h_4368 : (M_1 = M_1_0) then
((if h_4369 : (M_2 = M_2_0) then
([⟨(some zero_opt), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_31]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_32 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F32 M_2_0 (.DEMOTE v_zero)) => ((if h_4370 : (M_1 = M_1_0) then
((if h_4371 : (M_2 = M_2_0) then
([⟨(some (some v_zero)), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_32]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_33 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F32 M_2_0 (.DEMOTE v_zero)) => ((if h_4372 : (M_1 = M_1_0) then
((if h_4373 : (M_2 = M_2_0) then
([⟨(some (some v_zero)), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_33]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_34 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F64 M_2_0 (.DEMOTE v_zero)) => ((if h_4374 : (M_1 = M_1_0) then
((if h_4375 : (M_2 = M_2_0) then
([⟨(some (some v_zero)), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_34]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_35 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F64 M_2_0 (.DEMOTE v_zero)) => ((if h_4376 : (M_1 = M_1_0) then
((if h_4377 : (M_2 = M_2_0) then
([⟨(some (some v_zero)), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_35]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_36 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F32 M_2_0 .PROMOTELOW) => ((if h_4378 : (M_1 = M_1_0) then
((if h_4379 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_36]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_37 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F32 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F32 M_2_0 .PROMOTELOW) => ((if h_4380 : (M_1 = M_1_0) then
((if h_4381 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_37]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_38 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F32 M_1_0 .F64 M_2_0 .PROMOTELOW) => ((if h_4382 : (M_1 = M_1_0) then
((if h_4383 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_38 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_38]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio_fun_zeroop_case_39 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim M_1)), (.X .F64 (.mk_dim M_2)), (.mk_vcvtop___3 .F64 M_1_0 .F64 M_2_0 .PROMOTELOW) => ((if h_4384 : (M_1 = M_1_0) then
((if h_4385 : (M_2 = M_2_0) then
([⟨(some none), by subst_vars; first | (apply fun_zeroop.fun_zeroop_case_39 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_zeroop.fun_zeroop_case_39]⟩])
else []))
else []))
 | _, _, _ => []

def interp_fun_zeroop_iiio (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : (Option (Option zero)) // (fun_zeroop a0 a1 a2 o)} :=
  interp_fun_zeroop_iiio_fun_zeroop_case_0 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_1 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_2 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_3 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_4 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_5 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_6 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_7 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_8 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_9 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_10 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_11 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_12 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_13 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_14 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_15 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_16 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_17 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_18 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_19 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_20 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_21 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_22 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_23 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_24 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_25 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_26 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_27 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_28 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_29 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_30 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_31 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_32 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_33 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_34 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_35 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_36 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_37 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_38 a0 a1 a2 ++
  interp_fun_zeroop_iiio_fun_zeroop_case_39 a0 a1 a2

def interp_fun_vcvtop___iiiio (a0 : shape) (a1 : shape) (a2 : vcvtop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vcvtop__ a0 a1 a2 a3 o)} :=
  []

def interp_wf_uN_ii_uN_case_0 (a0 : N) (a1 : uN) : List {o : Unit // (wf_uN a0 a1)} :=
  match a0, a1 with
 | v_N, (.mk_uN i) => ((if h_1210 : (i >= 0) then
((if h_1211 : (i <= (Int.toNat ((Int.ofNat (2 ^ v_N)) - (Int.ofNat 1)))) then
((if h_1212 : (0 ≤ ((Int.ofNat (2 ^ v_N)) - (Int.ofNat 1))) then
([⟨(), by subst_vars; first | (apply wf_uN.uN_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_uN.uN_case_0]⟩])
else []))
else []))
else []))

def interp_wf_uN_ii (a0 : N) (a1 : uN) : List {o : Unit // (wf_uN a0 a1)} :=
  interp_wf_uN_ii_uN_case_0 a0 a1

def interp_wf_lane__ii_lane__case_0 (a0 : lanetype) (a1 : lane_) : List {o : Unit // (wf_lane_ a0 a1)} :=
  match a0, a1 with
 | v_lanetype, (.mk_lane__0 v_Jnn var_x) => ((if h_1383 : (v_lanetype = (lanetype_Jnn v_Jnn)) then
(((interp_wf_uN_ii ((lsize (lanetype_Jnn v_Jnn))) (var_x)).flatMap fun ⟨_, h_1384⟩ => ([⟨(), by subst_vars; first | (apply wf_lane_.lane__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_lane_.lane__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_lane__ii_lane__case_1 (a0 : lanetype) (a1 : lane_) : List {o : Unit // (wf_lane_ a0 a1)} :=
  match a0, a1 with
 | v_lanetype, (.mk_lane__1 v_Fnn var_x) => ((if h_1385 : (v_lanetype = (lanetype_Fnn v_Fnn)) then
(((interp_wf_fN_ii ((sizenn (numtype_Fnn v_Fnn))) (var_x)).flatMap fun ⟨_, h_1386⟩ => ([⟨(), by subst_vars; first | (apply wf_lane_.lane__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_lane_.lane__case_1]⟩])))
else []))
 | _, _ => []

def interp_wf_lane__ii (a0 : lanetype) (a1 : lane_) : List {o : Unit // (wf_lane_ a0 a1)} :=
  interp_wf_lane__ii_lane__case_0 a0 a1 ++
  interp_wf_lane__ii_lane__case_1 a0 a1

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_0 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I32 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2430 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2431 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2432 : ((List.map (fun (c_1_148 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_148)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2433 : ((List.map (fun (c_2_100 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_100)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2434 : ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_2 : iN) => ((.mk_lane__0 .I32 c'_1_2) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_2 : iN) => ((.mk_lane__0 .I32 c'_2_2) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_1)))).flatMap fun ⟨_, h_2435⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_2)))).flatMap fun ⟨_, h_2436⟩ => (((interp_allL (fun (c'_1_3 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_1_3)))) c'_1_lst).flatMap fun ⟨_, h_2437⟩ => (((interp_allL (fun (c'_2_3 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_2_3)))) c'_2_lst).flatMap fun ⟨_, h_2438⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_0]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_2 : iN) => ((.mk_lane__0 .I32 c'_1_2) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_2 : iN) => ((.mk_lane__0 .I32 c'_2_2) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_100 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_100)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_148 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_148)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_1 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I64 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2439 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2440 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2441 : ((List.map (fun (c_1_150 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_150)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2442 : ((List.map (fun (c_2_102 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_102)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2443 : ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_5 : iN) => ((.mk_lane__0 .I32 c'_1_5) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_5 : iN) => ((.mk_lane__0 .I32 c'_2_5) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_1)))).flatMap fun ⟨_, h_2444⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_2)))).flatMap fun ⟨_, h_2445⟩ => (((interp_allL (fun (c'_1_6 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_1_6)))) c'_1_lst).flatMap fun ⟨_, h_2446⟩ => (((interp_allL (fun (c'_2_6 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_2_6)))) c'_2_lst).flatMap fun ⟨_, h_2447⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_1]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_5 : iN) => ((.mk_lane__0 .I32 c'_1_5) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_5 : iN) => ((.mk_lane__0 .I32 c'_2_5) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_102 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_102)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_150 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_150)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_2 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I8 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2448 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2449 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2450 : ((List.map (fun (c_1_152 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_152)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2451 : ((List.map (fun (c_2_104 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_104)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2452 : ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_8 : iN) => ((.mk_lane__0 .I32 c'_1_8) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_8 : iN) => ((.mk_lane__0 .I32 c'_2_8) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_1)))).flatMap fun ⟨_, h_2453⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_2)))).flatMap fun ⟨_, h_2454⟩ => (((interp_allL (fun (c'_1_9 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_1_9)))) c'_1_lst).flatMap fun ⟨_, h_2455⟩ => (((interp_allL (fun (c'_2_9 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_2_9)))) c'_2_lst).flatMap fun ⟨_, h_2456⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_2]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_8 : iN) => ((.mk_lane__0 .I32 c'_1_8) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_8 : iN) => ((.mk_lane__0 .I32 c'_2_8) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_104 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_104)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_152 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_152)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_3 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I16 (.mk_dim M_1)), (.X .I32 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2457 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2458 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2459 : ((List.map (fun (c_1_154 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_154)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2460 : ((List.map (fun (c_2_106 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_106)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2461 : ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_11 : iN) => ((.mk_lane__0 .I32 c'_1_11) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_11 : iN) => ((.mk_lane__0 .I32 c'_2_11) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_1)))).flatMap fun ⟨_, h_2462⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_2)))).flatMap fun ⟨_, h_2463⟩ => (((interp_allL (fun (c'_1_12 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_1_12)))) c'_1_lst).flatMap fun ⟨_, h_2464⟩ => (((interp_allL (fun (c'_2_12 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2)))) ((.mk_lane__0 .I32 c'_2_12)))) c'_2_lst).flatMap fun ⟨_, h_2465⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_3]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1_11 : iN) => ((.mk_lane__0 .I32 c'_1_11) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_11 : iN) => ((.mk_lane__0 .I32 c'_2_11) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_106 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_2_106)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_154 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__0 c_1_154)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_4 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I32 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2466 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2467 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2468 : ((List.map (fun (c_1_156 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_156)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2469 : ((List.map (fun (c_2_108 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_108)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2470 : ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_14 : iN) => ((.mk_lane__0 .I64 c'_1_14) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_14 : iN) => ((.mk_lane__0 .I64 c'_2_14) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_1)))).flatMap fun ⟨_, h_2471⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_2)))).flatMap fun ⟨_, h_2472⟩ => (((interp_allL (fun (c'_1_15 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_1_15)))) c'_1_lst).flatMap fun ⟨_, h_2473⟩ => (((interp_allL (fun (c'_2_15 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_2_15)))) c'_2_lst).flatMap fun ⟨_, h_2474⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_4]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_14 : iN) => ((.mk_lane__0 .I64 c'_1_14) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_14 : iN) => ((.mk_lane__0 .I64 c'_2_14) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_108 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_108)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_156 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_156)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_5 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I64 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2475 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2476 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2477 : ((List.map (fun (c_1_158 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_158)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2478 : ((List.map (fun (c_2_110 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_110)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2479 : ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_17 : iN) => ((.mk_lane__0 .I64 c'_1_17) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_17 : iN) => ((.mk_lane__0 .I64 c'_2_17) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_1)))).flatMap fun ⟨_, h_2480⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_2)))).flatMap fun ⟨_, h_2481⟩ => (((interp_allL (fun (c'_1_18 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_1_18)))) c'_1_lst).flatMap fun ⟨_, h_2482⟩ => (((interp_allL (fun (c'_2_18 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_2_18)))) c'_2_lst).flatMap fun ⟨_, h_2483⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_5]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_17 : iN) => ((.mk_lane__0 .I64 c'_1_17) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_17 : iN) => ((.mk_lane__0 .I64 c'_2_17) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_110 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_110)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_158 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_158)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_6 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I8 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2484 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2485 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2486 : ((List.map (fun (c_1_160 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_160)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2487 : ((List.map (fun (c_2_112 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_112)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2488 : ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_20 : iN) => ((.mk_lane__0 .I64 c'_1_20) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_20 : iN) => ((.mk_lane__0 .I64 c'_2_20) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_1)))).flatMap fun ⟨_, h_2489⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_2)))).flatMap fun ⟨_, h_2490⟩ => (((interp_allL (fun (c'_1_21 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_1_21)))) c'_1_lst).flatMap fun ⟨_, h_2491⟩ => (((interp_allL (fun (c'_2_21 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_2_21)))) c'_2_lst).flatMap fun ⟨_, h_2492⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_6]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_20 : iN) => ((.mk_lane__0 .I64 c'_1_20) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_20 : iN) => ((.mk_lane__0 .I64 c'_2_20) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_112 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_112)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_160 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_160)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_7 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I16 (.mk_dim M_1)), (.X .I64 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2493 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2494 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2495 : ((List.map (fun (c_1_162 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_162)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2496 : ((List.map (fun (c_2_114 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_114)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2497 : ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_23 : iN) => ((.mk_lane__0 .I64 c'_1_23) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_23 : iN) => ((.mk_lane__0 .I64 c'_2_23) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_1)))).flatMap fun ⟨_, h_2498⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_2)))).flatMap fun ⟨_, h_2499⟩ => (((interp_allL (fun (c'_1_24 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_1_24)))) c'_1_lst).flatMap fun ⟨_, h_2500⟩ => (((interp_allL (fun (c'_2_24 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2)))) ((.mk_lane__0 .I64 c'_2_24)))) c'_2_lst).flatMap fun ⟨_, h_2501⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_7]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1_23 : iN) => ((.mk_lane__0 .I64 c'_1_23) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_23 : iN) => ((.mk_lane__0 .I64 c'_2_23) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_114 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_2_114)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_162 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__0 c_1_162)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_8 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I32 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2502 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2503 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2504 : ((List.map (fun (c_1_164 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_164)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2505 : ((List.map (fun (c_2_116 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_116)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2506 : ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_26 : iN) => ((.mk_lane__0 .I8 c'_1_26) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_26 : iN) => ((.mk_lane__0 .I8 c'_2_26) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_1)))).flatMap fun ⟨_, h_2507⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_2)))).flatMap fun ⟨_, h_2508⟩ => (((interp_allL (fun (c'_1_27 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_1_27)))) c'_1_lst).flatMap fun ⟨_, h_2509⟩ => (((interp_allL (fun (c'_2_27 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_2_27)))) c'_2_lst).flatMap fun ⟨_, h_2510⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_8]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_26 : iN) => ((.mk_lane__0 .I8 c'_1_26) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_26 : iN) => ((.mk_lane__0 .I8 c'_2_26) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_116 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_116)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_164 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_164)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_9 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I64 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2511 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2512 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2513 : ((List.map (fun (c_1_166 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_166)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2514 : ((List.map (fun (c_2_118 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_118)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2515 : ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_29 : iN) => ((.mk_lane__0 .I8 c'_1_29) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_29 : iN) => ((.mk_lane__0 .I8 c'_2_29) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_1)))).flatMap fun ⟨_, h_2516⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_2)))).flatMap fun ⟨_, h_2517⟩ => (((interp_allL (fun (c'_1_30 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_1_30)))) c'_1_lst).flatMap fun ⟨_, h_2518⟩ => (((interp_allL (fun (c'_2_30 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_2_30)))) c'_2_lst).flatMap fun ⟨_, h_2519⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_9]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_29 : iN) => ((.mk_lane__0 .I8 c'_1_29) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_29 : iN) => ((.mk_lane__0 .I8 c'_2_29) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_118 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_118)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_166 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_166)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_10 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I8 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2520 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2521 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2522 : ((List.map (fun (c_1_168 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_168)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2523 : ((List.map (fun (c_2_120 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_120)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2524 : ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_32 : iN) => ((.mk_lane__0 .I8 c'_1_32) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_32 : iN) => ((.mk_lane__0 .I8 c'_2_32) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_1)))).flatMap fun ⟨_, h_2525⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_2)))).flatMap fun ⟨_, h_2526⟩ => (((interp_allL (fun (c'_1_33 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_1_33)))) c'_1_lst).flatMap fun ⟨_, h_2527⟩ => (((interp_allL (fun (c'_2_33 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_2_33)))) c'_2_lst).flatMap fun ⟨_, h_2528⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_10]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_32 : iN) => ((.mk_lane__0 .I8 c'_1_32) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_32 : iN) => ((.mk_lane__0 .I8 c'_2_32) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_120 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_120)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_168 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_168)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_11 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I16 (.mk_dim M_1)), (.X .I8 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2529 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2530 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2531 : ((List.map (fun (c_1_170 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_170)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2532 : ((List.map (fun (c_2_122 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_122)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2533 : ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_35 : iN) => ((.mk_lane__0 .I8 c'_1_35) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_35 : iN) => ((.mk_lane__0 .I8 c'_2_35) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_1)))).flatMap fun ⟨_, h_2534⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_2)))).flatMap fun ⟨_, h_2535⟩ => (((interp_allL (fun (c'_1_36 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_1_36)))) c'_1_lst).flatMap fun ⟨_, h_2536⟩ => (((interp_allL (fun (c'_2_36 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2)))) ((.mk_lane__0 .I8 c'_2_36)))) c'_2_lst).flatMap fun ⟨_, h_2537⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_11]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1_35 : iN) => ((.mk_lane__0 .I8 c'_1_35) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_35 : iN) => ((.mk_lane__0 .I8 c'_2_35) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_122 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_2_122)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_170 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__0 c_1_170)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_12 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I32 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2538 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2539 : ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2540 : ((List.map (fun (c_1_172 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_172)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2541 : ((List.map (fun (c_2_124 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_124)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2542 : ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_38 : iN) => ((.mk_lane__0 .I16 c'_1_38) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_38 : iN) => ((.mk_lane__0 .I16 c'_2_38) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I32) (.mk_dim M_1)))).flatMap fun ⟨_, h_2543⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_2)))).flatMap fun ⟨_, h_2544⟩ => (((interp_allL (fun (c'_1_39 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_1_39)))) c'_1_lst).flatMap fun ⟨_, h_2545⟩ => (((interp_allL (fun (c'_2_39 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_2_39)))) c'_2_lst).flatMap fun ⟨_, h_2546⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_12]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_38 : iN) => ((.mk_lane__0 .I16 c'_1_38) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_38 : iN) => ((.mk_lane__0 .I16 c'_2_38) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_124 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_124)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_172 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_172)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_13 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I64 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2547 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2548 : ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2549 : ((List.map (fun (c_1_174 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_174)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2550 : ((List.map (fun (c_2_126 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_126)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2551 : ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_41 : iN) => ((.mk_lane__0 .I16 c'_1_41) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_41 : iN) => ((.mk_lane__0 .I16 c'_2_41) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I64) (.mk_dim M_1)))).flatMap fun ⟨_, h_2552⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_2)))).flatMap fun ⟨_, h_2553⟩ => (((interp_allL (fun (c'_1_42 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_1_42)))) c'_1_lst).flatMap fun ⟨_, h_2554⟩ => (((interp_allL (fun (c'_2_42 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_2_42)))) c'_2_lst).flatMap fun ⟨_, h_2555⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_13]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_41 : iN) => ((.mk_lane__0 .I16 c'_1_41) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_41 : iN) => ((.mk_lane__0 .I16 c'_2_41) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_126 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_126)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_174 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_174)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_14 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I8 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2556 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2557 : ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2558 : ((List.map (fun (c_1_176 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_176)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2559 : ((List.map (fun (c_2_128 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_128)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2560 : ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_44 : iN) => ((.mk_lane__0 .I16 c'_1_44) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_44 : iN) => ((.mk_lane__0 .I16 c'_2_44) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I8) (.mk_dim M_1)))).flatMap fun ⟨_, h_2561⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_2)))).flatMap fun ⟨_, h_2562⟩ => (((interp_allL (fun (c'_1_45 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_1_45)))) c'_1_lst).flatMap fun ⟨_, h_2563⟩ => (((interp_allL (fun (c'_2_45 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_2_45)))) c'_2_lst).flatMap fun ⟨_, h_2564⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_14]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_44 : iN) => ((.mk_lane__0 .I16 c'_1_44) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_44 : iN) => ((.mk_lane__0 .I16 c'_2_44) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_128 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_128)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_176 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_176)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_15 (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I16 (.mk_dim M_1)), (.X .I16 (.mk_dim M_2)), v_sx, v_1, v_2 => (((fun (c_1_lst : (List lane_)) (h_2565 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) = c_1_lst) => (((fun (c_2_lst : (List lane_)) (h_2566 : ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) = c_2_lst) => (((fun (c'_1_lst : (List iN)) (h_2567 : ((List.map (fun (c_1_178 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_178)))) c_1_lst) : (List iN)) = c'_1_lst) => (((fun (c'_2_lst : (List iN)) (h_2568 : ((List.map (fun (c_2_130 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_130)))) c_2_lst) : (List iN)) = c'_2_lst) => (((fun (v : vec_) (h_2569 : ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_47 : iN) => ((.mk_lane__0 .I16 c'_1_47) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_47 : iN) => ((.mk_lane__0 .I16 c'_2_47) : lane_)) c'_2_lst))) : vec_) = v) => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_1)))).flatMap fun ⟨_, h_2570⟩ => (((interp_wf_shape_i ((.X (lanetype_Jnn .I16) (.mk_dim M_2)))).flatMap fun ⟨_, h_2571⟩ => (((interp_allL (fun (c'_1_48 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_1_48)))) c'_1_lst).flatMap fun ⟨_, h_2572⟩ => (((interp_allL (fun (c'_2_48 : iN) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2)))) ((.mk_lane__0 .I16 c'_2_48)))) c'_2_lst).flatMap fun ⟨_, h_2573⟩ => ([⟨v, by subst_vars; first | (apply fun_vnarrowop__.fun_vnarrowop___case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vnarrowop__.fun_vnarrowop___case_15]⟩])))))))))) ((inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1_47 : iN) => ((.mk_lane__0 .I16 c'_1_47) : lane_)) c'_1_lst) ++ (List.map (fun (c'_2_47 : iN) => ((.mk_lane__0 .I16 c'_2_47) : lane_)) c'_2_lst))) : vec_) rfl))) ((List.map (fun (c_2_130 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_2_130)))) c_2_lst) : (List iN)) rfl))) ((List.map (fun (c_1_178 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__0 c_1_178)))) c_1_lst) : (List iN)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2) : (List lane_)) rfl))) ((lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1) : (List lane_)) rfl))
 | _, _, _, _, _ => []

def interp_fun_vnarrowop___iiiiio (a0 : shape) (a1 : shape) (a2 : sx) (a3 : vec_) (a4 : vec_) : List {o : vec_ // (fun_vnarrowop__ a0 a1 a2 a3 a4 o)} :=
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_0 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_1 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_2 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_3 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_4 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_5 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_6 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_7 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_8 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_9 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_10 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_11 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_12 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_13 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_14 a0 a1 a2 a3 a4 ++
  interp_fun_vnarrowop___iiiiio_fun_vnarrowop___case_15 a0 a1 a2 a3 a4

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_0 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .ADD => ([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_0]⟩])
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_1 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .SUB => ([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_1]⟩])
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_2 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.ADD_SAT v_sx) => ((if h_4571 : ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_2]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_3 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.SUB_SAT v_sx) => ((if h_4572 : ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_3]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_4 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .MUL => ((if h_4573 : ((lsizenn (lanetype_Jnn v_Jnn)) >= 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_4]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_5 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .AVGRU => ((if h_4574 : ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_5]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_6 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .Q15MULR_SATS => ((if h_4575 : ((lsizenn (lanetype_Jnn v_Jnn)) = 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_6]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_7 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .RELAXED_Q15MULRS => ((if h_4576 : ((lsizenn (lanetype_Jnn v_Jnn)) = 16) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_7]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_8 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.MIN v_sx) => ((if h_4577 : ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_8]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_9 (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.MAX v_sx) => ((if h_4578 : ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) then
([⟨(), by subst_vars; first | (apply wf_vbinop_Jnn_M.vbinop_Jnn_M_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_Jnn_M.vbinop_Jnn_M_case_9]⟩])
else []))
 | _, _, _ => []

def interp_wf_vbinop_Jnn_M_iii (a0 : Jnn) (a1 : M) (a2 : vbinop_Jnn_M) : List {o : Unit // (wf_vbinop_Jnn_M a0 a1 a2)} :=
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_0 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_1 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_2 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_3 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_4 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_5 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_6 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_7 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_8 a0 a1 a2 ++
  interp_wf_vbinop_Jnn_M_iii_vbinop_Jnn_M_case_9 a0 a1 a2

def interp_wf_vbinop__ii_vbinop__case_0 (a0 : shape) (a1 : vbinop_) : List {o : Unit // (wf_vbinop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vbinop__0 v_Jnn v_M var_x) => ((if h_4205 : (v_shape = (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) then
(((interp_wf_vbinop_Jnn_M_iii (v_Jnn) (v_M) (var_x)).flatMap fun ⟨_, h_4206⟩ => ([⟨(), by subst_vars; first | (apply wf_vbinop_.vbinop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_.vbinop__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_vbinop__ii_vbinop__case_1 (a0 : shape) (a1 : vbinop_) : List {o : Unit // (wf_vbinop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vbinop__1 v_Fnn v_M var_x) => ((if h_4207 : (v_shape = (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vbinop_.vbinop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vbinop_.vbinop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_vbinop__ii (a0 : shape) (a1 : vbinop_) : List {o : Unit // (wf_vbinop_ a0 a1)} :=
  interp_wf_vbinop__ii_vbinop__case_0 a0 a1 ++
  interp_wf_vbinop__ii_vbinop__case_1 a0 a1

def interp_wf_ishape_i (a0 : ishape) : List {o : Unit // (wf_ishape a0)} :=
  []

def interp_fun_vextternop___iiiiiio (a0 : ishape) (a1 : ishape) (a2 : vextternop__) (a3 : vec_) (a4 : vec_) (a5 : vec_) : List {o : (Option vec_) // (fun_vextternop__ a0 a1 a2 a3 a4 a5 o)} :=
  []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_0 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I32 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1420 : (M_1 = M_1_0) then
((if h_1421 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_0]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_1 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I32 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1422 : (M_1 = M_1_0) then
((if h_1423 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_1]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_2 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I32 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1424 : (M_1 = M_1_0) then
((if h_1425 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_2]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_3 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I32 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1426 : (M_1 = M_1_0) then
((if h_1427 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_3]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_4 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I64 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1428 : (M_1 = M_1_0) then
((if h_1429 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_4]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_5 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I64 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1430 : (M_1 = M_1_0) then
((if h_1431 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_5]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_6 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I64 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1432 : (M_1 = M_1_0) then
((if h_1433 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_6]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_7 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I64 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1434 : (M_1 = M_1_0) then
((if h_1435 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_7]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_8 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I8 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1436 : (M_1 = M_1_0) then
((if h_1437 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_8]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_9 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I8 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1438 : (M_1 = M_1_0) then
((if h_1439 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_9]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_10 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I8 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1440 : (M_1 = M_1_0) then
((if h_1441 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_10]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_11 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I8 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1442 : (M_1 = M_1_0) then
((if h_1443 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_11]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_12 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I16 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1444 : (M_1 = M_1_0) then
((if h_1445 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_12]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_13 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I16 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1446 : (M_1 = M_1_0) then
((if h_1447 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_13]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_14 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I16 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1448 : (M_1 = M_1_0) then
((if h_1449 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_14]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_15 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I16 M_2_0 (.EXTMUL v_half v_sx)), v_1, v_2 => ((if h_1450 : (M_1 = M_1_0) then
((if h_1451 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_15]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_16 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I32 M_2_0 .DOTS), v_1, v_2 => ((if h_1452 : (M_1 = M_1_0) then
((if h_1453 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_16]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_17 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I32 M_2_0 .DOTS), v_1, v_2 => ((if h_1454 : (M_1 = M_1_0) then
((if h_1455 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_17]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_18 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I32 M_2_0 .DOTS), v_1, v_2 => ((if h_1456 : (M_1 = M_1_0) then
((if h_1457 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_18]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_19 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I32 M_2_0 .DOTS), v_1, v_2 => ((if h_1458 : (M_1 = M_1_0) then
((if h_1459 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_19]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_20 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I64 M_2_0 .DOTS), v_1, v_2 => ((if h_1460 : (M_1 = M_1_0) then
((if h_1461 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_20]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_21 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I64 M_2_0 .DOTS), v_1, v_2 => ((if h_1462 : (M_1 = M_1_0) then
((if h_1463 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_21]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_22 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I64 M_2_0 .DOTS), v_1, v_2 => ((if h_1464 : (M_1 = M_1_0) then
((if h_1465 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_22]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_23 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I64 M_2_0 .DOTS), v_1, v_2 => ((if h_1466 : (M_1 = M_1_0) then
((if h_1467 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_23]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_24 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I8 M_2_0 .DOTS), v_1, v_2 => ((if h_1468 : (M_1 = M_1_0) then
((if h_1469 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_24]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_25 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I8 M_2_0 .DOTS), v_1, v_2 => ((if h_1470 : (M_1 = M_1_0) then
((if h_1471 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_25]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_26 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I8 M_2_0 .DOTS), v_1, v_2 => ((if h_1472 : (M_1 = M_1_0) then
((if h_1473 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_26]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_27 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I8 M_2_0 .DOTS), v_1, v_2 => ((if h_1474 : (M_1 = M_1_0) then
((if h_1475 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_27]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_28 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I16 M_2_0 .DOTS), v_1, v_2 => ((if h_1476 : (M_1 = M_1_0) then
((if h_1477 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_28]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_29 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I16 M_2_0 .DOTS), v_1, v_2 => ((if h_1478 : (M_1 = M_1_0) then
((if h_1479 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_29]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_30 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I16 M_2_0 .DOTS), v_1, v_2 => ((if h_1480 : (M_1 = M_1_0) then
((if h_1481 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_30]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_31 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I16 M_2_0 .DOTS), v_1, v_2 => ((if h_1482 : (M_1 = M_1_0) then
((if h_1483 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_31]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_32 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I32 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1484 : (M_1 = M_1_0) then
((if h_1485 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_32]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_33 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I32 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1486 : (M_1 = M_1_0) then
((if h_1487 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_33]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_34 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I32 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1488 : (M_1 = M_1_0) then
((if h_1489 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_34]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_35 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I32 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1490 : (M_1 = M_1_0) then
((if h_1491 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_35]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_36 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I64 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1492 : (M_1 = M_1_0) then
((if h_1493 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_36]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_37 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I64 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1494 : (M_1 = M_1_0) then
((if h_1495 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_37]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_38 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I64 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1496 : (M_1 = M_1_0) then
((if h_1497 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_38 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_38]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_39 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I64 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1498 : (M_1 = M_1_0) then
((if h_1499 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_39 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_39]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_40 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I8 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1500 : (M_1 = M_1_0) then
((if h_1501 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_40 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_40]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_41 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I8 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1502 : (M_1 = M_1_0) then
((if h_1503 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_41 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_41]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_42 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I8 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1504 : (M_1 = M_1_0) then
((if h_1505 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_42 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_42]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_43 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I8 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1506 : (M_1 = M_1_0) then
((if h_1507 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_43 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_43]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_44 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I32 M_1_0 .I16 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1508 : (M_1 = M_1_0) then
((if h_1509 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_44 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_44]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_45 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I64 M_1_0 .I16 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1510 : (M_1 = M_1_0) then
((if h_1511 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_45 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_45]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_46 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I8 M_1_0 .I16 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1512 : (M_1 = M_1_0) then
((if h_1513 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_46 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_46]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio_fun_vextbinop___case_47 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextbinop___0 .I16 M_1_0 .I16 M_2_0 .RELAXED_DOTS), v_1, v_2 => ((if h_1514 : (M_1 = M_1_0) then
((if h_1515 : (M_2 = M_2_0) then
([⟨(some (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)), by subst_vars; first | (apply fun_vextbinop__.fun_vextbinop___case_47 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextbinop__.fun_vextbinop___case_47]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_fun_vextbinop___iiiiio (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) (a3 : vec_) (a4 : vec_) : List {o : (Option vec_) // (fun_vextbinop__ a0 a1 a2 a3 a4 o)} :=
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_0 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_1 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_2 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_3 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_4 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_5 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_6 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_7 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_8 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_9 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_10 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_11 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_12 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_13 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_14 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_15 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_16 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_17 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_18 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_19 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_20 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_21 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_22 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_23 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_24 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_25 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_26 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_27 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_28 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_29 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_30 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_31 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_32 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_33 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_34 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_35 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_36 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_37 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_38 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_39 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_40 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_41 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_42 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_43 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_44 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_45 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_46 a0 a1 a2 a3 a4 ++
  interp_fun_vextbinop___iiiiio_fun_vextbinop___case_47 a0 a1 a2 a3 a4

def interp_fun_vextunop___iiiio_fun_vextunop___case_0 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextunop___0 .I32 M_1_0 .I32 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1387 : (M_1 = M_1_0) then
((if h_1388 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_0]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_1 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextunop___0 .I64 M_1_0 .I32 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1389 : (M_1 = M_1_0) then
((if h_1390 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_1]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_2 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextunop___0 .I8 M_1_0 .I32 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1391 : (M_1 = M_1_0) then
((if h_1392 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_2]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_3 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I32 (.mk_dim M_2))), (.mk_vextunop___0 .I16 M_1_0 .I32 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1393 : (M_1 = M_1_0) then
((if h_1394 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_3]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_4 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextunop___0 .I32 M_1_0 .I64 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1395 : (M_1 = M_1_0) then
((if h_1396 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_4]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_5 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextunop___0 .I64 M_1_0 .I64 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1397 : (M_1 = M_1_0) then
((if h_1398 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_5]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_6 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextunop___0 .I8 M_1_0 .I64 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1399 : (M_1 = M_1_0) then
((if h_1400 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_6]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_7 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I64 (.mk_dim M_2))), (.mk_vextunop___0 .I16 M_1_0 .I64 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1401 : (M_1 = M_1_0) then
((if h_1402 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_7]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_8 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextunop___0 .I32 M_1_0 .I8 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1403 : (M_1 = M_1_0) then
((if h_1404 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_8]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_9 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextunop___0 .I64 M_1_0 .I8 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1405 : (M_1 = M_1_0) then
((if h_1406 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_9]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_10 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextunop___0 .I8 M_1_0 .I8 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1407 : (M_1 = M_1_0) then
((if h_1408 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_10]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_11 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I8 (.mk_dim M_2))), (.mk_vextunop___0 .I16 M_1_0 .I8 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1409 : (M_1 = M_1_0) then
((if h_1410 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_11]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_12 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextunop___0 .I32 M_1_0 .I16 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1411 : (M_1 = M_1_0) then
((if h_1412 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_12]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_13 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextunop___0 .I64 M_1_0 .I16 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1413 : (M_1 = M_1_0) then
((if h_1414 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_13]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_14 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextunop___0 .I8 M_1_0 .I16 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1415 : (M_1 = M_1_0) then
((if h_1416 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_14]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio_fun_vextunop___case_15 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim M_1))), (.mk_ishape (.X .I16 (.mk_dim M_2))), (.mk_vextunop___0 .I16 M_1_0 .I16 M_2_0 (.EXTADD_PAIRWISE v_sx)), v_1 => ((if h_1417 : (M_1 = M_1_0) then
((if h_1418 : (M_2 = M_2_0) then
([⟨(some (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)), by subst_vars; first | (apply fun_vextunop__.fun_vextunop___case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vextunop__.fun_vextunop___case_15]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vextunop___iiiio (a0 : ishape) (a1 : ishape) (a2 : vextunop__) (a3 : vec_) : List {o : (Option vec_) // (fun_vextunop__ a0 a1 a2 a3 o)} :=
  interp_fun_vextunop___iiiio_fun_vextunop___case_0 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_1 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_2 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_3 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_4 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_5 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_6 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_7 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_8 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_9 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_10 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_11 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_12 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_13 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_14 a0 a1 a2 a3 ++
  interp_fun_vextunop___iiiio_fun_vextunop___case_15 a0 a1 a2 a3

def interp_fun_vswizzlop__iiiio_fun_vswizzlop__case_0 (a0 : bshape) (a1 : vswizzlop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vswizzlop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_bshape (.X .I8 (.mk_dim v_M))), (.mk_vswizzlop__0 M_0 .SWIZZLE), v_1, v_2 => ((if h_1380 : (v_M = M_0) then
([⟨(ivswizzlop_ (.X .I8 (.mk_dim v_M)) iswizzle_lane_ v_1 v_2), by subst_vars; first | (apply fun_vswizzlop_.fun_vswizzlop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vswizzlop_.fun_vswizzlop__case_0]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vswizzlop__iiiio_fun_vswizzlop__case_1 (a0 : bshape) (a1 : vswizzlop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vswizzlop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_bshape (.X .I8 (.mk_dim v_M))), (.mk_vswizzlop__0 M_0 .RELAXED_SWIZZLE), v_1, v_2 => ((if h_1381 : (v_M = M_0) then
([⟨(ivswizzlop_ (.X .I8 (.mk_dim v_M)) irelaxed_swizzle_lane_ v_1 v_2), by subst_vars; first | (apply fun_vswizzlop_.fun_vswizzlop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vswizzlop_.fun_vswizzlop__case_1]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vswizzlop__iiiio (a0 : bshape) (a1 : vswizzlop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vswizzlop_ a0 a1 a2 a3 o)} :=
  interp_fun_vswizzlop__iiiio_fun_vswizzlop__case_0 a0 a1 a2 a3 ++
  interp_fun_vswizzlop__iiiio_fun_vswizzlop__case_1 a0 a1 a2 a3

def interp_wf_bit_i_bit_case_0 (a0 : bit) : List {o : Unit // (wf_bit a0)} :=
  match a0 with
 | (.mk_bit i) => ((if h_4614 : ((i = 0) ∨ (i = 1)) then
([⟨(), by subst_vars; first | (apply wf_bit.bit_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_bit.bit_case_0]⟩])
else []))

def interp_wf_bit_i (a0 : bit) : List {o : Unit // (wf_bit a0)} :=
  interp_wf_bit_i_bit_case_0 a0

def interp_fun_ivbitmaskop__iio (a0 : shape) (a1 : vec_) : List {o : u32 // (fun_ivbitmaskop_ a0 a1 o)} :=
  []

def interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_0 (a0 : ishape) (a1 : vec_) : List {o : u32 // (fun_vbitmaskop_ a0 a1 o)} :=
  match a0, a1 with
 | (.mk_ishape (.X .I32 (.mk_dim v_M))), v => (((interp_fun_ivbitmaskop__iio ((.X (lanetype_Jnn .I32) (.mk_dim v_M))) (v)).flatMap fun ⟨o_179, h_1376⟩ => (match o_179 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_vbitmaskop_.fun_vbitmaskop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbitmaskop_.fun_vbitmaskop__case_0]⟩]))))
 | _, _ => []

def interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_1 (a0 : ishape) (a1 : vec_) : List {o : u32 // (fun_vbitmaskop_ a0 a1 o)} :=
  match a0, a1 with
 | (.mk_ishape (.X .I64 (.mk_dim v_M))), v => (((interp_fun_ivbitmaskop__iio ((.X (lanetype_Jnn .I64) (.mk_dim v_M))) (v)).flatMap fun ⟨o_180, h_1377⟩ => (match o_180 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_vbitmaskop_.fun_vbitmaskop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbitmaskop_.fun_vbitmaskop__case_1]⟩]))))
 | _, _ => []

def interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_2 (a0 : ishape) (a1 : vec_) : List {o : u32 // (fun_vbitmaskop_ a0 a1 o)} :=
  match a0, a1 with
 | (.mk_ishape (.X .I8 (.mk_dim v_M))), v => (((interp_fun_ivbitmaskop__iio ((.X (lanetype_Jnn .I8) (.mk_dim v_M))) (v)).flatMap fun ⟨o_181, h_1378⟩ => (match o_181 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_vbitmaskop_.fun_vbitmaskop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbitmaskop_.fun_vbitmaskop__case_2]⟩]))))
 | _, _ => []

def interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_3 (a0 : ishape) (a1 : vec_) : List {o : u32 // (fun_vbitmaskop_ a0 a1 o)} :=
  match a0, a1 with
 | (.mk_ishape (.X .I16 (.mk_dim v_M))), v => (((interp_fun_ivbitmaskop__iio ((.X (lanetype_Jnn .I16) (.mk_dim v_M))) (v)).flatMap fun ⟨o_182, h_1379⟩ => (match o_182 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_vbitmaskop_.fun_vbitmaskop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbitmaskop_.fun_vbitmaskop__case_3]⟩]))))
 | _, _ => []

def interp_fun_vbitmaskop__iio (a0 : ishape) (a1 : vec_) : List {o : u32 // (fun_vbitmaskop_ a0 a1 o)} :=
  interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_0 a0 a1 ++
  interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_1 a0 a1 ++
  interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_2 a0 a1 ++
  interp_fun_vbitmaskop__iio_fun_vbitmaskop__case_3 a0 a1

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_0 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim v_M))), (.mk_vshiftop__0 .I32 M_0 .SHL), v, i => ((if h_1359 : (v_M = M_0) then
((if h_1360 : ((lsizenn (lanetype_Jnn .I32)) ≠ 0) then
([⟨(ivshiftop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ishl_ v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I32))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_0]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_1 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim v_M))), (.mk_vshiftop__0 .I64 M_0 .SHL), v, i => ((if h_1361 : (v_M = M_0) then
((if h_1362 : ((lsizenn (lanetype_Jnn .I64)) ≠ 0) then
([⟨(ivshiftop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ishl_ v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I64))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_1]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_2 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim v_M))), (.mk_vshiftop__0 .I8 M_0 .SHL), v, i => ((if h_1363 : (v_M = M_0) then
((if h_1364 : ((lsizenn (lanetype_Jnn .I8)) ≠ 0) then
([⟨(ivshiftop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ishl_ v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I8))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_2]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_3 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim v_M))), (.mk_vshiftop__0 .I16 M_0 .SHL), v, i => ((if h_1365 : (v_M = M_0) then
((if h_1366 : ((lsizenn (lanetype_Jnn .I16)) ≠ 0) then
([⟨(ivshiftop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ishl_ v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I16))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_3]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_4 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I32 (.mk_dim v_M))), (.mk_vshiftop__0 .I32 M_0 (.SHR v_sx)), v, i => ((if h_1367 : (v_M = M_0) then
((if h_1368 : ((lsizenn (lanetype_Jnn .I32)) ≠ 0) then
([⟨(ivshiftopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ishr_ v_sx v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I32))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_4]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_5 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I64 (.mk_dim v_M))), (.mk_vshiftop__0 .I64 M_0 (.SHR v_sx)), v, i => ((if h_1369 : (v_M = M_0) then
((if h_1370 : ((lsizenn (lanetype_Jnn .I64)) ≠ 0) then
([⟨(ivshiftopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ishr_ v_sx v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I64))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_5]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_6 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I8 (.mk_dim v_M))), (.mk_vshiftop__0 .I8 M_0 (.SHR v_sx)), v, i => ((if h_1371 : (v_M = M_0) then
((if h_1372 : ((lsizenn (lanetype_Jnn .I8)) ≠ 0) then
([⟨(ivshiftopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ishr_ v_sx v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I8))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_6]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio_fun_vshiftop__case_7 (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.mk_ishape (.X .I16 (.mk_dim v_M))), (.mk_vshiftop__0 .I16 M_0 (.SHR v_sx)), v, i => ((if h_1373 : (v_M = M_0) then
((if h_1374 : ((lsizenn (lanetype_Jnn .I16)) ≠ 0) then
([⟨(ivshiftopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ishr_ v_sx v (.mk_uN ((proj_uN_0 i) % (lsizenn (lanetype_Jnn .I16))))), by subst_vars; first | (apply fun_vshiftop_.fun_vshiftop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vshiftop_.fun_vshiftop__case_7]⟩])
else []))
else []))
 | _, _, _, _ => []

def interp_fun_vshiftop__iiiio (a0 : ishape) (a1 : vshiftop_) (a2 : vec_) (a3 : u32) : List {o : (Option vec_) // (fun_vshiftop_ a0 a1 a2 a3 o)} :=
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_0 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_1 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_2 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_3 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_4 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_5 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_6 a0 a1 a2 a3 ++
  interp_fun_vshiftop__iiiio_fun_vshiftop__case_7 a0 a1 a2 a3

def interp_fun_vrelop__iiiio_fun_vrelop__case_0 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 .EQ), v_1, v_2 => ((if h_1322 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ieq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_0]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_1 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 .EQ), v_1, v_2 => ((if h_1323 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ieq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_1]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_2 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 .EQ), v_1, v_2 => ((if h_1324 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ieq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_2]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_3 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 .EQ), v_1, v_2 => ((if h_1325 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ieq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_3]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_4 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 .NE), v_1, v_2 => ((if h_1326 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ine_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_4]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_5 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 .NE), v_1, v_2 => ((if h_1327 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ine_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_5]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_6 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 .NE), v_1, v_2 => ((if h_1328 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ine_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_6]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_7 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 .NE), v_1, v_2 => ((if h_1329 : (v_M = M_0) then
([⟨(some (ivrelop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ine_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_7]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_8 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 (.LT v_sx)), v_1, v_2 => ((if h_1330 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_8]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_9 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 (.LT v_sx)), v_1, v_2 => ((if h_1331 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_9]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_10 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 (.LT v_sx)), v_1, v_2 => ((if h_1332 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_10]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_11 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 (.LT v_sx)), v_1, v_2 => ((if h_1333 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_11]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_12 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 (.GT v_sx)), v_1, v_2 => ((if h_1334 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) igt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_12]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_13 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 (.GT v_sx)), v_1, v_2 => ((if h_1335 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) igt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_13]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_14 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 (.GT v_sx)), v_1, v_2 => ((if h_1336 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) igt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_14]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_15 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 (.GT v_sx)), v_1, v_2 => ((if h_1337 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) igt_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_15]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_16 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 (.LE v_sx)), v_1, v_2 => ((if h_1338 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ile_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_16]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_17 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 (.LE v_sx)), v_1, v_2 => ((if h_1339 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ile_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_17]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_18 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 (.LE v_sx)), v_1, v_2 => ((if h_1340 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ile_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_18]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_19 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 (.LE v_sx)), v_1, v_2 => ((if h_1341 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ile_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_19]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_20 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vrelop__0 .I32 M_0 (.GE v_sx)), v_1, v_2 => ((if h_1342 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ige_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_20]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_21 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vrelop__0 .I64 M_0 (.GE v_sx)), v_1, v_2 => ((if h_1343 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ige_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_21]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_22 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vrelop__0 .I8 M_0 (.GE v_sx)), v_1, v_2 => ((if h_1344 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ige_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_22]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_23 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vrelop__0 .I16 M_0 (.GE v_sx)), v_1, v_2 => ((if h_1345 : (v_M = M_0) then
([⟨(some (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ige_ v_sx v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_23]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_24 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .EQ), v_1, v_2 => ((if h_1346 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) feq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_24]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_25 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .EQ), v_1, v_2 => ((if h_1347 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) feq_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_25]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_26 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .NE), v_1, v_2 => ((if h_1348 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fne_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_26]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_27 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .NE), v_1, v_2 => ((if h_1349 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fne_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_27]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_28 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .LT), v_1, v_2 => ((if h_1350 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) flt_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_28]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_29 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .LT), v_1, v_2 => ((if h_1351 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) flt_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_29]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_30 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .GT), v_1, v_2 => ((if h_1352 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fgt_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_30]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_31 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .GT), v_1, v_2 => ((if h_1353 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fgt_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_31]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_32 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .LE), v_1, v_2 => ((if h_1354 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fle_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_32]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_33 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .LE), v_1, v_2 => ((if h_1355 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fle_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_33]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_34 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vrelop__1 .F32 M_0 .GE), v_1, v_2 => ((if h_1356 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fge_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_34]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio_fun_vrelop__case_35 (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vrelop__1 .F64 M_0 .GE), v_1, v_2 => ((if h_1357 : (v_M = M_0) then
([⟨(some (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fge_ v_1 v_2)), by subst_vars; first | (apply fun_vrelop_.fun_vrelop__case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vrelop_.fun_vrelop__case_35]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vrelop__iiiio (a0 : shape) (a1 : vrelop_) (a2 : vec_) (a3 : vec_) : List {o : (Option vec_) // (fun_vrelop_ a0 a1 a2 a3 o)} :=
  interp_fun_vrelop__iiiio_fun_vrelop__case_0 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_1 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_2 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_3 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_4 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_5 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_6 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_7 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_8 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_9 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_10 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_11 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_12 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_13 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_14 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_15 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_16 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_17 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_18 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_19 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_20 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_21 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_22 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_23 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_24 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_25 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_26 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_27 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_28 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_29 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_30 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_31 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_32 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_33 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_34 a0 a1 a2 a3 ++
  interp_fun_vrelop__iiiio_fun_vrelop__case_35 a0 a1 a2 a3

mutual

partial def interp_fun_prod_io_fun_prod_case_0 (a0 : (List Nat)) : List {o : Nat // (fun_prod a0 o)} :=
  match a0 with
 | [] => ([⟨1, by subst_vars; first | (apply fun_prod.fun_prod_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_prod.fun_prod_case_0]⟩])
 | _ => []

partial def interp_fun_prod_io_fun_prod_case_1 (a0 : (List Nat)) : List {o : Nat // (fun_prod a0 o)} :=
  match a0 with
 | (v_n :: n'_lst) => (((interp_fun_prod_io (n'_lst)).flatMap fun ⟨o_178, h_1319⟩ => (match o_178 with
 | var_0 => ([⟨(v_n * var_0), by subst_vars; first | (apply fun_prod.fun_prod_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_prod.fun_prod_case_1]⟩]))))
 | _ => []

partial def interp_fun_prod_io (a0 : (List Nat)) : List {o : Nat // (fun_prod a0 o)} :=
  interp_fun_prod_io_fun_prod_case_0 a0 ++
  interp_fun_prod_io_fun_prod_case_1 a0

end

def interp_fun_vternop__iiiiio_fun_vternop__case_0 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vternop__0 .I32 M_0 .RELAXED_LANESELECT), v_1, v_2, v_3 => ((if h_1310 : (v_M = M_0) then
([⟨(some (ivternopnd_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_0]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_1 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vternop__0 .I64 M_0 .RELAXED_LANESELECT), v_1, v_2, v_3 => ((if h_1311 : (v_M = M_0) then
([⟨(some (ivternopnd_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_1]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_2 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vternop__0 .I8 M_0 .RELAXED_LANESELECT), v_1, v_2, v_3 => ((if h_1312 : (v_M = M_0) then
([⟨(some (ivternopnd_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_2]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_3 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vternop__0 .I16 M_0 .RELAXED_LANESELECT), v_1, v_2, v_3 => ((if h_1313 : (v_M = M_0) then
([⟨(some (ivternopnd_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_3]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_4 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vternop__1 .F32 M_0 .RELAXED_MADD), v_1, v_2, v_3 => ((if h_1314 : (v_M = M_0) then
([⟨(some (fvternop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_4]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_5 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vternop__1 .F64 M_0 .RELAXED_MADD), v_1, v_2, v_3 => ((if h_1315 : (v_M = M_0) then
([⟨(some (fvternop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_5]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_6 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vternop__1 .F32 M_0 .RELAXED_NMADD), v_1, v_2, v_3 => ((if h_1316 : (v_M = M_0) then
([⟨(some (fvternop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_6]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio_fun_vternop__case_7 (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  match a0, a1, a2, a3, a4 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vternop__1 .F64 M_0 .RELAXED_NMADD), v_1, v_2, v_3 => ((if h_1317 : (v_M = M_0) then
([⟨(some (fvternop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3)), by subst_vars; first | (apply fun_vternop_.fun_vternop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vternop_.fun_vternop__case_7]⟩])
else []))
 | _, _, _, _, _ => []

def interp_fun_vternop__iiiiio (a0 : shape) (a1 : vternop_) (a2 : vec_) (a3 : vec_) (a4 : vec_) : List {o : (Option (List vec_)) // (fun_vternop_ a0 a1 a2 a3 a4 o)} :=
  interp_fun_vternop__iiiiio_fun_vternop__case_0 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_1 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_2 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_3 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_4 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_5 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_6 a0 a1 a2 a3 a4 ++
  interp_fun_vternop__iiiiio_fun_vternop__case_7 a0 a1 a2 a3 a4

def interp_fun_vbinop__iiiio_fun_vbinop__case_0 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .ADD), v_1, v_2 => ((if h_1249 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iadd_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_0]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_1 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .ADD), v_1, v_2 => ((if h_1250 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iadd_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_1]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_2 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .ADD), v_1, v_2 => ((if h_1251 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iadd_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_2]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_3 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .ADD), v_1, v_2 => ((if h_1252 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iadd_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_3]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_4 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .SUB), v_1, v_2 => ((if h_1253 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) isub_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_4]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_5 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .SUB), v_1, v_2 => ((if h_1254 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) isub_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_5]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_6 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .SUB), v_1, v_2 => ((if h_1255 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) isub_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_6]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_7 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .SUB), v_1, v_2 => ((if h_1256 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) isub_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_7]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_8 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .MUL), v_1, v_2 => ((if h_1257 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imul_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_8]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_9 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .MUL), v_1, v_2 => ((if h_1258 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imul_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_9]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_10 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .MUL), v_1, v_2 => ((if h_1259 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imul_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_10]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_11 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .MUL), v_1, v_2 => ((if h_1260 : (v_M = M_0) then
([⟨(ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imul_ v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_11]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_12 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 (.ADD_SAT v_sx)), v_1, v_2 => ((if h_1261 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_12]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_13 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 (.ADD_SAT v_sx)), v_1, v_2 => ((if h_1262 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_13]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_14 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 (.ADD_SAT v_sx)), v_1, v_2 => ((if h_1263 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_14]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_15 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 (.ADD_SAT v_sx)), v_1, v_2 => ((if h_1264 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_15]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_16 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 (.SUB_SAT v_sx)), v_1, v_2 => ((if h_1265 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_16]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_17 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 (.SUB_SAT v_sx)), v_1, v_2 => ((if h_1266 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_17]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_18 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 (.SUB_SAT v_sx)), v_1, v_2 => ((if h_1267 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_18]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_19 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 (.SUB_SAT v_sx)), v_1, v_2 => ((if h_1268 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_19]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_20 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 (.MIN v_sx)), v_1, v_2 => ((if h_1269 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imin_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_20]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_21 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 (.MIN v_sx)), v_1, v_2 => ((if h_1270 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imin_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_21]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_22 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 (.MIN v_sx)), v_1, v_2 => ((if h_1271 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imin_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_22]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_23 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 (.MIN v_sx)), v_1, v_2 => ((if h_1272 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imin_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_23]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_24 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 (.MAX v_sx)), v_1, v_2 => ((if h_1273 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imax_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_24]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_25 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 (.MAX v_sx)), v_1, v_2 => ((if h_1274 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imax_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_25]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_26 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 (.MAX v_sx)), v_1, v_2 => ((if h_1275 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imax_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_26]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_27 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 (.MAX v_sx)), v_1, v_2 => ((if h_1276 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imax_ v_sx v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_27]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_28 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .AVGRU), v_1, v_2 => ((if h_1277 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iavgr_ .U v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_28]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_29 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .AVGRU), v_1, v_2 => ((if h_1278 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iavgr_ .U v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_29]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_30 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .AVGRU), v_1, v_2 => ((if h_1279 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iavgr_ .U v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_30]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_31 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .AVGRU), v_1, v_2 => ((if h_1280 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iavgr_ .U v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_31]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_32 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .Q15MULR_SATS), v_1, v_2 => ((if h_1281 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_32]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_33 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .Q15MULR_SATS), v_1, v_2 => ((if h_1282 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_33]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_34 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .Q15MULR_SATS), v_1, v_2 => ((if h_1283 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_34]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_35 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .Q15MULR_SATS), v_1, v_2 => ((if h_1284 : (v_M = M_0) then
([⟨(ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_35]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_36 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vbinop__0 .I32 M_0 .RELAXED_Q15MULRS), v_1, v_2 => ((if h_1285 : (v_M = M_0) then
([⟨(some (ivbinopsxnd_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_36]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_37 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vbinop__0 .I64 M_0 .RELAXED_Q15MULRS), v_1, v_2 => ((if h_1286 : (v_M = M_0) then
([⟨(some (ivbinopsxnd_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_37]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_38 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vbinop__0 .I8 M_0 .RELAXED_Q15MULRS), v_1, v_2 => ((if h_1287 : (v_M = M_0) then
([⟨(some (ivbinopsxnd_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_38 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_38]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_39 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vbinop__0 .I16 M_0 .RELAXED_Q15MULRS), v_1, v_2 => ((if h_1288 : (v_M = M_0) then
([⟨(some (ivbinopsxnd_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_39 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_39]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_40 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .ADD), v_1, v_2 => ((if h_1289 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fadd_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_40 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_40]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_41 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .ADD), v_1, v_2 => ((if h_1290 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fadd_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_41 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_41]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_42 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .SUB), v_1, v_2 => ((if h_1291 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fsub_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_42 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_42]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_43 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .SUB), v_1, v_2 => ((if h_1292 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fsub_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_43 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_43]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_44 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .MUL), v_1, v_2 => ((if h_1293 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmul_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_44 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_44]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_45 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .MUL), v_1, v_2 => ((if h_1294 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmul_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_45 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_45]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_46 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .DIV), v_1, v_2 => ((if h_1295 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fdiv_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_46 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_46]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_47 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .DIV), v_1, v_2 => ((if h_1296 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fdiv_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_47 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_47]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_48 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .MIN), v_1, v_2 => ((if h_1297 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmin_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_48 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_48]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_49 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .MIN), v_1, v_2 => ((if h_1298 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmin_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_49 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_49]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_50 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .MAX), v_1, v_2 => ((if h_1299 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmax_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_50 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_50]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_51 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .MAX), v_1, v_2 => ((if h_1300 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmax_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_51 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_51]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_52 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .PMIN), v_1, v_2 => ((if h_1301 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fpmin_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_52 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_52]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_53 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .PMIN), v_1, v_2 => ((if h_1302 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fpmin_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_53 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_53]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_54 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .PMAX), v_1, v_2 => ((if h_1303 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fpmax_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_54 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_54]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_55 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .PMAX), v_1, v_2 => ((if h_1304 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fpmax_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_55 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_55]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_56 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .RELAXED_MIN), v_1, v_2 => ((if h_1305 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_min_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_56 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_56]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_57 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .RELAXED_MIN), v_1, v_2 => ((if h_1306 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_min_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_57 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_57]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_58 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vbinop__1 .F32 M_0 .RELAXED_MAX), v_1, v_2 => ((if h_1307 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_max_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_58 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_58]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio_fun_vbinop__case_59 (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vbinop__1 .F64 M_0 .RELAXED_MAX), v_1, v_2 => ((if h_1308 : (v_M = M_0) then
([⟨(some (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_max_ v_1 v_2)), by subst_vars; first | (apply fun_vbinop_.fun_vbinop__case_59 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vbinop_.fun_vbinop__case_59]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_vbinop__iiiio (a0 : shape) (a1 : vbinop_) (a2 : vec_) (a3 : vec_) : List {o : (Option (List vec_)) // (fun_vbinop_ a0 a1 a2 a3 o)} :=
  interp_fun_vbinop__iiiio_fun_vbinop__case_0 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_1 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_2 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_3 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_4 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_5 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_6 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_7 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_8 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_9 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_10 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_11 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_12 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_13 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_14 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_15 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_16 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_17 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_18 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_19 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_20 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_21 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_22 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_23 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_24 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_25 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_26 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_27 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_28 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_29 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_30 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_31 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_32 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_33 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_34 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_35 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_36 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_37 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_38 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_39 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_40 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_41 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_42 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_43 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_44 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_45 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_46 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_47 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_48 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_49 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_50 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_51 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_52 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_53 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_54 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_55 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_56 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_57 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_58 a0 a1 a2 a3 ++
  interp_fun_vbinop__iiiio_fun_vbinop__case_59 a0 a1 a2 a3

def interp_fun_vunop__iiio_fun_vunop__case_0 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .ABS), v => ((if h_1222 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fabs_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_0]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_1 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .ABS), v => ((if h_1223 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fabs_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_1]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_2 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .NEG), v => ((if h_1224 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fneg_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_2]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_3 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .NEG), v => ((if h_1225 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fneg_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_3]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_4 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .SQRT), v => ((if h_1226 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fsqrt_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_4]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_5 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .SQRT), v => ((if h_1227 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fsqrt_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_5]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_6 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .CEIL), v => ((if h_1228 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fceil_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_6]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_7 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .CEIL), v => ((if h_1229 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fceil_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_7]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_8 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .FLOOR), v => ((if h_1230 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) ffloor_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_8]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_9 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .FLOOR), v => ((if h_1231 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) ffloor_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_9]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_10 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .TRUNC), v => ((if h_1232 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) ftrunc_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_10]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_11 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .TRUNC), v => ((if h_1233 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) ftrunc_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_11]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_12 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F32 (.mk_dim v_M)), (.mk_vunop__1 .F32 M_0 .NEAREST), v => ((if h_1234 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fnearest_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_12]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_13 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .F64 (.mk_dim v_M)), (.mk_vunop__1 .F64 M_0 .NEAREST), v => ((if h_1235 : (v_M = M_0) then
([⟨(some (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fnearest_ v)), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_13]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_14 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vunop__0 .I32 M_0 .ABS), v => ((if h_1236 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iabs_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_14]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_15 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vunop__0 .I64 M_0 .ABS), v => ((if h_1237 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iabs_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_15]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_16 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vunop__0 .I8 M_0 .ABS), v => ((if h_1238 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iabs_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_16]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_17 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vunop__0 .I16 M_0 .ABS), v => ((if h_1239 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iabs_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_17]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_18 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vunop__0 .I32 M_0 .NEG), v => ((if h_1240 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ineg_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_18]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_19 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vunop__0 .I64 M_0 .NEG), v => ((if h_1241 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ineg_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_19]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_20 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vunop__0 .I8 M_0 .NEG), v => ((if h_1242 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ineg_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_20]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_21 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vunop__0 .I16 M_0 .NEG), v => ((if h_1243 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ineg_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_21]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_22 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I32 (.mk_dim v_M)), (.mk_vunop__0 .I32 M_0 .POPCNT), v => ((if h_1244 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ipopcnt_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_22]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_23 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I64 (.mk_dim v_M)), (.mk_vunop__0 .I64 M_0 .POPCNT), v => ((if h_1245 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ipopcnt_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_23]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_24 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I8 (.mk_dim v_M)), (.mk_vunop__0 .I8 M_0 .POPCNT), v => ((if h_1246 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ipopcnt_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_24]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio_fun_vunop__case_25 (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.X .I16 (.mk_dim v_M)), (.mk_vunop__0 .I16 M_0 .POPCNT), v => ((if h_1247 : (v_M = M_0) then
([⟨(ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ipopcnt_ v), by subst_vars; first | (apply fun_vunop_.fun_vunop__case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_vunop_.fun_vunop__case_25]⟩])
else []))
 | _, _, _ => []

def interp_fun_vunop__iiio (a0 : shape) (a1 : vunop_) (a2 : vec_) : List {o : (Option (List vec_)) // (fun_vunop_ a0 a1 a2 o)} :=
  interp_fun_vunop__iiio_fun_vunop__case_0 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_1 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_2 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_3 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_4 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_5 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_6 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_7 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_8 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_9 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_10 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_11 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_12 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_13 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_14 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_15 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_16 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_17 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_18 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_19 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_20 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_21 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_22 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_23 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_24 a0 a1 a2 ++
  interp_fun_vunop__iiio_fun_vunop__case_25 a0 a1 a2

def interp_fun_cvtop___iiiio_fun_cvtop___case_0 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .I32, (.mk_cvtop___0 .I32 .I32 (.EXTEND v_sx)), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_0]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_1 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .I32, (.mk_cvtop___0 .I64 .I32 (.EXTEND v_sx)), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_1]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_2 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .I64, (.mk_cvtop___0 .I32 .I64 (.EXTEND v_sx)), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_2]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_3 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .I64, (.mk_cvtop___0 .I64 .I64 (.EXTEND v_sx)), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_3]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_4 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .I32, (.mk_cvtop___0 .I32 .I32 .WRAP), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_4]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_5 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .I32, (.mk_cvtop___0 .I64 .I32 .WRAP), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_5]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_6 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .I64, (.mk_cvtop___0 .I32 .I64 .WRAP), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_6]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_7 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .I64, (.mk_cvtop___0 .I64 .I64 .WRAP), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_7]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_8 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I32, (.mk_cvtop___2 .F32 .I32 (.TRUNC v_sx)), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_51 : iN) => ((.mk_num__0 .I32 iter_0_51) : num_)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_8]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_9 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I32, (.mk_cvtop___2 .F64 .I32 (.TRUNC v_sx)), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_52 : iN) => ((.mk_num__0 .I32 iter_0_52) : num_)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_9]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_10 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I64, (.mk_cvtop___2 .F32 .I64 (.TRUNC v_sx)), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_53 : iN) => ((.mk_num__0 .I64 iter_0_53) : num_)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_10]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_11 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I64, (.mk_cvtop___2 .F64 .I64 (.TRUNC v_sx)), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_54 : iN) => ((.mk_num__0 .I64 iter_0_54) : num_)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_11]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_12 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I32, (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT v_sx)), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_55 : iN) => ((.mk_num__0 .I32 iter_0_55) : num_)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_12]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_13 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I32, (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT v_sx)), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_56 : iN) => ((.mk_num__0 .I32 iter_0_56) : num_)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_13]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_14 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I64, (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT v_sx)), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_57 : iN) => ((.mk_num__0 .I64 iter_0_57) : num_)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_14]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_15 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I64, (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT v_sx)), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_58 : iN) => ((.mk_num__0 .I64 iter_0_58) : num_)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_15]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_16 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .F32, (.mk_cvtop___1 .I32 .F32 (.CONVERT v_sx)), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_16]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_17 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .F32, (.mk_cvtop___1 .I64 .F32 (.CONVERT v_sx)), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_17]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_18 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .F64, (.mk_cvtop___1 .I32 .F64 (.CONVERT v_sx)), (.mk_num__0 .I32 i_1) => ([⟨(some ([(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_18]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_19 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .F64, (.mk_cvtop___1 .I64 .F64 (.CONVERT v_sx)), (.mk_num__0 .I64 i_1) => ([⟨(some ([(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_19]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_20 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .F32, (.mk_cvtop___3 .F32 .F32 .PROMOTE), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_59 : fN) => ((.mk_num__1 .F32 iter_0_59) : num_)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_20]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_21 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .F32, (.mk_cvtop___3 .F64 .F32 .PROMOTE), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_60 : fN) => ((.mk_num__1 .F32 iter_0_60) : num_)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_21]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_22 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .F64, (.mk_cvtop___3 .F32 .F64 .PROMOTE), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_61 : fN) => ((.mk_num__1 .F64 iter_0_61) : num_)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_22]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_23 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .F64, (.mk_cvtop___3 .F64 .F64 .PROMOTE), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_62 : fN) => ((.mk_num__1 .F64 iter_0_62) : num_)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_23]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_24 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .F32, (.mk_cvtop___3 .F32 .F32 .DEMOTE), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_63 : fN) => ((.mk_num__1 .F32 iter_0_63) : num_)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_24]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_25 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .F32, (.mk_cvtop___3 .F64 .F32 .DEMOTE), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_64 : fN) => ((.mk_num__1 .F32 iter_0_64) : num_)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_25]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_26 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .F64, (.mk_cvtop___3 .F32 .F64 .DEMOTE), (.mk_num__1 .F32 f_1) => ([⟨(some (List.map (fun (iter_0_65 : fN) => ((.mk_num__1 .F64 iter_0_65) : num_)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_26]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_27 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .F64, (.mk_cvtop___3 .F64 .F64 .DEMOTE), (.mk_num__1 .F64 f_1) => ([⟨(some (List.map (fun (iter_0_66 : fN) => ((.mk_num__1 .F64 iter_0_66) : num_)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_27]⟩])
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_28 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .F32, (.mk_cvtop___1 .I32 .F32 .REINTERPRET), (.mk_num__0 .I32 i_1) => ((if h_1213 : ((size (numtype_addrtype .I32)) = (size (numtype_Fnn .F32))) then
([⟨(some ([(reinterpret__ (numtype_addrtype .I32) (numtype_Fnn .F32) (.mk_num__0 .I32 i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_28]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_29 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .F32, (.mk_cvtop___1 .I64 .F32 .REINTERPRET), (.mk_num__0 .I64 i_1) => ((if h_1214 : ((size (numtype_addrtype .I64)) = (size (numtype_Fnn .F32))) then
([⟨(some ([(reinterpret__ (numtype_addrtype .I64) (numtype_Fnn .F32) (.mk_num__0 .I64 i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_29]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_30 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, .F64, (.mk_cvtop___1 .I32 .F64 .REINTERPRET), (.mk_num__0 .I32 i_1) => ((if h_1215 : ((size (numtype_addrtype .I32)) = (size (numtype_Fnn .F64))) then
([⟨(some ([(reinterpret__ (numtype_addrtype .I32) (numtype_Fnn .F64) (.mk_num__0 .I32 i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_30]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_31 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, .F64, (.mk_cvtop___1 .I64 .F64 .REINTERPRET), (.mk_num__0 .I64 i_1) => ((if h_1216 : ((size (numtype_addrtype .I64)) = (size (numtype_Fnn .F64))) then
([⟨(some ([(reinterpret__ (numtype_addrtype .I64) (numtype_Fnn .F64) (.mk_num__0 .I64 i_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_31]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_32 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I32, (.mk_cvtop___2 .F32 .I32 .REINTERPRET), (.mk_num__1 .F32 f_1) => ((if h_1217 : ((size (numtype_Fnn .F32)) = (size (numtype_addrtype .I32))) then
([⟨(some ([(reinterpret__ (numtype_Fnn .F32) (numtype_addrtype .I32) (.mk_num__1 .F32 f_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_32]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_33 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I32, (.mk_cvtop___2 .F64 .I32 .REINTERPRET), (.mk_num__1 .F64 f_1) => ((if h_1218 : ((size (numtype_Fnn .F64)) = (size (numtype_addrtype .I32))) then
([⟨(some ([(reinterpret__ (numtype_Fnn .F64) (numtype_addrtype .I32) (.mk_num__1 .F64 f_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_33]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_34 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, .I64, (.mk_cvtop___2 .F32 .I64 .REINTERPRET), (.mk_num__1 .F32 f_1) => ((if h_1219 : ((size (numtype_Fnn .F32)) = (size (numtype_addrtype .I64))) then
([⟨(some ([(reinterpret__ (numtype_Fnn .F32) (numtype_addrtype .I64) (.mk_num__1 .F32 f_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_34]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio_fun_cvtop___case_35 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, .I64, (.mk_cvtop___2 .F64 .I64 .REINTERPRET), (.mk_num__1 .F64 f_1) => ((if h_1220 : ((size (numtype_Fnn .F64)) = (size (numtype_addrtype .I64))) then
([⟨(some ([(reinterpret__ (numtype_Fnn .F64) (numtype_addrtype .I64) (.mk_num__1 .F64 f_1))] : (List num_))), by subst_vars; first | (apply fun_cvtop__.fun_cvtop___case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_cvtop__.fun_cvtop___case_35]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_cvtop___iiiio (a0 : numtype) (a1 : numtype) (a2 : cvtop__) (a3 : num_) : List {o : (Option (List num_)) // (fun_cvtop__ a0 a1 a2 a3 o)} :=
  interp_fun_cvtop___iiiio_fun_cvtop___case_0 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_1 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_2 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_3 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_4 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_5 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_6 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_7 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_8 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_9 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_10 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_11 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_12 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_13 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_14 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_15 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_16 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_17 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_18 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_19 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_20 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_21 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_22 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_23 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_24 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_25 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_26 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_27 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_28 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_29 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_30 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_31 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_32 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_33 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_34 a0 a1 a2 a3 ++
  interp_fun_cvtop___iiiio_fun_cvtop___case_35 a0 a1 a2 a3

def interp_fun_inv_signed__iio_fun_inv_signed__case_0 (a0 : N) (a1 : Int) : List {o : Nat // (fun_inv_signed_ a0 a1 o)} :=
  match a0, a1 with
 | v_N, i => ((if h_4115 : ((Int.ofNat 0) <= i) then
((if h_4116 : (i < (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat v_N) - (Int.ofNat 1)))))) then
((if h_4117 : (0 ≤ i) then
((if h_4118 : (0 ≤ ((Int.ofNat v_N) - (Int.ofNat 1))) then
([⟨(Int.toNat i), by subst_vars; first | (apply fun_inv_signed_.fun_inv_signed__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_inv_signed_.fun_inv_signed__case_0]⟩])
else []))
else []))
else []))
else []))

def interp_fun_inv_signed__iio_fun_inv_signed__case_1 (a0 : N) (a1 : Int) : List {o : Nat // (fun_inv_signed_ a0 a1 o)} :=
  match a0, a1 with
 | v_N, i => ((if h_4119 : ((0 - (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat v_N) - (Int.ofNat 1)))))) <= i) then
((if h_4120 : (i < (Int.ofNat 0)) then
((if h_4121 : (0 ≤ (i + (Int.ofNat (2 ^ v_N)))) then
((if h_4122 : (0 ≤ ((Int.ofNat v_N) - (Int.ofNat 1))) then
([⟨(Int.toNat (i + (Int.ofNat (2 ^ v_N)))), by subst_vars; first | (apply fun_inv_signed_.fun_inv_signed__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_inv_signed_.fun_inv_signed__case_1]⟩])
else []))
else []))
else []))
else []))

def interp_fun_inv_signed__iio (a0 : N) (a1 : Int) : List {o : Nat // (fun_inv_signed_ a0 a1 o)} :=
  interp_fun_inv_signed__iio_fun_inv_signed__case_0 a0 a1 ++
  interp_fun_inv_signed__iio_fun_inv_signed__case_1 a0 a1

def interp_fun_signed__iio_fun_signed__case_0 (a0 : N) (a1 : Nat) : List {o : Int // (fun_signed_ a0 a1 o)} :=
  match a0, a1 with
 | v_N, i => ((if h_4600 : (i < (2 ^ (Int.toNat ((Int.ofNat v_N) - (Int.ofNat 1))))) then
((if h_4601 : (0 ≤ ((Int.ofNat v_N) - (Int.ofNat 1))) then
([⟨(Int.ofNat i), by subst_vars; first | (apply fun_signed_.fun_signed__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_signed_.fun_signed__case_0]⟩])
else []))
else []))

def interp_fun_signed__iio_fun_signed__case_1 (a0 : N) (a1 : Nat) : List {o : Int // (fun_signed_ a0 a1 o)} :=
  match a0, a1 with
 | v_N, i => ((if h_4602 : ((2 ^ (Int.toNat ((Int.ofNat v_N) - (Int.ofNat 1)))) <= i) then
((if h_4603 : (i < (2 ^ v_N)) then
((if h_4604 : (0 ≤ ((Int.ofNat v_N) - (Int.ofNat 1))) then
([⟨((Int.ofNat i) - (Int.ofNat (2 ^ v_N))), by subst_vars; first | (apply fun_signed_.fun_signed__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_signed_.fun_signed__case_1]⟩])
else []))
else []))
else []))

def interp_fun_signed__iio (a0 : N) (a1 : Nat) : List {o : Int // (fun_signed_ a0 a1 o)} :=
  interp_fun_signed__iio_fun_signed__case_0 a0 a1 ++
  interp_fun_signed__iio_fun_signed__case_1 a0 a1

def interp_fun_irem__iiiio_fun_irem__case_0 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_irem_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .U, i_1, (.mk_uN 0) => ([⟨none, by subst_vars; first | (apply fun_irem_.fun_irem__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_irem_.fun_irem__case_0]⟩])
 | _, _, _, _ => []

def interp_fun_irem__iiiio_fun_irem__case_1 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_irem_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .U, i_1, i_2 => ((if h_4262 : (0 ≤ ((Int.ofNat (proj_uN_0 i_1)) - (Int.ofNat ((proj_uN_0 i_2) * (Int.toNat (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2)))))))))) then
((if h_4263 : (0 ≤ (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2)))))) then
((if h_4264 : ((Rat.ofInt (Int.ofNat (proj_uN_0 i_2))) ≠ 0) then
([⟨(some (.mk_uN (Int.toNat ((Int.ofNat (proj_uN_0 i_1)) - (Int.ofNat ((proj_uN_0 i_2) * (Int.toNat (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2)))))))))))), by subst_vars; first | (apply fun_irem_.fun_irem__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_irem_.fun_irem__case_1]⟩])
else []))
else []))
else []))
 | _, _, _, _ => []

def interp_fun_irem__iiiio_fun_irem__case_2 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_irem_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .S, i_1, (.mk_uN 0) => ([⟨none, by subst_vars; first | (apply fun_irem_.fun_irem__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_irem_.fun_irem__case_2]⟩])
 | _, _, _, _ => []

def interp_fun_irem__iiiio_fun_irem__case_3 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_irem_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .S, i_1, i_2 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_2))).flatMap fun ⟨o_350, h_4265⟩ => (match o_350 with
 | var_2 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_1))).flatMap fun ⟨o_351, h_4266⟩ => (match o_351 with
 | var_1 => (((fun (j_1 : Int) (h_4268 : (var_1 : Int) = j_1) => (((fun (j_2 : Int) (h_4270 : (var_2 : Int) = j_2) => (((interp_fun_inv_signed__iio (v_N) ((j_1 - (j_2 * (truncz ((Rat.ofInt j_1) / (Rat.ofInt j_2))))))).flatMap fun ⟨o_352, h_4271⟩ => (match o_352 with
 | var_0 => ((if h_4272 : ((Rat.ofInt j_2) ≠ 0) then
([⟨(some (.mk_uN var_0)), by subst_vars; first | (apply fun_irem_.fun_irem__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_irem_.fun_irem__case_3]⟩])
else [])))))) (var_2 : Int) rfl))) (var_1 : Int) rfl))))))))
 | _, _, _, _ => []

def interp_fun_irem__iiiio (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_irem_ a0 a1 a2 a3 o)} :=
  interp_fun_irem__iiiio_fun_irem__case_0 a0 a1 a2 a3 ++
  interp_fun_irem__iiiio_fun_irem__case_1 a0 a1 a2 a3 ++
  interp_fun_irem__iiiio_fun_irem__case_2 a0 a1 a2 a3 ++
  interp_fun_irem__iiiio_fun_irem__case_3 a0 a1 a2 a3

def interp_fun_idiv__iiiio_fun_idiv__case_0 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .U, i_1, (.mk_uN 0) => ([⟨none, by subst_vars; first | (apply fun_idiv_.fun_idiv__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_idiv_.fun_idiv__case_0]⟩])
 | _, _, _, _ => []

def interp_fun_idiv__iiiio_fun_idiv__case_1 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .U, i_1, i_2 => (((interp_wf_uN_ii (v_N) ((.mk_uN (Int.toNat (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2))))))))).flatMap fun ⟨_, h_4249⟩ => ((if h_4250 : (0 ≤ (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2)))))) then
((if h_4251 : ((Rat.ofInt (Int.ofNat (proj_uN_0 i_2))) ≠ 0) then
([⟨(some (.mk_uN (Int.toNat (truncz ((Rat.ofInt (Int.ofNat (proj_uN_0 i_1))) / (Rat.ofInt (Int.ofNat (proj_uN_0 i_2)))))))), by subst_vars; first | (apply fun_idiv_.fun_idiv__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_idiv_.fun_idiv__case_1]⟩])
else []))
else []))))
 | _, _, _, _ => []

def interp_fun_idiv__iiiio_fun_idiv__case_2 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .S, i_1, (.mk_uN 0) => ([⟨none, by subst_vars; first | (apply fun_idiv_.fun_idiv__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_idiv_.fun_idiv__case_2]⟩])
 | _, _, _, _ => []

def interp_fun_idiv__iiiio_fun_idiv__case_3 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .S, i_1, i_2 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_2))).flatMap fun ⟨o_345, h_4252⟩ => (match o_345 with
 | var_1 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_1))).flatMap fun ⟨o_346, h_4253⟩ => (match o_346 with
 | var_0 => ((if h_4254 : (((Rat.ofInt var_0) / (Rat.ofInt var_1)) = (Rat.ofInt (Int.ofNat (2 ^ (Int.toNat ((Int.ofNat v_N) - (Int.ofNat 1))))))) then
((if h_4255 : ((Rat.ofInt var_1) ≠ 0) then
((if h_4256 : (0 ≤ ((Int.ofNat v_N) - (Int.ofNat 1))) then
([⟨none, by subst_vars; first | (apply fun_idiv_.fun_idiv__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_idiv_.fun_idiv__case_3]⟩])
else []))
else []))
else []))))))))
 | _, _, _, _ => []

def interp_fun_idiv__iiiio_fun_idiv__case_4 (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, .S, i_1, i_2 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_2))).flatMap fun ⟨o_347, h_4257⟩ => (match o_347 with
 | var_2 => (((interp_fun_signed__iio (v_N) ((proj_uN_0 i_1))).flatMap fun ⟨o_348, h_4258⟩ => (match o_348 with
 | var_1 => (((interp_fun_inv_signed__iio (v_N) ((truncz ((Rat.ofInt var_1) / (Rat.ofInt var_2))))).flatMap fun ⟨o_349, h_4259⟩ => (match o_349 with
 | var_0 => (((interp_wf_uN_ii (v_N) ((.mk_uN var_0))).flatMap fun ⟨_, h_4260⟩ => ((if h_4261 : ((Rat.ofInt var_2) ≠ 0) then
([⟨(some (.mk_uN var_0)), by subst_vars; first | (apply fun_idiv_.fun_idiv__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_idiv_.fun_idiv__case_4]⟩])
else [])))))))))))))
 | _, _, _, _ => []

def interp_fun_idiv__iiiio (a0 : N) (a1 : sx) (a2 : iN) (a3 : iN) : List {o : (Option iN) // (fun_idiv_ a0 a1 a2 a3 o)} :=
  interp_fun_idiv__iiiio_fun_idiv__case_0 a0 a1 a2 a3 ++
  interp_fun_idiv__iiiio_fun_idiv__case_1 a0 a1 a2 a3 ++
  interp_fun_idiv__iiiio_fun_idiv__case_2 a0 a1 a2 a3 ++
  interp_fun_idiv__iiiio_fun_idiv__case_3 a0 a1 a2 a3 ++
  interp_fun_idiv__iiiio_fun_idiv__case_4 a0 a1 a2 a3

def interp_wf_num__ii_num__case_0 (a0 : numtype) (a1 : num_) : List {o : Unit // (wf_num_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_num__0 v_Inn var_x) => ((if h_1137 : (v_numtype = (numtype_addrtype v_Inn)) then
(((interp_wf_uN_ii ((size (numtype_addrtype v_Inn))) (var_x)).flatMap fun ⟨_, h_1138⟩ => ([⟨(), by subst_vars; first | (apply wf_num_.num__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_num_.num__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_num__ii_num__case_1 (a0 : numtype) (a1 : num_) : List {o : Unit // (wf_num_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_num__1 v_Fnn var_x) => ((if h_1139 : (v_numtype = (numtype_Fnn v_Fnn)) then
(((interp_wf_fN_ii ((sizenn (numtype_Fnn v_Fnn))) (var_x)).flatMap fun ⟨_, h_1140⟩ => ([⟨(), by subst_vars; first | (apply wf_num_.num__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_num_.num__case_1]⟩])))
else []))
 | _, _ => []

def interp_wf_num__ii (a0 : numtype) (a1 : num_) : List {o : Unit // (wf_num_ a0 a1)} :=
  interp_wf_num__ii_num__case_0 a0 a1 ++
  interp_wf_num__ii_num__case_1 a0 a1

def interp_fun_binop__iiiio_fun_binop__case_0 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .ADD), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (iadd_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1141⟩ => ((if h_1142 : ((2 ^ (sizenn (numtype_addrtype .I32))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I32 (iadd_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_0]⟩])
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_1 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .ADD), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (iadd_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1143⟩ => ((if h_1144 : ((2 ^ (sizenn (numtype_addrtype .I64))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I64 (iadd_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_1]⟩])
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_2 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .SUB), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (isub_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1145⟩ => ((if h_1146 : (0 ≤ (Int.tmod ((Int.ofNat ((2 ^ (sizenn (numtype_addrtype .I32))) + (proj_uN_0 i_1))) - (Int.ofNat (proj_uN_0 i_2))) (Int.ofNat (2 ^ (sizenn (numtype_addrtype .I32)))))) then
((if h_1147 : ((Int.ofNat (2 ^ (sizenn (numtype_addrtype .I32)))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I32 (isub_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_2]⟩])
else []))
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_3 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .SUB), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (isub_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1148⟩ => ((if h_1149 : (0 ≤ (Int.tmod ((Int.ofNat ((2 ^ (sizenn (numtype_addrtype .I64))) + (proj_uN_0 i_1))) - (Int.ofNat (proj_uN_0 i_2))) (Int.ofNat (2 ^ (sizenn (numtype_addrtype .I64)))))) then
((if h_1150 : ((Int.ofNat (2 ^ (sizenn (numtype_addrtype .I64)))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I64 (isub_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_3]⟩])
else []))
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_4 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .MUL), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (imul_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1151⟩ => ((if h_1152 : ((2 ^ (sizenn (numtype_addrtype .I32))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I32 (imul_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_4]⟩])
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_5 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .MUL), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (imul_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1153⟩ => ((if h_1154 : ((2 ^ (sizenn (numtype_addrtype .I64))) ≠ 0) then
([⟨(some ([(.mk_num__0 .I64 (imul_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_5]⟩])
else []))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_6 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 (.DIV v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_fun_idiv__iiiio ((sizenn (numtype_addrtype .I32))) (v_sx) (i_1) (i_2)).flatMap fun ⟨o_174, h_1155⟩ => (match o_174 with
 | var_0 => (((interp_allL (fun (iter_10 : iN) => (interp_wf_uN_ii ((size (numtype_addrtype .I32))) (iter_10))) (Option.toList var_0)).flatMap fun ⟨_, h_1156⟩ => (((interp_allL (fun (iter_0_15 : iN) => (interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 iter_0_15)))) (Option.toList var_0)).flatMap fun ⟨_, h_1157⟩ => ([⟨(some (List.map (fun (iter_0_16 : iN) => ((.mk_num__0 .I32 iter_0_16) : num_)) (Option.toList var_0))), by subst_vars; first | (apply fun_binop_.fun_binop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_6]⟩]))))))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_7 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 (.DIV v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_fun_idiv__iiiio ((sizenn (numtype_addrtype .I64))) (v_sx) (i_1) (i_2)).flatMap fun ⟨o_175, h_1158⟩ => (match o_175 with
 | var_0 => (((interp_allL (fun (iter_11 : iN) => (interp_wf_uN_ii ((size (numtype_addrtype .I64))) (iter_11))) (Option.toList var_0)).flatMap fun ⟨_, h_1159⟩ => (((interp_allL (fun (iter_0_17 : iN) => (interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 iter_0_17)))) (Option.toList var_0)).flatMap fun ⟨_, h_1160⟩ => ([⟨(some (List.map (fun (iter_0_18 : iN) => ((.mk_num__0 .I64 iter_0_18) : num_)) (Option.toList var_0))), by subst_vars; first | (apply fun_binop_.fun_binop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_7]⟩]))))))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_8 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 (.REM v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_fun_irem__iiiio ((sizenn (numtype_addrtype .I32))) (v_sx) (i_1) (i_2)).flatMap fun ⟨o_176, h_1161⟩ => (match o_176 with
 | var_0 => (((interp_allL (fun (iter_12 : iN) => (interp_wf_uN_ii ((size (numtype_addrtype .I32))) (iter_12))) (Option.toList var_0)).flatMap fun ⟨_, h_1162⟩ => (((interp_allL (fun (iter_0_19 : iN) => (interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 iter_0_19)))) (Option.toList var_0)).flatMap fun ⟨_, h_1163⟩ => ([⟨(some (List.map (fun (iter_0_20 : iN) => ((.mk_num__0 .I32 iter_0_20) : num_)) (Option.toList var_0))), by subst_vars; first | (apply fun_binop_.fun_binop__case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_8]⟩]))))))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_9 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 (.REM v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_fun_irem__iiiio ((sizenn (numtype_addrtype .I64))) (v_sx) (i_1) (i_2)).flatMap fun ⟨o_177, h_1164⟩ => (match o_177 with
 | var_0 => (((interp_allL (fun (iter_13 : iN) => (interp_wf_uN_ii ((size (numtype_addrtype .I64))) (iter_13))) (Option.toList var_0)).flatMap fun ⟨_, h_1165⟩ => (((interp_allL (fun (iter_0_21 : iN) => (interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 iter_0_21)))) (Option.toList var_0)).flatMap fun ⟨_, h_1166⟩ => ([⟨(some (List.map (fun (iter_0_22 : iN) => ((.mk_num__0 .I64 iter_0_22) : num_)) (Option.toList var_0))), by subst_vars; first | (apply fun_binop_.fun_binop__case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_9]⟩]))))))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_10 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .AND), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (iand_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1167⟩ => ([⟨(some ([(.mk_num__0 .I32 (iand_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_10]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_11 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .AND), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (iand_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1168⟩ => ([⟨(some ([(.mk_num__0 .I64 (iand_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_11]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_12 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .OR), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (ior_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1169⟩ => ([⟨(some ([(.mk_num__0 .I32 (ior_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_12]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_13 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .OR), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (ior_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1170⟩ => ([⟨(some ([(.mk_num__0 .I64 (ior_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_13]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_14 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .XOR), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (ixor_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1171⟩ => ([⟨(some ([(.mk_num__0 .I32 (ixor_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_14]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_15 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .XOR), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (ixor_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1172⟩ => ([⟨(some ([(.mk_num__0 .I64 (ixor_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_15]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_16 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .SHL), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (ishl_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1173⟩ => ([⟨(some ([(.mk_num__0 .I32 (ishl_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_16]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_17 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .SHL), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (ishl_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1174⟩ => ([⟨(some ([(.mk_num__0 .I64 (ishl_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_17]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_18 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 (.SHR v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (ishr_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2)))).flatMap fun ⟨_, h_1175⟩ => ([⟨(some ([(.mk_num__0 .I32 (ishr_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_18]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_19 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 (.SHR v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (ishr_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2)))).flatMap fun ⟨_, h_1176⟩ => ([⟨(some ([(.mk_num__0 .I64 (ishr_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_19]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_20 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .ROTL), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (irotl_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1177⟩ => ([⟨(some ([(.mk_num__0 .I32 (irotl_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_20]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_21 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .ROTL), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (irotl_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1178⟩ => ([⟨(some ([(.mk_num__0 .I64 (irotl_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_21]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_22 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I32, (.mk_binop__0 .I32 .ROTR), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I32)) ((.mk_num__0 .I32 (irotr_ (sizenn (numtype_addrtype .I32)) i_1 i_2)))).flatMap fun ⟨_, h_1179⟩ => ([⟨(some ([(.mk_num__0 .I32 (irotr_ (sizenn (numtype_addrtype .I32)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_22]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_23 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .I64, (.mk_binop__0 .I64 .ROTR), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) => (((interp_wf_num__ii ((numtype_addrtype .I64)) ((.mk_num__0 .I64 (irotr_ (sizenn (numtype_addrtype .I64)) i_1 i_2)))).flatMap fun ⟨_, h_1180⟩ => ([⟨(some ([(.mk_num__0 .I64 (irotr_ (sizenn (numtype_addrtype .I64)) i_1 i_2))] : (List num_))), by subst_vars; first | (apply fun_binop_.fun_binop__case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_23]⟩])))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_24 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .ADD), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_14 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_14))) (fadd_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1181⟩ => (((interp_allL (fun (iter_0_23 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_23)))) (fadd_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1182⟩ => ([⟨(some (List.map (fun (iter_0_24 : fN) => ((.mk_num__1 .F32 iter_0_24) : num_)) (fadd_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_24]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_25 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .ADD), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_15 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_15))) (fadd_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1183⟩ => (((interp_allL (fun (iter_0_25 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_25)))) (fadd_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1184⟩ => ([⟨(some (List.map (fun (iter_0_26 : fN) => ((.mk_num__1 .F64 iter_0_26) : num_)) (fadd_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_25]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_26 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .SUB), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_16 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_16))) (fsub_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1185⟩ => (((interp_allL (fun (iter_0_27 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_27)))) (fsub_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1186⟩ => ([⟨(some (List.map (fun (iter_0_28 : fN) => ((.mk_num__1 .F32 iter_0_28) : num_)) (fsub_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_26]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_27 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .SUB), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_17 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_17))) (fsub_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1187⟩ => (((interp_allL (fun (iter_0_29 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_29)))) (fsub_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1188⟩ => ([⟨(some (List.map (fun (iter_0_30 : fN) => ((.mk_num__1 .F64 iter_0_30) : num_)) (fsub_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_27]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_28 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .MUL), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_18 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_18))) (fmul_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1189⟩ => (((interp_allL (fun (iter_0_31 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_31)))) (fmul_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1190⟩ => ([⟨(some (List.map (fun (iter_0_32 : fN) => ((.mk_num__1 .F32 iter_0_32) : num_)) (fmul_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_28]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_29 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .MUL), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_19 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_19))) (fmul_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1191⟩ => (((interp_allL (fun (iter_0_33 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_33)))) (fmul_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1192⟩ => ([⟨(some (List.map (fun (iter_0_34 : fN) => ((.mk_num__1 .F64 iter_0_34) : num_)) (fmul_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_29]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_30 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .DIV), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_20 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_20))) (fdiv_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1193⟩ => (((interp_allL (fun (iter_0_35 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_35)))) (fdiv_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1194⟩ => ([⟨(some (List.map (fun (iter_0_36 : fN) => ((.mk_num__1 .F32 iter_0_36) : num_)) (fdiv_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_30]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_31 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .DIV), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_21 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_21))) (fdiv_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1195⟩ => (((interp_allL (fun (iter_0_37 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_37)))) (fdiv_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1196⟩ => ([⟨(some (List.map (fun (iter_0_38 : fN) => ((.mk_num__1 .F64 iter_0_38) : num_)) (fdiv_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_31]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_32 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .MIN), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_22 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_22))) (fmin_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1197⟩ => (((interp_allL (fun (iter_0_39 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_39)))) (fmin_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1198⟩ => ([⟨(some (List.map (fun (iter_0_40 : fN) => ((.mk_num__1 .F32 iter_0_40) : num_)) (fmin_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_32]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_33 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .MIN), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_23 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_23))) (fmin_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1199⟩ => (((interp_allL (fun (iter_0_41 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_41)))) (fmin_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1200⟩ => ([⟨(some (List.map (fun (iter_0_42 : fN) => ((.mk_num__1 .F64 iter_0_42) : num_)) (fmin_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_33]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_34 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .MAX), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_24 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_24))) (fmax_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1201⟩ => (((interp_allL (fun (iter_0_43 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_43)))) (fmax_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1202⟩ => ([⟨(some (List.map (fun (iter_0_44 : fN) => ((.mk_num__1 .F32 iter_0_44) : num_)) (fmax_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_34]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_35 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .MAX), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_25 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_25))) (fmax_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1203⟩ => (((interp_allL (fun (iter_0_45 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_45)))) (fmax_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1204⟩ => ([⟨(some (List.map (fun (iter_0_46 : fN) => ((.mk_num__1 .F64 iter_0_46) : num_)) (fmax_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_35]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_36 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F32, (.mk_binop__1 .F32 .COPYSIGN), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) => (((interp_allL (fun (iter_26 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F32))) (iter_26))) (fcopysign_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1205⟩ => (((interp_allL (fun (iter_0_47 : fN) => (interp_wf_num__ii ((numtype_Fnn .F32)) ((.mk_num__1 .F32 iter_0_47)))) (fcopysign_ (sizenn (numtype_Fnn .F32)) f_1 f_2)).flatMap fun ⟨_, h_1206⟩ => ([⟨(some (List.map (fun (iter_0_48 : fN) => ((.mk_num__1 .F32 iter_0_48) : num_)) (fcopysign_ (sizenn (numtype_Fnn .F32)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_36]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio_fun_binop__case_37 (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | .F64, (.mk_binop__1 .F64 .COPYSIGN), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) => (((interp_allL (fun (iter_27 : fN) => (interp_wf_fN_ii ((sizenn (numtype_Fnn .F64))) (iter_27))) (fcopysign_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1207⟩ => (((interp_allL (fun (iter_0_49 : fN) => (interp_wf_num__ii ((numtype_Fnn .F64)) ((.mk_num__1 .F64 iter_0_49)))) (fcopysign_ (sizenn (numtype_Fnn .F64)) f_1 f_2)).flatMap fun ⟨_, h_1208⟩ => ([⟨(some (List.map (fun (iter_0_50 : fN) => ((.mk_num__1 .F64 iter_0_50) : num_)) (fcopysign_ (sizenn (numtype_Fnn .F64)) f_1 f_2))), by subst_vars; first | (apply fun_binop_.fun_binop__case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_binop_.fun_binop__case_37]⟩])))))
 | _, _, _, _ => []

def interp_fun_binop__iiiio (a0 : numtype) (a1 : binop_) (a2 : num_) (a3 : num_) : List {o : (Option (List num_)) // (fun_binop_ a0 a1 a2 a3 o)} :=
  interp_fun_binop__iiiio_fun_binop__case_0 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_1 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_2 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_3 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_4 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_5 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_6 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_7 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_8 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_9 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_10 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_11 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_12 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_13 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_14 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_15 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_16 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_17 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_18 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_19 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_20 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_21 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_22 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_23 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_24 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_25 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_26 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_27 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_28 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_29 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_30 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_31 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_32 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_33 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_34 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_35 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_36 a0 a1 a2 a3 ++
  interp_fun_binop__iiiio_fun_binop__case_37 a0 a1 a2 a3

def interp_fun_iextend__iiiio_fun_iextend__case_0 (a0 : N) (a1 : M) (a2 : sx) (a3 : iN) : List {o : iN // (fun_iextend_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, v_M, .U, i => ((if h_4243 : ((2 ^ v_M) ≠ 0) then
([⟨(.mk_uN ((proj_uN_0 i) % (2 ^ v_M))), by subst_vars; first | (apply fun_iextend_.fun_iextend__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_iextend_.fun_iextend__case_0]⟩])
else []))
 | _, _, _, _ => []

def interp_fun_iextend__iiiio_fun_iextend__case_1 (a0 : N) (a1 : M) (a2 : sx) (a3 : iN) : List {o : iN // (fun_iextend_ a0 a1 a2 a3 o)} :=
  match a0, a1, a2, a3 with
 | v_N, v_M, .S, i => (((interp_fun_signed__iio (v_M) (((proj_uN_0 i) % (2 ^ v_M)))).flatMap fun ⟨o_343, h_4244⟩ => (match o_343 with
 | var_1 => (((interp_fun_inv_signed__iio (v_N) (var_1)).flatMap fun ⟨o_344, h_4245⟩ => (match o_344 with
 | var_0 => ((if h_4246 : ((2 ^ v_M) ≠ 0) then
([⟨(.mk_uN var_0), by subst_vars; first | (apply fun_iextend_.fun_iextend__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_iextend_.fun_iextend__case_1]⟩])
else []))))))))
 | _, _, _, _ => []

def interp_fun_iextend__iiiio (a0 : N) (a1 : M) (a2 : sx) (a3 : iN) : List {o : iN // (fun_iextend_ a0 a1 a2 a3 o)} :=
  interp_fun_iextend__iiiio_fun_iextend__case_0 a0 a1 a2 a3 ++
  interp_fun_iextend__iiiio_fun_iextend__case_1 a0 a1 a2 a3

def interp_fun_unop__iiio_fun_unop__case_0 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I32, (.mk_unop__0 .I32 .CLZ), (.mk_num__0 .I32 i) => ([⟨(some ([(.mk_num__0 .I32 (iclz_ (sizenn (numtype_addrtype .I32)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_0]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_1 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I64, (.mk_unop__0 .I64 .CLZ), (.mk_num__0 .I64 i) => ([⟨(some ([(.mk_num__0 .I64 (iclz_ (sizenn (numtype_addrtype .I64)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_1]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_2 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I32, (.mk_unop__0 .I32 .CTZ), (.mk_num__0 .I32 i) => ([⟨(some ([(.mk_num__0 .I32 (ictz_ (sizenn (numtype_addrtype .I32)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_2]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_3 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I64, (.mk_unop__0 .I64 .CTZ), (.mk_num__0 .I64 i) => ([⟨(some ([(.mk_num__0 .I64 (ictz_ (sizenn (numtype_addrtype .I64)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_3]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_4 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I32, (.mk_unop__0 .I32 .POPCNT), (.mk_num__0 .I32 i) => ([⟨(some ([(.mk_num__0 .I32 (ipopcnt_ (sizenn (numtype_addrtype .I32)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_4]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_5 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I64, (.mk_unop__0 .I64 .POPCNT), (.mk_num__0 .I64 i) => ([⟨(some ([(.mk_num__0 .I64 (ipopcnt_ (sizenn (numtype_addrtype .I64)) i))] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_5]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_6 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I32, (.mk_unop__0 .I32 (.EXTEND (.mk_sz v_M))), (.mk_num__0 .I32 i) => (((interp_fun_iextend__iiiio ((sizenn (numtype_addrtype .I32))) (v_M) (.S) (i)).flatMap fun ⟨o_172, h_1134⟩ => (match o_172 with
 | var_0 => ([⟨(some ([(.mk_num__0 .I32 var_0)] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_6]⟩]))))
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_7 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .I64, (.mk_unop__0 .I64 (.EXTEND (.mk_sz v_M))), (.mk_num__0 .I64 i) => (((interp_fun_iextend__iiiio ((sizenn (numtype_addrtype .I64))) (v_M) (.S) (i)).flatMap fun ⟨o_173, h_1135⟩ => (match o_173 with
 | var_0 => ([⟨(some ([(.mk_num__0 .I64 var_0)] : (List num_))), by subst_vars; first | (apply fun_unop_.fun_unop__case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_7]⟩]))))
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_8 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .ABS), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_1 : fN) => ((.mk_num__1 .F32 iter_0_1) : num_)) (fabs_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_8]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_9 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .ABS), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_2 : fN) => ((.mk_num__1 .F64 iter_0_2) : num_)) (fabs_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_9]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_10 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .NEG), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_3 : fN) => ((.mk_num__1 .F32 iter_0_3) : num_)) (fneg_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_10]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_11 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .NEG), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_4 : fN) => ((.mk_num__1 .F64 iter_0_4) : num_)) (fneg_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_11]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_12 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .SQRT), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_5 : fN) => ((.mk_num__1 .F32 iter_0_5) : num_)) (fsqrt_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_12]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_13 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .SQRT), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_6 : fN) => ((.mk_num__1 .F64 iter_0_6) : num_)) (fsqrt_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_13]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_14 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .CEIL), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_7 : fN) => ((.mk_num__1 .F32 iter_0_7) : num_)) (fceil_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_14]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_15 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .CEIL), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_8 : fN) => ((.mk_num__1 .F64 iter_0_8) : num_)) (fceil_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_15]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_16 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .FLOOR), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_9 : fN) => ((.mk_num__1 .F32 iter_0_9) : num_)) (ffloor_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_16]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_17 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .FLOOR), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_10 : fN) => ((.mk_num__1 .F64 iter_0_10) : num_)) (ffloor_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_17]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_18 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .TRUNC), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_11 : fN) => ((.mk_num__1 .F32 iter_0_11) : num_)) (ftrunc_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_18]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_19 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .TRUNC), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_12 : fN) => ((.mk_num__1 .F64 iter_0_12) : num_)) (ftrunc_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_19]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_20 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F32, (.mk_unop__1 .F32 .NEAREST), (.mk_num__1 .F32 f) => ([⟨(some (List.map (fun (iter_0_13 : fN) => ((.mk_num__1 .F32 iter_0_13) : num_)) (fnearest_ (sizenn (numtype_Fnn .F32)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_20]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio_fun_unop__case_21 (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | .F64, (.mk_unop__1 .F64 .NEAREST), (.mk_num__1 .F64 f) => ([⟨(some (List.map (fun (iter_0_14 : fN) => ((.mk_num__1 .F64 iter_0_14) : num_)) (fnearest_ (sizenn (numtype_Fnn .F64)) f))), by subst_vars; first | (apply fun_unop_.fun_unop__case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unop_.fun_unop__case_21]⟩])
 | _, _, _ => []

def interp_fun_unop__iiio (a0 : numtype) (a1 : unop_) (a2 : num_) : List {o : (Option (List num_)) // (fun_unop_ a0 a1 a2 o)} :=
  interp_fun_unop__iiio_fun_unop__case_0 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_1 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_2 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_3 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_4 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_5 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_6 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_7 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_8 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_9 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_10 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_11 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_12 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_13 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_14 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_15 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_16 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_17 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_18 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_19 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_20 a0 a1 a2 ++
  interp_fun_unop__iiio_fun_unop__case_21 a0 a1 a2

mutual

partial def interp_wf_ref_i_ref_case_0 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_I31_NUM v_u31) => (((interp_wf_uN_ii (31) (v_u31)).flatMap fun ⟨_, h_1132⟩ => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_0]⟩])))
 | _ => []

partial def interp_wf_ref_i_ref_case_1 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | .REF_NULL_ADDR => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_1]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_2 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_STRUCT_ADDR v_structaddr) => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_2]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_3 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_ARRAY_ADDR v_arrayaddr) => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_3]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_4 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_FUNC_ADDR v_funcaddr) => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_4]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_5 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_EXN_ADDR v_exnaddr) => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_5]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_6 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_HOST_ADDR v_hostaddr) => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_6]⟩])
 | _ => []

partial def interp_wf_ref_i_ref_case_7 (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  match a0 with
 | (.REF_EXTERN v_ref) => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_1133⟩ => ([⟨(), by subst_vars; first | (apply wf_ref.ref_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_ref.ref_case_7]⟩])))
 | _ => []

partial def interp_wf_ref_i (a0 : ref) : List {o : Unit // (wf_ref a0)} :=
  interp_wf_ref_i_ref_case_0 a0 ++
  interp_wf_ref_i_ref_case_1 a0 ++
  interp_wf_ref_i_ref_case_2 a0 ++
  interp_wf_ref_i_ref_case_3 a0 ++
  interp_wf_ref_i_ref_case_4 a0 ++
  interp_wf_ref_i_ref_case_5 a0 ++
  interp_wf_ref_i_ref_case_6 a0 ++
  interp_wf_ref_i_ref_case_7 a0

end

def interp_wf_val_i_val_case_0 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.CONST v_numtype var_0) => (((interp_wf_num__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1128⟩ => ([⟨(), by subst_vars; first | (apply wf_val.val_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_0]⟩])))
 | _ => []

def interp_wf_val_i_val_case_1 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.VCONST v_vectype var_0) => (((interp_wf_uN_ii ((vsize v_vectype)) (var_0)).flatMap fun ⟨_, h_1129⟩ => ([⟨(), by subst_vars; first | (apply wf_val.val_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_1]⟩])))
 | _ => []

def interp_wf_val_i_val_case_2 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_I31_NUM v_u31) => (((interp_wf_uN_ii (31) (v_u31)).flatMap fun ⟨_, h_1130⟩ => ([⟨(), by subst_vars; first | (apply wf_val.val_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_2]⟩])))
 | _ => []

def interp_wf_val_i_val_case_3 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | .REF_NULL_ADDR => ([⟨(), by subst_vars; first | (apply wf_val.val_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_3]⟩])
 | _ => []

def interp_wf_val_i_val_case_4 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_STRUCT_ADDR v_structaddr) => ([⟨(), by subst_vars; first | (apply wf_val.val_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_4]⟩])
 | _ => []

def interp_wf_val_i_val_case_5 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_ARRAY_ADDR v_arrayaddr) => ([⟨(), by subst_vars; first | (apply wf_val.val_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_5]⟩])
 | _ => []

def interp_wf_val_i_val_case_6 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_FUNC_ADDR v_funcaddr) => ([⟨(), by subst_vars; first | (apply wf_val.val_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_6]⟩])
 | _ => []

def interp_wf_val_i_val_case_7 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_EXN_ADDR v_exnaddr) => ([⟨(), by subst_vars; first | (apply wf_val.val_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_7]⟩])
 | _ => []

def interp_wf_val_i_val_case_8 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_HOST_ADDR v_hostaddr) => ([⟨(), by subst_vars; first | (apply wf_val.val_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_8]⟩])
 | _ => []

def interp_wf_val_i_val_case_9 (a0 : val) : List {o : Unit // (wf_val a0)} :=
  match a0 with
 | (.REF_EXTERN v_ref) => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_1131⟩ => ([⟨(), by subst_vars; first | (apply wf_val.val_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_val.val_case_9]⟩])))
 | _ => []

def interp_wf_val_i (a0 : val) : List {o : Unit // (wf_val a0)} :=
  interp_wf_val_i_val_case_0 a0 ++
  interp_wf_val_i_val_case_1 a0 ++
  interp_wf_val_i_val_case_2 a0 ++
  interp_wf_val_i_val_case_3 a0 ++
  interp_wf_val_i_val_case_4 a0 ++
  interp_wf_val_i_val_case_5 a0 ++
  interp_wf_val_i_val_case_6 a0 ++
  interp_wf_val_i_val_case_7 a0 ++
  interp_wf_val_i_val_case_8 a0 ++
  interp_wf_val_i_val_case_9 a0

mutual

partial def interp_wf_rectype_i_rectype_case_0 (a0 : rectype) : List {o : Unit // (wf_rectype a0)} :=
  match a0 with
 | (.REC var_0) => ((if h_4550 : ((List.length (List.map (fun (X_17397 : subtype) => X_17397) (proj_list_0 subtype var_0))) < (2 ^ 32)) then
(((interp_allL (fun (iter : subtype) => (interp_wf_subtype_i (iter))) (proj_list_0 subtype var_0)).flatMap fun ⟨_, h_4551⟩ => ([⟨(), by subst_vars; first | (apply wf_rectype.rectype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_rectype.rectype_case_0]⟩])))
else []))

partial def interp_wf_rectype_i (a0 : rectype) : List {o : Unit // (wf_rectype a0)} :=
  interp_wf_rectype_i_rectype_case_0 a0

partial def interp_wf_subtype_i_subtype_case_0 (a0 : subtype) : List {o : Unit // (wf_subtype a0)} :=
  match a0 with
 | (.SUB final_opt typeuse_lst v_comptype) => (((interp_allL (fun (v_typeuse : typeuse) => (interp_wf_typeuse_i (v_typeuse))) typeuse_lst).flatMap fun ⟨_, h_4548⟩ => (((interp_wf_comptype_i (v_comptype)).flatMap fun ⟨_, h_4549⟩ => ([⟨(), by subst_vars; first | (apply wf_subtype.subtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_subtype.subtype_case_0]⟩])))))

partial def interp_wf_subtype_i (a0 : subtype) : List {o : Unit // (wf_subtype a0)} :=
  interp_wf_subtype_i_subtype_case_0 a0

partial def interp_wf_typeuse_i_typeuse_case_0 (a0 : typeuse) : List {o : Unit // (wf_typeuse a0)} :=
  match a0 with
 | (._IDX v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_4158⟩ => ([⟨(), by subst_vars; first | (apply wf_typeuse.typeuse_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_typeuse.typeuse_case_0]⟩])))
 | _ => []

partial def interp_wf_typeuse_i_typeuse_case_1 (a0 : typeuse) : List {o : Unit // (wf_typeuse a0)} :=
  match a0 with
 | (._DEF v_rectype v_n) => (((interp_wf_rectype_i (v_rectype)).flatMap fun ⟨_, h_4159⟩ => ([⟨(), by subst_vars; first | (apply wf_typeuse.typeuse_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_typeuse.typeuse_case_1]⟩])))
 | _ => []

partial def interp_wf_typeuse_i_typeuse_case_2 (a0 : typeuse) : List {o : Unit // (wf_typeuse a0)} :=
  match a0 with
 | (.REC v_n) => ([⟨(), by subst_vars; first | (apply wf_typeuse.typeuse_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_typeuse.typeuse_case_2]⟩])
 | _ => []

partial def interp_wf_typeuse_i (a0 : typeuse) : List {o : Unit // (wf_typeuse a0)} :=
  interp_wf_typeuse_i_typeuse_case_0 a0 ++
  interp_wf_typeuse_i_typeuse_case_1 a0 ++
  interp_wf_typeuse_i_typeuse_case_2 a0

partial def interp_wf_comptype_i_comptype_case_0 (a0 : comptype) : List {o : Unit // (wf_comptype a0)} :=
  match a0 with
 | (.STRUCT var_0) => ((if h_4093 : ((List.length (List.map (fun (X_17394 : fieldtype) => X_17394) (proj_list_0 fieldtype var_0))) < (2 ^ 32)) then
(((interp_allL (fun (iter : fieldtype) => (interp_wf_fieldtype_i (iter))) (proj_list_0 fieldtype var_0)).flatMap fun ⟨_, h_4094⟩ => ([⟨(), by subst_vars; first | (apply wf_comptype.comptype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_comptype.comptype_case_0]⟩])))
else []))
 | _ => []

partial def interp_wf_comptype_i_comptype_case_1 (a0 : comptype) : List {o : Unit // (wf_comptype a0)} :=
  match a0 with
 | (.ARRAY v_fieldtype) => (((interp_wf_fieldtype_i (v_fieldtype)).flatMap fun ⟨_, h_4095⟩ => ([⟨(), by subst_vars; first | (apply wf_comptype.comptype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_comptype.comptype_case_1]⟩])))
 | _ => []

partial def interp_wf_comptype_i_comptype_case_2 (a0 : comptype) : List {o : Unit // (wf_comptype a0)} :=
  match a0 with
 | (.FUNC v_resulttype resulttype_0) => ((if h_4096 : ((List.length (List.map (fun (X_17395 : valtype) => X_17395) (proj_list_0 valtype v_resulttype))) < (2 ^ 32)) then
((if h_4097 : ((List.length (List.map (fun (X_17396 : valtype) => X_17396) (proj_list_0 valtype resulttype_0))) < (2 ^ 32)) then
(((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype v_resulttype)).flatMap fun ⟨_, h_4098⟩ => (((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype resulttype_0)).flatMap fun ⟨_, h_4099⟩ => ([⟨(), by subst_vars; first | (apply wf_comptype.comptype_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_comptype.comptype_case_2]⟩])))))
else []))
else []))
 | _ => []

partial def interp_wf_comptype_i (a0 : comptype) : List {o : Unit // (wf_comptype a0)} :=
  interp_wf_comptype_i_comptype_case_0 a0 ++
  interp_wf_comptype_i_comptype_case_1 a0 ++
  interp_wf_comptype_i_comptype_case_2 a0

partial def interp_wf_valtype_i_valtype_case_0 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .I32 => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_0]⟩])
 | _ => []

partial def interp_wf_valtype_i_valtype_case_1 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .I64 => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_1]⟩])
 | _ => []

partial def interp_wf_valtype_i_valtype_case_2 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .F32 => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_2]⟩])
 | _ => []

partial def interp_wf_valtype_i_valtype_case_3 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .F64 => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_3]⟩])
 | _ => []

partial def interp_wf_valtype_i_valtype_case_4 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .V128 => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_4]⟩])
 | _ => []

partial def interp_wf_valtype_i_valtype_case_5 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | (.REF null_opt v_heaptype) => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4154⟩ => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_5]⟩])))
 | _ => []

partial def interp_wf_valtype_i_valtype_case_6 (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  match a0 with
 | .BOT => ([⟨(), by subst_vars; first | (apply wf_valtype.valtype_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_valtype.valtype_case_6]⟩])
 | _ => []

partial def interp_wf_valtype_i (a0 : valtype) : List {o : Unit // (wf_valtype a0)} :=
  interp_wf_valtype_i_valtype_case_0 a0 ++
  interp_wf_valtype_i_valtype_case_1 a0 ++
  interp_wf_valtype_i_valtype_case_2 a0 ++
  interp_wf_valtype_i_valtype_case_3 a0 ++
  interp_wf_valtype_i_valtype_case_4 a0 ++
  interp_wf_valtype_i_valtype_case_5 a0 ++
  interp_wf_valtype_i_valtype_case_6 a0

partial def interp_wf_heaptype_i_heaptype_case_0 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .ANY => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_0]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_1 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .EQ => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_1]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_2 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .I31 => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_2]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_3 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .STRUCT => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_3]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_4 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .ARRAY => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_4]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_5 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .NONE => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_5]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_6 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .FUNC => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_6]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_7 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .NOFUNC => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_7]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_8 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .EXN => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_8]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_9 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .NOEXN => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_9]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_10 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .EXTERN => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_10]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_11 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .NOEXTERN => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_11]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_12 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | .BOT => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_12]⟩])
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_13 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | (._IDX v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_4180⟩ => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_13]⟩])))
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_14 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | (._DEF v_rectype v_n) => (((interp_wf_rectype_i (v_rectype)).flatMap fun ⟨_, h_4181⟩ => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_14]⟩])))
 | _ => []

partial def interp_wf_heaptype_i_heaptype_case_15 (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  match a0 with
 | (.REC v_n) => ([⟨(), by subst_vars; first | (apply wf_heaptype.heaptype_case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_heaptype.heaptype_case_15]⟩])
 | _ => []

partial def interp_wf_heaptype_i (a0 : heaptype) : List {o : Unit // (wf_heaptype a0)} :=
  interp_wf_heaptype_i_heaptype_case_0 a0 ++
  interp_wf_heaptype_i_heaptype_case_1 a0 ++
  interp_wf_heaptype_i_heaptype_case_2 a0 ++
  interp_wf_heaptype_i_heaptype_case_3 a0 ++
  interp_wf_heaptype_i_heaptype_case_4 a0 ++
  interp_wf_heaptype_i_heaptype_case_5 a0 ++
  interp_wf_heaptype_i_heaptype_case_6 a0 ++
  interp_wf_heaptype_i_heaptype_case_7 a0 ++
  interp_wf_heaptype_i_heaptype_case_8 a0 ++
  interp_wf_heaptype_i_heaptype_case_9 a0 ++
  interp_wf_heaptype_i_heaptype_case_10 a0 ++
  interp_wf_heaptype_i_heaptype_case_11 a0 ++
  interp_wf_heaptype_i_heaptype_case_12 a0 ++
  interp_wf_heaptype_i_heaptype_case_13 a0 ++
  interp_wf_heaptype_i_heaptype_case_14 a0 ++
  interp_wf_heaptype_i_heaptype_case_15 a0

partial def interp_wf_fieldtype_i_fieldtype_case_0 (a0 : fieldtype) : List {o : Unit // (wf_fieldtype a0)} :=
  match a0 with
 | (.mk_fieldtype mut_opt v_storagetype) => (((interp_wf_storagetype_i (v_storagetype)).flatMap fun ⟨_, h_4552⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldtype.fieldtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldtype.fieldtype_case_0]⟩])))

partial def interp_wf_fieldtype_i (a0 : fieldtype) : List {o : Unit // (wf_fieldtype a0)} :=
  interp_wf_fieldtype_i_fieldtype_case_0 a0

partial def interp_wf_storagetype_i_storagetype_case_0 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .I32 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_0]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_1 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .I64 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_1]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_2 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .F32 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_2]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_3 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .F64 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_3]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_4 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .V128 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_4]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_5 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | (.REF null_opt v_heaptype) => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4730⟩ => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_5]⟩])))
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_6 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .BOT => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_6]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_7 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .I8 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_7]⟩])
 | _ => []

partial def interp_wf_storagetype_i_storagetype_case_8 (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  match a0 with
 | .I16 => ([⟨(), by subst_vars; first | (apply wf_storagetype.storagetype_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storagetype.storagetype_case_8]⟩])
 | _ => []

partial def interp_wf_storagetype_i (a0 : storagetype) : List {o : Unit // (wf_storagetype a0)} :=
  interp_wf_storagetype_i_storagetype_case_0 a0 ++
  interp_wf_storagetype_i_storagetype_case_1 a0 ++
  interp_wf_storagetype_i_storagetype_case_2 a0 ++
  interp_wf_storagetype_i_storagetype_case_3 a0 ++
  interp_wf_storagetype_i_storagetype_case_4 a0 ++
  interp_wf_storagetype_i_storagetype_case_5 a0 ++
  interp_wf_storagetype_i_storagetype_case_6 a0 ++
  interp_wf_storagetype_i_storagetype_case_7 a0 ++
  interp_wf_storagetype_i_storagetype_case_8 a0

end

def interp_wf_deftype_i_deftype_case_0 (a0 : deftype) : List {o : Unit // (wf_deftype a0)} :=
  match a0 with
 | (._DEF v_rectype v_n) => (((interp_wf_rectype_i (v_rectype)).flatMap fun ⟨_, h_4091⟩ => ([⟨(), by subst_vars; first | (apply wf_deftype.deftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_deftype.deftype_case_0]⟩])))

def interp_wf_deftype_i (a0 : deftype) : List {o : Unit // (wf_deftype a0)} :=
  interp_wf_deftype_i_deftype_case_0 a0

def interp_wf_char_i_char_case_0 (a0 : char) : List {o : Unit // (wf_char a0)} :=
  match a0 with
 | (.mk_char i) => ((if h_4991 : (((i >= 0) ∧ (i <= 55295)) ∨ ((i >= 57344) ∧ (i <= 1114111))) then
([⟨(), by subst_vars; first | (apply wf_char.char_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_char.char_case_0]⟩])
else []))

def interp_wf_char_i (a0 : char) : List {o : Unit // (wf_char a0)} :=
  interp_wf_char_i_char_case_0 a0

def interp_wf_byte_i_byte_case_0 (a0 : byte) : List {o : Unit // (wf_byte a0)} :=
  match a0 with
 | (.mk_byte i) => ((if h_4125 : (i >= 0) then
((if h_4126 : (i <= 255) then
([⟨(), by subst_vars; first | (apply wf_byte.byte_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_byte.byte_case_0]⟩])
else []))
else []))

def interp_wf_byte_i (a0 : byte) : List {o : Unit // (wf_byte a0)} :=
  interp_wf_byte_i_byte_case_0 a0

def interp_fun_utf8_io_fun_utf8_case_1 (a0 : (List char)) : List {o : (List byte) // (fun_utf8 a0 o)} :=
  match a0 with
 | [ch] => ((if h_4944 : ((proj_char_0 ch) < 128) then
(((fun (b : byte) (h_4945 : ((.mk_byte (proj_char_0 ch)) : byte) = b) => (((interp_wf_byte_i ((.mk_byte (proj_char_0 ch)))).flatMap fun ⟨_, h_4946⟩ => ([⟨([b] : (List byte)), by subst_vars; first | (apply fun_utf8.fun_utf8_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_utf8.fun_utf8_case_1]⟩])))) ((.mk_byte (proj_char_0 ch)) : byte) rfl))
else []))
 | _ => []

def interp_fun_utf8_io (a0 : (List char)) : List {o : (List byte) // (fun_utf8 a0 o)} :=
  interp_fun_utf8_io_fun_utf8_case_1 a0

def interp_wf_name_i_name_case_0 (a0 : name) : List {o : Unit // (wf_name a0)} :=
  match a0 with
 | (.mk_name char_lst) => (((interp_fun_utf8_io (char_lst)).flatMap fun ⟨o_383, h_4866⟩ => (match o_383 with
 | var_0 => ((if h_4867 : ((List.length var_0) < (2 ^ 32)) then
(((interp_allL (fun (v_char : char) => (interp_wf_char_i (v_char))) char_lst).flatMap fun ⟨_, h_4868⟩ => ([⟨(), by subst_vars; first | (apply wf_name.name_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_name.name_case_0]⟩])))
else [])))))

def interp_wf_name_i (a0 : name) : List {o : Unit // (wf_name a0)} :=
  interp_wf_name_i_name_case_0 a0

def interp_wf_exportinst_i_exportinst_case_ (a0 : exportinst) : List {o : Unit // (wf_exportinst a0)} :=
  match a0 with
 | { NAME := var_0, ADDR := var_1 } => (((interp_wf_name_i (var_0)).flatMap fun ⟨_, h_4701⟩ => ([⟨(), by subst_vars; first | (apply wf_exportinst.exportinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_exportinst.exportinst_case_]⟩])))

def interp_wf_exportinst_i (a0 : exportinst) : List {o : Unit // (wf_exportinst a0)} :=
  interp_wf_exportinst_i_exportinst_case_ a0

def interp_wf_moduleinst_i_moduleinst_case_ (a0 : moduleinst) : List {o : Unit // (wf_moduleinst a0)} :=
  match a0 with
 | { TYPES := var_0_lst, TAGS := var_1_lst, GLOBALS := var_2_lst, MEMS := var_3_lst, TABLES := var_4_lst, FUNCS := var_5_lst, DATAS := var_6_lst, ELEMS := var_7_lst, EXPORTS := var_8_lst } => (((interp_allL (fun (var_0 : deftype) => (interp_wf_deftype_i (var_0))) var_0_lst).flatMap fun ⟨_, h_4529⟩ => (((interp_allL (fun (var_8 : exportinst) => (interp_wf_exportinst_i (var_8))) var_8_lst).flatMap fun ⟨_, h_4530⟩ => ([⟨(), by subst_vars; first | (apply wf_moduleinst.moduleinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_moduleinst.moduleinst_case_]⟩])))))

def interp_wf_moduleinst_i (a0 : moduleinst) : List {o : Unit // (wf_moduleinst a0)} :=
  interp_wf_moduleinst_i_moduleinst_case_ a0

def interp_wf_frame_i_frame_case_ (a0 : frame) : List {o : Unit // (wf_frame a0)} :=
  match a0 with
 | { LOCALS := var_0_opt_lst, MODULE := var_1 } => (((interp_allL (fun (var_0_opt : (Option val)) => (interp_allL (fun (var_0 : val) => (interp_wf_val_i (var_0))) (Option.toList var_0_opt))) var_0_opt_lst).flatMap fun ⟨_, h_4241⟩ => (((interp_wf_moduleinst_i (var_1)).flatMap fun ⟨_, h_4242⟩ => ([⟨(), by subst_vars; first | (apply wf_frame.frame_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_frame.frame_case_]⟩])))))

def interp_wf_frame_i (a0 : frame) : List {o : Unit // (wf_frame a0)} :=
  interp_wf_frame_i_frame_case_ a0

def interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 (a0 : Fnn) (a1 : M) (a2 : Fnn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Fnn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Fnn_1, M_1, Fnn_2, M_2, (.DEMOTE v_zero) => ((if h_4598 : ((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (sizenn2 (numtype_Fnn Fnn_2)))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2.vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2.vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0]⟩])
else []))
 | _, _, _, _, _ => []

def interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 (a0 : Fnn) (a1 : M) (a2 : Fnn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Fnn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Fnn_1, M_1, Fnn_2, M_2, .PROMOTELOW => ((if h_4599 : ((2 * (sizenn1 (numtype_Fnn Fnn_1))) = (sizenn2 (numtype_Fnn Fnn_2))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2.vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2.vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1]⟩])
else []))
 | _, _, _, _, _ => []

def interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii (a0 : Fnn) (a1 : M) (a2 : Fnn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Fnn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 a0 a1 a2 a3 a4 ++
  interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 a0 a1 a2 a3 a4

def interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0 (a0 : Fnn) (a1 : M) (a2 : Inn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Inn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Inn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Fnn_1, M_1, Inn_2, M_2, (.TRUNC_SAT v_sx zero_opt) => ((if h_4596 : (((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_addrtype Inn_2))) ∧ ((lsizenn2 (lanetype_addrtype Inn_2)) = 32)) ∧ (zero_opt = none)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_addrtype Inn_2)))) ∧ (zero_opt = (some .ZERO)))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Fnn_1_M_1_Inn_2_M_2.vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Fnn_1_M_1_Inn_2_M_2.vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0]⟩])
else []))
 | _, _, _, _, _ => []

def interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Inn_2_M_2_case_1 (a0 : Fnn) (a1 : M) (a2 : Inn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Inn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Inn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Fnn_1, M_1, Inn_2, M_2, (.RELAXED_TRUNC v_sx zero_opt) => ((if h_4597 : (((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_addrtype Inn_2))) ∧ ((lsizenn2 (lanetype_addrtype Inn_2)) = 32)) ∧ (zero_opt = none)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_addrtype Inn_2)))) ∧ (zero_opt = (some .ZERO)))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Fnn_1_M_1_Inn_2_M_2.vcvtop__Fnn_1_M_1_Inn_2_M_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Fnn_1_M_1_Inn_2_M_2.vcvtop__Fnn_1_M_1_Inn_2_M_2_case_1]⟩])
else []))
 | _, _, _, _, _ => []

def interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii (a0 : Fnn) (a1 : M) (a2 : Inn) (a3 : M) (a4 : vcvtop__Fnn_1_M_1_Inn_2_M_2) : List {o : Unit // (wf_vcvtop__Fnn_1_M_1_Inn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0 a0 a1 a2 a3 a4 ++
  interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii_vcvtop__Fnn_1_M_1_Inn_2_M_2_case_1 a0 a1 a2 a3 a4

def interp_wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 (a0 : Jnn) (a1 : M) (a2 : Fnn) (a3 : M) (a4 : vcvtop__Jnn_1_M_1_Fnn_2_M_2) : List {o : Unit // (wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Fnn_2, M_2, (.CONVERT half_opt v_sx) => ((if h_4595 : (((((sizenn2 (numtype_Fnn Fnn_2)) = (lsizenn1 (lanetype_Jnn Jnn_1))) ∧ ((lsizenn1 (lanetype_Jnn Jnn_1)) = 32)) ∧ (half_opt = none)) ∨ (((sizenn2 (numtype_Fnn Fnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ∧ (half_opt = (some .LOW)))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2.vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2.vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0]⟩])
else []))

def interp_wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2_iiiii (a0 : Jnn) (a1 : M) (a2 : Fnn) (a3 : M) (a4 : vcvtop__Jnn_1_M_1_Fnn_2_M_2) : List {o : Unit // (wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2_iiiii_vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 a0 a1 a2 a3 a4

def interp_wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vcvtop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, (.EXTEND v_half v_sx) => ((if h_4594 : ((lsizenn2 (lanetype_Jnn Jnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) then
([⟨(), by subst_vars; first | (apply wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2.vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2.vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0]⟩])
else []))

def interp_wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2_iiiii (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vcvtop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 a0 a1 a2 a3 a4

def interp_wf_vcvtop___iii_vcvtop___case_0 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : Unit // (wf_vcvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | shape_1, shape_2, (.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) => ((if h_4229 : (shape_1 = (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1))) then
((if h_4230 : (shape_2 = (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2))) then
(((interp_wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2_iiiii (Jnn_1) (M_1) (Jnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4231⟩ => ([⟨(), by subst_vars; first | (apply wf_vcvtop__.vcvtop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__.vcvtop___case_0]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_vcvtop___iii_vcvtop___case_1 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : Unit // (wf_vcvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | shape_1, shape_2, (.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x) => ((if h_4232 : (shape_1 = (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1))) then
((if h_4233 : (shape_2 = (.X (lanetype_Fnn Fnn_2) (.mk_dim M_2))) then
(((interp_wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2_iiiii (Jnn_1) (M_1) (Fnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4234⟩ => ([⟨(), by subst_vars; first | (apply wf_vcvtop__.vcvtop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__.vcvtop___case_1]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_vcvtop___iii_vcvtop___case_2 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : Unit // (wf_vcvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | shape_1, shape_2, (.mk_vcvtop___2 Fnn_1 M_1 Inn_2 M_2 var_x) => ((if h_4235 : (shape_1 = (.X (lanetype_Fnn Fnn_1) (.mk_dim M_1))) then
((if h_4236 : (shape_2 = (.X (lanetype_addrtype Inn_2) (.mk_dim M_2))) then
(((interp_wf_vcvtop__Fnn_1_M_1_Inn_2_M_2_iiiii (Fnn_1) (M_1) (Inn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4237⟩ => ([⟨(), by subst_vars; first | (apply wf_vcvtop__.vcvtop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__.vcvtop___case_2]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_vcvtop___iii_vcvtop___case_3 (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : Unit // (wf_vcvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | shape_1, shape_2, (.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x) => ((if h_4238 : (shape_1 = (.X (lanetype_Fnn Fnn_1) (.mk_dim M_1))) then
((if h_4239 : (shape_2 = (.X (lanetype_Fnn Fnn_2) (.mk_dim M_2))) then
(((interp_wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2_iiiii (Fnn_1) (M_1) (Fnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4240⟩ => ([⟨(), by subst_vars; first | (apply wf_vcvtop__.vcvtop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vcvtop__.vcvtop___case_3]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_vcvtop___iii (a0 : shape) (a1 : shape) (a2 : vcvtop__) : List {o : Unit // (wf_vcvtop__ a0 a1 a2)} :=
  interp_wf_vcvtop___iii_vcvtop___case_0 a0 a1 a2 ++
  interp_wf_vcvtop___iii_vcvtop___case_1 a0 a1 a2 ++
  interp_wf_vcvtop___iii_vcvtop___case_2 a0 a1 a2 ++
  interp_wf_vcvtop___iii_vcvtop___case_3 a0 a1 a2

def interp_wf_vextternop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextternop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, .RELAXED_DOT_ADDS => ((if h_4592 : ((4 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) then
((if h_4593 : ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32) then
([⟨(), by subst_vars; first | (apply wf_vextternop__Jnn_1_M_1_Jnn_2_M_2.vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextternop__Jnn_1_M_1_Jnn_2_M_2.vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0]⟩])
else []))
else []))

def interp_wf_vextternop__Jnn_1_M_1_Jnn_2_M_2_iiiii (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextternop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vextternop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 a0 a1 a2 a3 a4

def interp_wf_vextternop___iii_vextternop___case_0 (a0 : ishape) (a1 : ishape) (a2 : vextternop__) : List {o : Unit // (wf_vextternop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | ishape_1, ishape_2, (.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) => ((if h_4226 : (ishape_1 = (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) then
((if h_4227 : (ishape_2 = (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) then
(((interp_wf_vextternop__Jnn_1_M_1_Jnn_2_M_2_iiiii (Jnn_1) (M_1) (Jnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4228⟩ => ([⟨(), by subst_vars; first | (apply wf_vextternop__.vextternop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextternop__.vextternop___case_0]⟩])))
else []))
else []))

def interp_wf_vextternop___iii (a0 : ishape) (a1 : ishape) (a2 : vextternop__) : List {o : Unit // (wf_vextternop__ a0 a1 a2)} :=
  interp_wf_vextternop___iii_vextternop___case_0 a0 a1 a2

def interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, (.EXTMUL v_half v_sx) => ((if h_4586 : ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) then
((if h_4587 : ((lsizenn2 (lanetype_Jnn Jnn_2)) >= 16) then
([⟨(), by subst_vars; first | (apply wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, .DOTS => ((if h_4588 : ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) then
((if h_4589 : ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32) then
([⟨(), by subst_vars; first | (apply wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, .RELAXED_DOTS => ((if h_4590 : ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) then
((if h_4591 : ((lsizenn2 (lanetype_Jnn Jnn_2)) = 16) then
([⟨(), by subst_vars; first | (apply wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2]⟩])
else []))
else []))
 | _, _, _, _, _ => []

def interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 a0 a1 a2 a3 a4 ++
  interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 a0 a1 a2 a3 a4 ++
  interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 a0 a1 a2 a3 a4

def interp_wf_vextbinop___iii_vextbinop___case_0 (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) : List {o : Unit // (wf_vextbinop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | ishape_1, ishape_2, (.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) => ((if h_4223 : (ishape_1 = (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) then
((if h_4224 : (ishape_2 = (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) then
(((interp_wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2_iiiii (Jnn_1) (M_1) (Jnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4225⟩ => ([⟨(), by subst_vars; first | (apply wf_vextbinop__.vextbinop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextbinop__.vextbinop___case_0]⟩])))
else []))
else []))

def interp_wf_vextbinop___iii (a0 : ishape) (a1 : ishape) (a2 : vextbinop__) : List {o : Unit // (wf_vextbinop__ a0 a1 a2)} :=
  interp_wf_vextbinop___iii_vextbinop___case_0 a0 a1 a2

def interp_wf_vextunop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextunop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  match a0, a1, a2, a3, a4 with
 | Jnn_1, M_1, Jnn_2, M_2, (.EXTADD_PAIRWISE v_sx) => ((if h_4583 : (16 <= (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) then
((if h_4584 : ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) then
((if h_4585 : ((lsizenn2 (lanetype_Jnn Jnn_2)) <= 32) then
([⟨(), by subst_vars; first | (apply wf_vextunop__Jnn_1_M_1_Jnn_2_M_2.vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextunop__Jnn_1_M_1_Jnn_2_M_2.vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0]⟩])
else []))
else []))
else []))

def interp_wf_vextunop__Jnn_1_M_1_Jnn_2_M_2_iiiii (a0 : Jnn) (a1 : M) (a2 : Jnn) (a3 : M) (a4 : vextunop__Jnn_1_M_1_Jnn_2_M_2) : List {o : Unit // (wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 a0 a1 a2 a3 a4)} :=
  interp_wf_vextunop__Jnn_1_M_1_Jnn_2_M_2_iiiii_vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 a0 a1 a2 a3 a4

def interp_wf_vextunop___iii_vextunop___case_0 (a0 : ishape) (a1 : ishape) (a2 : vextunop__) : List {o : Unit // (wf_vextunop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | ishape_1, ishape_2, (.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) => ((if h_4220 : (ishape_1 = (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) then
((if h_4221 : (ishape_2 = (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) then
(((interp_wf_vextunop__Jnn_1_M_1_Jnn_2_M_2_iiiii (Jnn_1) (M_1) (Jnn_2) (M_2) (var_x)).flatMap fun ⟨_, h_4222⟩ => ([⟨(), by subst_vars; first | (apply wf_vextunop__.vextunop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vextunop__.vextunop___case_0]⟩])))
else []))
else []))

def interp_wf_vextunop___iii (a0 : ishape) (a1 : ishape) (a2 : vextunop__) : List {o : Unit // (wf_vextunop__ a0 a1 a2)} :=
  interp_wf_vextunop___iii_vextunop___case_0 a0 a1 a2

def interp_wf_vswizzlop__ii_vswizzlop__case_0 (a0 : bshape) (a1 : vswizzlop_) : List {o : Unit // (wf_vswizzlop_ a0 a1)} :=
  match a0, a1 with
 | v_bshape, (.mk_vswizzlop__0 v_M var_x) => ((if h_4219 : (v_bshape = (.mk_bshape (.X .I8 (.mk_dim v_M)))) then
([⟨(), by subst_vars; first | (apply wf_vswizzlop_.vswizzlop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vswizzlop_.vswizzlop__case_0]⟩])
else []))

def interp_wf_vswizzlop__ii (a0 : bshape) (a1 : vswizzlop_) : List {o : Unit // (wf_vswizzlop_ a0 a1)} :=
  interp_wf_vswizzlop__ii_vswizzlop__case_0 a0 a1

def interp_wf_bshape_i_bshape_case_0 (a0 : bshape) : List {o : Unit // (wf_bshape a0)} :=
  match a0 with
 | (.mk_bshape v_shape) => ((if h_4217 : ((fun_lanetype v_shape) = .I8) then
(((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_4218⟩ => ([⟨(), by subst_vars; first | (apply wf_bshape.bshape_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_bshape.bshape_case_0]⟩])))
else []))

def interp_wf_bshape_i (a0 : bshape) : List {o : Unit // (wf_bshape a0)} :=
  interp_wf_bshape_i_bshape_case_0 a0

def interp_wf_vshiftop__ii_vshiftop__case_0 (a0 : ishape) (a1 : vshiftop_) : List {o : Unit // (wf_vshiftop_ a0 a1)} :=
  match a0, a1 with
 | v_ishape, (.mk_vshiftop__0 v_Jnn v_M var_x) => ((if h_4216 : (v_ishape = (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))) then
([⟨(), by subst_vars; first | (apply wf_vshiftop_.vshiftop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vshiftop_.vshiftop__case_0]⟩])
else []))

def interp_wf_vshiftop__ii (a0 : ishape) (a1 : vshiftop_) : List {o : Unit // (wf_vshiftop_ a0 a1)} :=
  interp_wf_vshiftop__ii_vshiftop__case_0 a0 a1

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_0 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .EQ => ([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_0]⟩])
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_1 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .NE => ([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_1]⟩])
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_2 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.LT v_sx) => ((if h_4579 : (((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = .S)) then
([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_2]⟩])
else []))
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_3 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.GT v_sx) => ((if h_4580 : (((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = .S)) then
([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_3]⟩])
else []))
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_4 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.LE v_sx) => ((if h_4581 : (((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = .S)) then
([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_4]⟩])
else []))
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_5 (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, (.GE v_sx) => ((if h_4582 : (((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = .S)) then
([⟨(), by subst_vars; first | (apply wf_vrelop_Jnn_M.vrelop_Jnn_M_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_Jnn_M.vrelop_Jnn_M_case_5]⟩])
else []))
 | _, _, _ => []

def interp_wf_vrelop_Jnn_M_iii (a0 : Jnn) (a1 : M) (a2 : vrelop_Jnn_M) : List {o : Unit // (wf_vrelop_Jnn_M a0 a1 a2)} :=
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_0 a0 a1 a2 ++
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_1 a0 a1 a2 ++
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_2 a0 a1 a2 ++
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_3 a0 a1 a2 ++
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_4 a0 a1 a2 ++
  interp_wf_vrelop_Jnn_M_iii_vrelop_Jnn_M_case_5 a0 a1 a2

def interp_wf_vrelop__ii_vrelop__case_0 (a0 : shape) (a1 : vrelop_) : List {o : Unit // (wf_vrelop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vrelop__0 v_Jnn v_M var_x) => ((if h_4211 : (v_shape = (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) then
(((interp_wf_vrelop_Jnn_M_iii (v_Jnn) (v_M) (var_x)).flatMap fun ⟨_, h_4212⟩ => ([⟨(), by subst_vars; first | (apply wf_vrelop_.vrelop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_.vrelop__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_vrelop__ii_vrelop__case_1 (a0 : shape) (a1 : vrelop_) : List {o : Unit // (wf_vrelop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vrelop__1 v_Fnn v_M var_x) => ((if h_4213 : (v_shape = (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vrelop_.vrelop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vrelop_.vrelop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_vrelop__ii (a0 : shape) (a1 : vrelop_) : List {o : Unit // (wf_vrelop_ a0 a1)} :=
  interp_wf_vrelop__ii_vrelop__case_0 a0 a1 ++
  interp_wf_vrelop__ii_vrelop__case_1 a0 a1

def interp_wf_vtestop__ii_vtestop__case_0 (a0 : shape) (a1 : vtestop_) : List {o : Unit // (wf_vtestop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vtestop__0 v_Jnn v_M var_x) => ((if h_4210 : (v_shape = (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vtestop_.vtestop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vtestop_.vtestop__case_0]⟩])
else []))

def interp_wf_vtestop__ii (a0 : shape) (a1 : vtestop_) : List {o : Unit // (wf_vtestop_ a0 a1)} :=
  interp_wf_vtestop__ii_vtestop__case_0 a0 a1

def interp_wf_vternop__ii_vternop__case_0 (a0 : shape) (a1 : vternop_) : List {o : Unit // (wf_vternop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vternop__0 v_Jnn v_M var_x) => ((if h_4208 : (v_shape = (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vternop_.vternop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vternop_.vternop__case_0]⟩])
else []))
 | _, _ => []

def interp_wf_vternop__ii_vternop__case_1 (a0 : shape) (a1 : vternop_) : List {o : Unit // (wf_vternop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vternop__1 v_Fnn v_M var_x) => ((if h_4209 : (v_shape = (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vternop_.vternop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vternop_.vternop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_vternop__ii (a0 : shape) (a1 : vternop_) : List {o : Unit // (wf_vternop_ a0 a1)} :=
  interp_wf_vternop__ii_vternop__case_0 a0 a1 ++
  interp_wf_vternop__ii_vternop__case_1 a0 a1

def interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_0 (a0 : Jnn) (a1 : M) (a2 : vunop_Jnn_M) : List {o : Unit // (wf_vunop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .ABS => ([⟨(), by subst_vars; first | (apply wf_vunop_Jnn_M.vunop_Jnn_M_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vunop_Jnn_M.vunop_Jnn_M_case_0]⟩])
 | _, _, _ => []

def interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_1 (a0 : Jnn) (a1 : M) (a2 : vunop_Jnn_M) : List {o : Unit // (wf_vunop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .NEG => ([⟨(), by subst_vars; first | (apply wf_vunop_Jnn_M.vunop_Jnn_M_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vunop_Jnn_M.vunop_Jnn_M_case_1]⟩])
 | _, _, _ => []

def interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_2 (a0 : Jnn) (a1 : M) (a2 : vunop_Jnn_M) : List {o : Unit // (wf_vunop_Jnn_M a0 a1 a2)} :=
  match a0, a1, a2 with
 | v_Jnn, v_M, .POPCNT => ((if h_4570 : ((lsizenn (lanetype_Jnn v_Jnn)) = 8) then
([⟨(), by subst_vars; first | (apply wf_vunop_Jnn_M.vunop_Jnn_M_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vunop_Jnn_M.vunop_Jnn_M_case_2]⟩])
else []))
 | _, _, _ => []

def interp_wf_vunop_Jnn_M_iii (a0 : Jnn) (a1 : M) (a2 : vunop_Jnn_M) : List {o : Unit // (wf_vunop_Jnn_M a0 a1 a2)} :=
  interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_0 a0 a1 a2 ++
  interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_1 a0 a1 a2 ++
  interp_wf_vunop_Jnn_M_iii_vunop_Jnn_M_case_2 a0 a1 a2

def interp_wf_vunop__ii_vunop__case_0 (a0 : shape) (a1 : vunop_) : List {o : Unit // (wf_vunop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vunop__0 v_Jnn v_M var_x) => ((if h_4202 : (v_shape = (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) then
(((interp_wf_vunop_Jnn_M_iii (v_Jnn) (v_M) (var_x)).flatMap fun ⟨_, h_4203⟩ => ([⟨(), by subst_vars; first | (apply wf_vunop_.vunop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vunop_.vunop__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_vunop__ii_vunop__case_1 (a0 : shape) (a1 : vunop_) : List {o : Unit // (wf_vunop_ a0 a1)} :=
  match a0, a1 with
 | v_shape, (.mk_vunop__1 v_Fnn v_M var_x) => ((if h_4204 : (v_shape = (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) then
([⟨(), by subst_vars; first | (apply wf_vunop_.vunop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vunop_.vunop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_vunop__ii (a0 : shape) (a1 : vunop_) : List {o : Unit // (wf_vunop_ a0 a1)} :=
  interp_wf_vunop__ii_vunop__case_0 a0 a1 ++
  interp_wf_vunop__ii_vunop__case_1 a0 a1

def interp_wf_cvtop__Fnn_1_Fnn_2_iii_cvtop__Fnn_1_Fnn_2_case_0 (a0 : Fnn) (a1 : Fnn) (a2 : cvtop__Fnn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Fnn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Fnn_1, Fnn_2, .PROMOTE => ((if h_4568 : ((sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Fnn_1_Fnn_2.cvtop__Fnn_1_Fnn_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Fnn_1_Fnn_2.cvtop__Fnn_1_Fnn_2_case_0]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Fnn_1_Fnn_2_iii_cvtop__Fnn_1_Fnn_2_case_1 (a0 : Fnn) (a1 : Fnn) (a2 : cvtop__Fnn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Fnn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Fnn_1, Fnn_2, .DEMOTE => ((if h_4569 : ((sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Fnn_1_Fnn_2.cvtop__Fnn_1_Fnn_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Fnn_1_Fnn_2.cvtop__Fnn_1_Fnn_2_case_1]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Fnn_1_Fnn_2_iii (a0 : Fnn) (a1 : Fnn) (a2 : cvtop__Fnn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Fnn_2 a0 a1 a2)} :=
  interp_wf_cvtop__Fnn_1_Fnn_2_iii_cvtop__Fnn_1_Fnn_2_case_0 a0 a1 a2 ++
  interp_wf_cvtop__Fnn_1_Fnn_2_iii_cvtop__Fnn_1_Fnn_2_case_1 a0 a1 a2

def interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_0 (a0 : Fnn) (a1 : Inn) (a2 : cvtop__Fnn_1_Inn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Inn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Fnn_1, Inn_2, (.TRUNC v_sx) => ([⟨(), by subst_vars; first | (apply wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_0]⟩])
 | _, _, _ => []

def interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_1 (a0 : Fnn) (a1 : Inn) (a2 : cvtop__Fnn_1_Inn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Inn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Fnn_1, Inn_2, (.TRUNC_SAT v_sx) => ([⟨(), by subst_vars; first | (apply wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_1]⟩])
 | _, _, _ => []

def interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_2 (a0 : Fnn) (a1 : Inn) (a2 : cvtop__Fnn_1_Inn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Inn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Fnn_1, Inn_2, .REINTERPRET => ((if h_4567 : ((sizenn1 (numtype_Fnn Fnn_1)) = (sizenn2 (numtype_addrtype Inn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Fnn_1_Inn_2.cvtop__Fnn_1_Inn_2_case_2]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Fnn_1_Inn_2_iii (a0 : Fnn) (a1 : Inn) (a2 : cvtop__Fnn_1_Inn_2) : List {o : Unit // (wf_cvtop__Fnn_1_Inn_2 a0 a1 a2)} :=
  interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_0 a0 a1 a2 ++
  interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_1 a0 a1 a2 ++
  interp_wf_cvtop__Fnn_1_Inn_2_iii_cvtop__Fnn_1_Inn_2_case_2 a0 a1 a2

def interp_wf_cvtop__Inn_1_Fnn_2_iii_cvtop__Inn_1_Fnn_2_case_0 (a0 : Inn) (a1 : Fnn) (a2 : cvtop__Inn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Inn_1_Fnn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Inn_1, Fnn_2, (.CONVERT v_sx) => ([⟨(), by subst_vars; first | (apply wf_cvtop__Inn_1_Fnn_2.cvtop__Inn_1_Fnn_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Inn_1_Fnn_2.cvtop__Inn_1_Fnn_2_case_0]⟩])
 | _, _, _ => []

def interp_wf_cvtop__Inn_1_Fnn_2_iii_cvtop__Inn_1_Fnn_2_case_1 (a0 : Inn) (a1 : Fnn) (a2 : cvtop__Inn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Inn_1_Fnn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Inn_1, Fnn_2, .REINTERPRET => ((if h_4566 : ((sizenn1 (numtype_addrtype Inn_1)) = (sizenn2 (numtype_Fnn Fnn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Inn_1_Fnn_2.cvtop__Inn_1_Fnn_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Inn_1_Fnn_2.cvtop__Inn_1_Fnn_2_case_1]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Inn_1_Fnn_2_iii (a0 : Inn) (a1 : Fnn) (a2 : cvtop__Inn_1_Fnn_2) : List {o : Unit // (wf_cvtop__Inn_1_Fnn_2 a0 a1 a2)} :=
  interp_wf_cvtop__Inn_1_Fnn_2_iii_cvtop__Inn_1_Fnn_2_case_0 a0 a1 a2 ++
  interp_wf_cvtop__Inn_1_Fnn_2_iii_cvtop__Inn_1_Fnn_2_case_1 a0 a1 a2

def interp_wf_cvtop__Inn_1_Inn_2_iii_cvtop__Inn_1_Inn_2_case_0 (a0 : Inn) (a1 : Inn) (a2 : cvtop__Inn_1_Inn_2) : List {o : Unit // (wf_cvtop__Inn_1_Inn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Inn_1, Inn_2, (.EXTEND v_sx) => ((if h_4564 : ((sizenn1 (numtype_addrtype Inn_1)) < (sizenn2 (numtype_addrtype Inn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Inn_1_Inn_2.cvtop__Inn_1_Inn_2_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Inn_1_Inn_2.cvtop__Inn_1_Inn_2_case_0]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Inn_1_Inn_2_iii_cvtop__Inn_1_Inn_2_case_1 (a0 : Inn) (a1 : Inn) (a2 : cvtop__Inn_1_Inn_2) : List {o : Unit // (wf_cvtop__Inn_1_Inn_2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | Inn_1, Inn_2, .WRAP => ((if h_4565 : ((sizenn1 (numtype_addrtype Inn_1)) > (sizenn2 (numtype_addrtype Inn_2))) then
([⟨(), by subst_vars; first | (apply wf_cvtop__Inn_1_Inn_2.cvtop__Inn_1_Inn_2_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__Inn_1_Inn_2.cvtop__Inn_1_Inn_2_case_1]⟩])
else []))
 | _, _, _ => []

def interp_wf_cvtop__Inn_1_Inn_2_iii (a0 : Inn) (a1 : Inn) (a2 : cvtop__Inn_1_Inn_2) : List {o : Unit // (wf_cvtop__Inn_1_Inn_2 a0 a1 a2)} :=
  interp_wf_cvtop__Inn_1_Inn_2_iii_cvtop__Inn_1_Inn_2_case_0 a0 a1 a2 ++
  interp_wf_cvtop__Inn_1_Inn_2_iii_cvtop__Inn_1_Inn_2_case_1 a0 a1 a2

def interp_wf_cvtop___iii_cvtop___case_0 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) : List {o : Unit // (wf_cvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | numtype_1, numtype_2, (.mk_cvtop___0 Inn_1 Inn_2 var_x) => ((if h_4190 : (numtype_1 = (numtype_addrtype Inn_1)) then
((if h_4191 : (numtype_2 = (numtype_addrtype Inn_2)) then
(((interp_wf_cvtop__Inn_1_Inn_2_iii (Inn_1) (Inn_2) (var_x)).flatMap fun ⟨_, h_4192⟩ => ([⟨(), by subst_vars; first | (apply wf_cvtop__.cvtop___case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__.cvtop___case_0]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_cvtop___iii_cvtop___case_1 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) : List {o : Unit // (wf_cvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | numtype_1, numtype_2, (.mk_cvtop___1 Inn_1 Fnn_2 var_x) => ((if h_4193 : (numtype_1 = (numtype_addrtype Inn_1)) then
((if h_4194 : (numtype_2 = (numtype_Fnn Fnn_2)) then
(((interp_wf_cvtop__Inn_1_Fnn_2_iii (Inn_1) (Fnn_2) (var_x)).flatMap fun ⟨_, h_4195⟩ => ([⟨(), by subst_vars; first | (apply wf_cvtop__.cvtop___case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__.cvtop___case_1]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_cvtop___iii_cvtop___case_2 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) : List {o : Unit // (wf_cvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | numtype_1, numtype_2, (.mk_cvtop___2 Fnn_1 Inn_2 var_x) => ((if h_4196 : (numtype_1 = (numtype_Fnn Fnn_1)) then
((if h_4197 : (numtype_2 = (numtype_addrtype Inn_2)) then
(((interp_wf_cvtop__Fnn_1_Inn_2_iii (Fnn_1) (Inn_2) (var_x)).flatMap fun ⟨_, h_4198⟩ => ([⟨(), by subst_vars; first | (apply wf_cvtop__.cvtop___case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__.cvtop___case_2]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_cvtop___iii_cvtop___case_3 (a0 : numtype) (a1 : numtype) (a2 : cvtop__) : List {o : Unit // (wf_cvtop__ a0 a1 a2)} :=
  match a0, a1, a2 with
 | numtype_1, numtype_2, (.mk_cvtop___3 Fnn_1 Fnn_2 var_x) => ((if h_4199 : (numtype_1 = (numtype_Fnn Fnn_1)) then
((if h_4200 : (numtype_2 = (numtype_Fnn Fnn_2)) then
(((interp_wf_cvtop__Fnn_1_Fnn_2_iii (Fnn_1) (Fnn_2) (var_x)).flatMap fun ⟨_, h_4201⟩ => ([⟨(), by subst_vars; first | (apply wf_cvtop__.cvtop___case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_cvtop__.cvtop___case_3]⟩])))
else []))
else []))
 | _, _, _ => []

def interp_wf_cvtop___iii (a0 : numtype) (a1 : numtype) (a2 : cvtop__) : List {o : Unit // (wf_cvtop__ a0 a1 a2)} :=
  interp_wf_cvtop___iii_cvtop___case_0 a0 a1 a2 ++
  interp_wf_cvtop___iii_cvtop___case_1 a0 a1 a2 ++
  interp_wf_cvtop___iii_cvtop___case_2 a0 a1 a2 ++
  interp_wf_cvtop___iii_cvtop___case_3 a0 a1 a2

def interp_wf_relop__ii_relop__case_0 (a0 : numtype) (a1 : relop_) : List {o : Unit // (wf_relop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_relop__0 v_Inn var_x) => ((if h_4188 : (v_numtype = (numtype_addrtype v_Inn)) then
([⟨(), by subst_vars; first | (apply wf_relop_.relop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_relop_.relop__case_0]⟩])
else []))
 | _, _ => []

def interp_wf_relop__ii_relop__case_1 (a0 : numtype) (a1 : relop_) : List {o : Unit // (wf_relop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_relop__1 v_Fnn var_x) => ((if h_4189 : (v_numtype = (numtype_Fnn v_Fnn)) then
([⟨(), by subst_vars; first | (apply wf_relop_.relop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_relop_.relop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_relop__ii (a0 : numtype) (a1 : relop_) : List {o : Unit // (wf_relop_ a0 a1)} :=
  interp_wf_relop__ii_relop__case_0 a0 a1 ++
  interp_wf_relop__ii_relop__case_1 a0 a1

def interp_wf_testop__ii_testop__case_0 (a0 : numtype) (a1 : testop_) : List {o : Unit // (wf_testop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_testop__0 v_Inn var_x) => ((if h_4187 : (v_numtype = (numtype_addrtype v_Inn)) then
([⟨(), by subst_vars; first | (apply wf_testop_.testop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_testop_.testop__case_0]⟩])
else []))

def interp_wf_testop__ii (a0 : numtype) (a1 : testop_) : List {o : Unit // (wf_testop_ a0 a1)} :=
  interp_wf_testop__ii_testop__case_0 a0 a1

def interp_wf_binop__ii_binop__case_0 (a0 : numtype) (a1 : binop_) : List {o : Unit // (wf_binop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_binop__0 v_Inn var_x) => ((if h_4185 : (v_numtype = (numtype_addrtype v_Inn)) then
([⟨(), by subst_vars; first | (apply wf_binop_.binop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_binop_.binop__case_0]⟩])
else []))
 | _, _ => []

def interp_wf_binop__ii_binop__case_1 (a0 : numtype) (a1 : binop_) : List {o : Unit // (wf_binop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_binop__1 v_Fnn var_x) => ((if h_4186 : (v_numtype = (numtype_Fnn v_Fnn)) then
([⟨(), by subst_vars; first | (apply wf_binop_.binop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_binop_.binop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_binop__ii (a0 : numtype) (a1 : binop_) : List {o : Unit // (wf_binop_ a0 a1)} :=
  interp_wf_binop__ii_binop__case_0 a0 a1 ++
  interp_wf_binop__ii_binop__case_1 a0 a1

def interp_wf_sz_i_sz_case_0 (a0 : sz) : List {o : Unit // (wf_sz a0)} :=
  match a0 with
 | (.mk_sz i) => ((if h_4179 : ((((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64)) then
([⟨(), by subst_vars; first | (apply wf_sz.sz_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_sz.sz_case_0]⟩])
else []))

def interp_wf_sz_i (a0 : sz) : List {o : Unit // (wf_sz a0)} :=
  interp_wf_sz_i_sz_case_0 a0

def interp_wf_unop_Inn_ii_unop_Inn_case_0 (a0 : Inn) (a1 : unop_Inn) : List {o : Unit // (wf_unop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, .CLZ => ([⟨(), by subst_vars; first | (apply wf_unop_Inn.unop_Inn_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_Inn.unop_Inn_case_0]⟩])
 | _, _ => []

def interp_wf_unop_Inn_ii_unop_Inn_case_1 (a0 : Inn) (a1 : unop_Inn) : List {o : Unit // (wf_unop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, .CTZ => ([⟨(), by subst_vars; first | (apply wf_unop_Inn.unop_Inn_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_Inn.unop_Inn_case_1]⟩])
 | _, _ => []

def interp_wf_unop_Inn_ii_unop_Inn_case_2 (a0 : Inn) (a1 : unop_Inn) : List {o : Unit // (wf_unop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, .POPCNT => ([⟨(), by subst_vars; first | (apply wf_unop_Inn.unop_Inn_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_Inn.unop_Inn_case_2]⟩])
 | _, _ => []

def interp_wf_unop_Inn_ii_unop_Inn_case_3 (a0 : Inn) (a1 : unop_Inn) : List {o : Unit // (wf_unop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, (.EXTEND v_sz) => ((if h_4562 : ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) then
(((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4563⟩ => ([⟨(), by subst_vars; first | (apply wf_unop_Inn.unop_Inn_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_Inn.unop_Inn_case_3]⟩])))
else []))
 | _, _ => []

def interp_wf_unop_Inn_ii (a0 : Inn) (a1 : unop_Inn) : List {o : Unit // (wf_unop_Inn a0 a1)} :=
  interp_wf_unop_Inn_ii_unop_Inn_case_0 a0 a1 ++
  interp_wf_unop_Inn_ii_unop_Inn_case_1 a0 a1 ++
  interp_wf_unop_Inn_ii_unop_Inn_case_2 a0 a1 ++
  interp_wf_unop_Inn_ii_unop_Inn_case_3 a0 a1

def interp_wf_unop__ii_unop__case_0 (a0 : numtype) (a1 : unop_) : List {o : Unit // (wf_unop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_unop__0 v_Inn var_x) => ((if h_4182 : (v_numtype = (numtype_addrtype v_Inn)) then
(((interp_wf_unop_Inn_ii (v_Inn) (var_x)).flatMap fun ⟨_, h_4183⟩ => ([⟨(), by subst_vars; first | (apply wf_unop_.unop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_.unop__case_0]⟩])))
else []))
 | _, _ => []

def interp_wf_unop__ii_unop__case_1 (a0 : numtype) (a1 : unop_) : List {o : Unit // (wf_unop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_unop__1 v_Fnn var_x) => ((if h_4184 : (v_numtype = (numtype_Fnn v_Fnn)) then
([⟨(), by subst_vars; first | (apply wf_unop_.unop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_unop_.unop__case_1]⟩])
else []))
 | _, _ => []

def interp_wf_unop__ii (a0 : numtype) (a1 : unop_) : List {o : Unit // (wf_unop_ a0 a1)} :=
  interp_wf_unop__ii_unop__case_0 a0 a1 ++
  interp_wf_unop__ii_unop__case_1 a0 a1

def interp_wf_vloadop__ii_vloadop__case_0 (a0 : vectype) (a1 : vloadop_) : List {o : Unit // (wf_vloadop_ a0 a1)} :=
  match a0, a1 with
 | v_vectype, (.SHAPEX_ v_sz v_M v_sx) => ((if h_4172 : ((Rat.ofInt (Int.ofNat ((proj_sz_0 v_sz) * v_M))) = ((Rat.ofInt (Int.ofNat (vsize v_vectype))) / (Rat.ofInt (Int.ofNat 2)))) then
((if h_4173 : (v_M > 1) then
(((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4174⟩ => ((if h_4175 : ((Rat.ofInt (Int.ofNat 2)) ≠ 0) then
([⟨(), by subst_vars; first | (apply wf_vloadop_.vloadop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vloadop_.vloadop__case_0]⟩])
else []))))
else []))
else []))
 | _, _ => []

def interp_wf_vloadop__ii_vloadop__case_1 (a0 : vectype) (a1 : vloadop_) : List {o : Unit // (wf_vloadop_ a0 a1)} :=
  match a0, a1 with
 | v_vectype, (.SPLAT v_sz) => (((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4176⟩ => ([⟨(), by subst_vars; first | (apply wf_vloadop_.vloadop__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vloadop_.vloadop__case_1]⟩])))
 | _, _ => []

def interp_wf_vloadop__ii_vloadop__case_2 (a0 : vectype) (a1 : vloadop_) : List {o : Unit // (wf_vloadop_ a0 a1)} :=
  match a0, a1 with
 | v_vectype, (.ZERO v_sz) => ((if h_4177 : ((proj_sz_0 v_sz) >= 32) then
(((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4178⟩ => ([⟨(), by subst_vars; first | (apply wf_vloadop_.vloadop__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_vloadop_.vloadop__case_2]⟩])))
else []))
 | _, _ => []

def interp_wf_vloadop__ii (a0 : vectype) (a1 : vloadop_) : List {o : Unit // (wf_vloadop_ a0 a1)} :=
  interp_wf_vloadop__ii_vloadop__case_0 a0 a1 ++
  interp_wf_vloadop__ii_vloadop__case_1 a0 a1 ++
  interp_wf_vloadop__ii_vloadop__case_2 a0 a1

def interp_wf_storeop_Inn_ii_storeop_Inn_case_0 (a0 : Inn) (a1 : storeop_Inn) : List {o : Unit // (wf_storeop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, (.mk_storeop_Inn v_sz) => ((if h_4560 : ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) then
(((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4561⟩ => ([⟨(), by subst_vars; first | (apply wf_storeop_Inn.storeop_Inn_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storeop_Inn.storeop_Inn_case_0]⟩])))
else []))

def interp_wf_storeop_Inn_ii (a0 : Inn) (a1 : storeop_Inn) : List {o : Unit // (wf_storeop_Inn a0 a1)} :=
  interp_wf_storeop_Inn_ii_storeop_Inn_case_0 a0 a1

def interp_wf_storeop__ii_storeop__case_0 (a0 : numtype) (a1 : storeop_) : List {o : Unit // (wf_storeop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_storeop__0 v_Inn var_x) => ((if h_4170 : (v_numtype = (numtype_addrtype v_Inn)) then
(((interp_wf_storeop_Inn_ii (v_Inn) (var_x)).flatMap fun ⟨_, h_4171⟩ => ([⟨(), by subst_vars; first | (apply wf_storeop_.storeop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_storeop_.storeop__case_0]⟩])))
else []))

def interp_wf_storeop__ii (a0 : numtype) (a1 : storeop_) : List {o : Unit // (wf_storeop_ a0 a1)} :=
  interp_wf_storeop__ii_storeop__case_0 a0 a1

def interp_wf_loadop_Inn_ii_loadop_Inn_case_0 (a0 : Inn) (a1 : loadop_Inn) : List {o : Unit // (wf_loadop_Inn a0 a1)} :=
  match a0, a1 with
 | v_Inn, (.mk_loadop_Inn v_sz v_sx) => ((if h_4558 : ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) then
(((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_4559⟩ => ([⟨(), by subst_vars; first | (apply wf_loadop_Inn.loadop_Inn_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_loadop_Inn.loadop_Inn_case_0]⟩])))
else []))

def interp_wf_loadop_Inn_ii (a0 : Inn) (a1 : loadop_Inn) : List {o : Unit // (wf_loadop_Inn a0 a1)} :=
  interp_wf_loadop_Inn_ii_loadop_Inn_case_0 a0 a1

def interp_wf_loadop__ii_loadop__case_0 (a0 : numtype) (a1 : loadop_) : List {o : Unit // (wf_loadop_ a0 a1)} :=
  match a0, a1 with
 | v_numtype, (.mk_loadop__0 v_Inn var_x) => ((if h_4168 : (v_numtype = (numtype_addrtype v_Inn)) then
(((interp_wf_loadop_Inn_ii (v_Inn) (var_x)).flatMap fun ⟨_, h_4169⟩ => ([⟨(), by subst_vars; first | (apply wf_loadop_.loadop__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_loadop_.loadop__case_0]⟩])))
else []))

def interp_wf_loadop__ii (a0 : numtype) (a1 : loadop_) : List {o : Unit // (wf_loadop_ a0 a1)} :=
  interp_wf_loadop__ii_loadop__case_0 a0 a1

def interp_wf_memarg_i_memarg_case_ (a0 : memarg) : List {o : Unit // (wf_memarg a0)} :=
  match a0 with
 | { ALIGN := var_0, OFFSET := var_1 } => (((interp_wf_uN_ii (32) (var_0)).flatMap fun ⟨_, h_4166⟩ => (((interp_wf_uN_ii (64) (var_1)).flatMap fun ⟨_, h_4167⟩ => ([⟨(), by subst_vars; first | (apply wf_memarg.memarg_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_memarg.memarg_case_]⟩])))))

def interp_wf_memarg_i (a0 : memarg) : List {o : Unit // (wf_memarg a0)} :=
  interp_wf_memarg_i_memarg_case_ a0

def interp_wf_catch_i_catch_case_0 (a0 : «catch») : List {o : Unit // (wf_catch a0)} :=
  match a0 with
 | (.CATCH v_tagidx v_labelidx) => (((interp_wf_uN_ii (32) (v_tagidx)).flatMap fun ⟨_, h_4160⟩ => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_4161⟩ => ([⟨(), by subst_vars; first | (apply wf_catch.catch_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_catch.catch_case_0]⟩])))))
 | _ => []

def interp_wf_catch_i_catch_case_1 (a0 : «catch») : List {o : Unit // (wf_catch a0)} :=
  match a0 with
 | (.CATCH_REF v_tagidx v_labelidx) => (((interp_wf_uN_ii (32) (v_tagidx)).flatMap fun ⟨_, h_4162⟩ => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_4163⟩ => ([⟨(), by subst_vars; first | (apply wf_catch.catch_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_catch.catch_case_1]⟩])))))
 | _ => []

def interp_wf_catch_i_catch_case_2 (a0 : «catch») : List {o : Unit // (wf_catch a0)} :=
  match a0 with
 | (.CATCH_ALL v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_4164⟩ => ([⟨(), by subst_vars; first | (apply wf_catch.catch_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_catch.catch_case_2]⟩])))
 | _ => []

def interp_wf_catch_i_catch_case_3 (a0 : «catch») : List {o : Unit // (wf_catch a0)} :=
  match a0 with
 | (.CATCH_ALL_REF v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_4165⟩ => ([⟨(), by subst_vars; first | (apply wf_catch.catch_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_catch.catch_case_3]⟩])))
 | _ => []

def interp_wf_catch_i (a0 : «catch») : List {o : Unit // (wf_catch a0)} :=
  interp_wf_catch_i_catch_case_0 a0 ++
  interp_wf_catch_i_catch_case_1 a0 ++
  interp_wf_catch_i_catch_case_2 a0 ++
  interp_wf_catch_i_catch_case_3 a0

def interp_wf_reftype_i_reftype_case_0 (a0 : reftype) : List {o : Unit // (wf_reftype a0)} :=
  match a0 with
 | (.REF null_opt v_heaptype) => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4157⟩ => ([⟨(), by subst_vars; first | (apply wf_reftype.reftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_reftype.reftype_case_0]⟩])))

def interp_wf_reftype_i (a0 : reftype) : List {o : Unit // (wf_reftype a0)} :=
  interp_wf_reftype_i_reftype_case_0 a0

def interp_wf_blocktype_i_blocktype_case_0 (a0 : blocktype) : List {o : Unit // (wf_blocktype a0)} :=
  match a0 with
 | (._RESULT valtype_opt) => (((interp_allL (fun (v_valtype : valtype) => (interp_wf_valtype_i (v_valtype))) (Option.toList valtype_opt)).flatMap fun ⟨_, h_4155⟩ => ([⟨(), by subst_vars; first | (apply wf_blocktype.blocktype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_blocktype.blocktype_case_0]⟩])))
 | _ => []

def interp_wf_blocktype_i_blocktype_case_1 (a0 : blocktype) : List {o : Unit // (wf_blocktype a0)} :=
  match a0 with
 | (._IDX v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_4156⟩ => ([⟨(), by subst_vars; first | (apply wf_blocktype.blocktype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_blocktype.blocktype_case_1]⟩])))
 | _ => []

def interp_wf_blocktype_i (a0 : blocktype) : List {o : Unit // (wf_blocktype a0)} :=
  interp_wf_blocktype_i_blocktype_case_0 a0 ++
  interp_wf_blocktype_i_blocktype_case_1 a0

mutual

partial def interp_wf_instr_i_instr_case_0 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .NOP => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_0]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_1 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .UNREACHABLE => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_1]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_2 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .DROP => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_2]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_3 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.SELECT valtype_lst_opt) => (((interp_allL (fun (valtype_lst : (List valtype)) => (interp_allL (fun (v_valtype : valtype) => (interp_wf_valtype_i (v_valtype))) valtype_lst)) (Option.toList valtype_lst_opt)).flatMap fun ⟨_, h_970⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_3]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_4 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BLOCK v_blocktype instr_lst) => (((interp_wf_blocktype_i (v_blocktype)).flatMap fun ⟨_, h_971⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_972⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_4]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_5 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LOOP v_blocktype instr_lst) => (((interp_wf_blocktype_i (v_blocktype)).flatMap fun ⟨_, h_973⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_974⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_5]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_6 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.IFELSE v_blocktype instr_lst instr_lst_0_lst) => (((interp_wf_blocktype_i (v_blocktype)).flatMap fun ⟨_, h_975⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_976⟩ => (((interp_allL (fun (instr_lst_0 : instr) => (interp_wf_instr_i (instr_lst_0))) instr_lst_0_lst).flatMap fun ⟨_, h_977⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_6]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_7 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_978⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_7]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_8 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_IF v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_979⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_8]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_9 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_TABLE labelidx_lst v_labelidx) => (((interp_allL (fun (v_labelidx : labelidx) => (interp_wf_uN_ii (32) (v_labelidx))) labelidx_lst).flatMap fun ⟨_, h_980⟩ => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_981⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_9]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_10 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_ON_NULL v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_982⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_10]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_11 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_ON_NON_NULL v_labelidx) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_983⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_11 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_11]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_12 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_ON_CAST v_labelidx v_reftype reftype_0) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_984⟩ => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_985⟩ => (((interp_wf_reftype_i (reftype_0)).flatMap fun ⟨_, h_986⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_12 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_12]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_13 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BR_ON_CAST_FAIL v_labelidx v_reftype reftype_0) => (((interp_wf_uN_ii (32) (v_labelidx)).flatMap fun ⟨_, h_987⟩ => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_988⟩ => (((interp_wf_reftype_i (reftype_0)).flatMap fun ⟨_, h_989⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_13 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_13]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_14 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.CALL v_funcidx) => (((interp_wf_uN_ii (32) (v_funcidx)).flatMap fun ⟨_, h_990⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_14 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_14]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_15 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.CALL_REF v_typeuse) => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_991⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_15 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_15]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_16 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.CALL_INDIRECT v_tableidx v_typeuse) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_992⟩ => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_993⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_16 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_16]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_17 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .RETURN => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_17 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_17]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_18 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.RETURN_CALL v_funcidx) => (((interp_wf_uN_ii (32) (v_funcidx)).flatMap fun ⟨_, h_994⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_18 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_18]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_19 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.RETURN_CALL_REF v_typeuse) => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_995⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_19 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_19]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_20 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.RETURN_CALL_INDIRECT v_tableidx v_typeuse) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_996⟩ => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_997⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_20 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_20]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_21 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.THROW v_tagidx) => (((interp_wf_uN_ii (32) (v_tagidx)).flatMap fun ⟨_, h_998⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_21 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_21]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_22 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .THROW_REF => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_22 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_22]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_23 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TRY_TABLE v_blocktype var_0 instr_lst) => ((if h_999 : ((List.length (List.map (fun (X_17400 : «catch») => X_17400) (proj_list_0 «catch» var_0))) < (2 ^ 32)) then
(((interp_wf_blocktype_i (v_blocktype)).flatMap fun ⟨_, h_1000⟩ => (((interp_allL (fun (iter : «catch») => (interp_wf_catch_i (iter))) (proj_list_0 «catch» var_0)).flatMap fun ⟨_, h_1001⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_1002⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_23 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_23]⟩])))))))
else []))
 | _ => []

partial def interp_wf_instr_i_instr_case_24 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LOCAL_GET v_localidx) => (((interp_wf_uN_ii (32) (v_localidx)).flatMap fun ⟨_, h_1003⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_24 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_24]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_25 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LOCAL_SET v_localidx) => (((interp_wf_uN_ii (32) (v_localidx)).flatMap fun ⟨_, h_1004⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_25 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_25]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_26 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LOCAL_TEE v_localidx) => (((interp_wf_uN_ii (32) (v_localidx)).flatMap fun ⟨_, h_1005⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_26 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_26]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_27 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.GLOBAL_GET v_globalidx) => (((interp_wf_uN_ii (32) (v_globalidx)).flatMap fun ⟨_, h_1006⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_27 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_27]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_28 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.GLOBAL_SET v_globalidx) => (((interp_wf_uN_ii (32) (v_globalidx)).flatMap fun ⟨_, h_1007⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_28 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_28]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_29 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_GET v_tableidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1008⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_29 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_29]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_30 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_SET v_tableidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1009⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_30 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_30]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_31 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_SIZE v_tableidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1010⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_31]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_32 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_GROW v_tableidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1011⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_32 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_32]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_33 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_FILL v_tableidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1012⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_33 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_33]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_34 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_COPY v_tableidx tableidx_0) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1013⟩ => (((interp_wf_uN_ii (32) (tableidx_0)).flatMap fun ⟨_, h_1014⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_34 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_34]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_35 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TABLE_INIT v_tableidx v_elemidx) => (((interp_wf_uN_ii (32) (v_tableidx)).flatMap fun ⟨_, h_1015⟩ => (((interp_wf_uN_ii (32) (v_elemidx)).flatMap fun ⟨_, h_1016⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_35 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_35]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_36 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ELEM_DROP v_elemidx) => (((interp_wf_uN_ii (32) (v_elemidx)).flatMap fun ⟨_, h_1017⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_36 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_36]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_37 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LOAD v_numtype var_0_opt v_memidx v_memarg) => (((interp_allL (fun (var_0 : loadop_) => (interp_wf_loadop__ii (v_numtype) (var_0))) (Option.toList var_0_opt)).flatMap fun ⟨_, h_1018⟩ => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1019⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1020⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_37 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_37]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_38 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.STORE v_numtype var_0_opt v_memidx v_memarg) => (((interp_allL (fun (var_0 : storeop_) => (interp_wf_storeop__ii (v_numtype) (var_0))) (Option.toList var_0_opt)).flatMap fun ⟨_, h_1021⟩ => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1022⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1023⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_38 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_38]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_39 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VLOAD v_vectype var_0_opt v_memidx v_memarg) => (((interp_allL (fun (var_0 : vloadop_) => (interp_wf_vloadop__ii (v_vectype) (var_0))) (Option.toList var_0_opt)).flatMap fun ⟨_, h_1024⟩ => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1025⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1026⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_39 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_39]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_40 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) => (((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_1027⟩ => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1028⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1029⟩ => (((interp_wf_uN_ii (8) (v_laneidx)).flatMap fun ⟨_, h_1030⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_40 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_40]⟩])))))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_41 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSTORE v_vectype v_memidx v_memarg) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1031⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1032⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_41 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_41]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_42 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) => (((interp_wf_sz_i (v_sz)).flatMap fun ⟨_, h_1033⟩ => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1034⟩ => (((interp_wf_memarg_i (v_memarg)).flatMap fun ⟨_, h_1035⟩ => (((interp_wf_uN_ii (8) (v_laneidx)).flatMap fun ⟨_, h_1036⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_42 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_42]⟩])))))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_43 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.MEMORY_SIZE v_memidx) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1037⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_43 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_43]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_44 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.MEMORY_GROW v_memidx) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1038⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_44 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_44]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_45 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.MEMORY_FILL v_memidx) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1039⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_45 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_45]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_46 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.MEMORY_COPY v_memidx memidx_0) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1040⟩ => (((interp_wf_uN_ii (32) (memidx_0)).flatMap fun ⟨_, h_1041⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_46 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_46]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_47 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.MEMORY_INIT v_memidx v_dataidx) => (((interp_wf_uN_ii (32) (v_memidx)).flatMap fun ⟨_, h_1042⟩ => (((interp_wf_uN_ii (32) (v_dataidx)).flatMap fun ⟨_, h_1043⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_47 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_47]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_48 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.DATA_DROP v_dataidx) => (((interp_wf_uN_ii (32) (v_dataidx)).flatMap fun ⟨_, h_1044⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_48 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_48]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_49 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_NULL v_heaptype) => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_1045⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_49 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_49]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_50 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .REF_IS_NULL => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_50 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_50]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_51 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .REF_AS_NON_NULL => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_51 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_51]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_52 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .REF_EQ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_52 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_52]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_53 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_TEST v_reftype) => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_1046⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_53 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_53]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_54 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_CAST v_reftype) => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_1047⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_54 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_54]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_55 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_FUNC v_funcidx) => (((interp_wf_uN_ii (32) (v_funcidx)).flatMap fun ⟨_, h_1048⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_55 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_55]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_56 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .REF_I31 => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_56 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_56]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_57 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.I31_GET v_sx) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_57 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_57]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_58 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.STRUCT_NEW v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1049⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_58 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_58]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_59 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.STRUCT_NEW_DEFAULT v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1050⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_59 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_59]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_60 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.STRUCT_GET sx_opt v_typeidx v_fieldidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1051⟩ => (((interp_wf_uN_ii (32) (v_fieldidx)).flatMap fun ⟨_, h_1052⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_60 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_60]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_61 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.STRUCT_SET v_typeidx v_fieldidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1053⟩ => (((interp_wf_uN_ii (32) (v_fieldidx)).flatMap fun ⟨_, h_1054⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_61 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_61]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_62 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_NEW v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1055⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_62 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_62]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_63 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_NEW_DEFAULT v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1056⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_63 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_63]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_64 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_NEW_FIXED v_typeidx v_u32) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1057⟩ => (((interp_wf_uN_ii (32) (v_u32)).flatMap fun ⟨_, h_1058⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_64 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_64]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_65 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_NEW_DATA v_typeidx v_dataidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1059⟩ => (((interp_wf_uN_ii (32) (v_dataidx)).flatMap fun ⟨_, h_1060⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_65 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_65]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_66 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_NEW_ELEM v_typeidx v_elemidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1061⟩ => (((interp_wf_uN_ii (32) (v_elemidx)).flatMap fun ⟨_, h_1062⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_66 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_66]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_67 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_GET sx_opt v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1063⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_67 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_67]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_68 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_SET v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1064⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_68 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_68]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_69 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .ARRAY_LEN => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_69 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_69]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_70 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_FILL v_typeidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1065⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_70 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_70]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_71 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_COPY v_typeidx typeidx_0) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1066⟩ => (((interp_wf_uN_ii (32) (typeidx_0)).flatMap fun ⟨_, h_1067⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_71 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_71]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_72 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_INIT_DATA v_typeidx v_dataidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1068⟩ => (((interp_wf_uN_ii (32) (v_dataidx)).flatMap fun ⟨_, h_1069⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_72 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_72]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_73 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.ARRAY_INIT_ELEM v_typeidx v_elemidx) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_1070⟩ => (((interp_wf_uN_ii (32) (v_elemidx)).flatMap fun ⟨_, h_1071⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_73 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_73]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_74 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .EXTERN_CONVERT_ANY => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_74 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_74]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_75 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .ANY_CONVERT_EXTERN => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_75 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_75]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_76 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.CONST v_numtype var_0) => (((interp_wf_num__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1072⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_76 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_76]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_77 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.UNOP v_numtype var_0) => (((interp_wf_unop__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1073⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_77 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_77]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_78 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.BINOP v_numtype var_0) => (((interp_wf_binop__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1074⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_78 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_78]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_79 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.TESTOP v_numtype var_0) => (((interp_wf_testop__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1075⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_79 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_79]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_80 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.RELOP v_numtype var_0) => (((interp_wf_relop__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_1076⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_80 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_80]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_81 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.CVTOP numtype_1 numtype_2 var_0) => (((interp_wf_cvtop___iii (numtype_2) (numtype_1) (var_0)).flatMap fun ⟨_, h_1077⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_81 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_81]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_82 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VCONST v_vectype var_0) => (((interp_wf_uN_ii ((vsize v_vectype)) (var_0)).flatMap fun ⟨_, h_1078⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_82 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_82]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_83 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VVUNOP v_vectype v_vvunop) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_83 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_83]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_84 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VVBINOP v_vectype v_vvbinop) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_84 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_84]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_85 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VVTERNOP v_vectype v_vvternop) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_85 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_85]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_86 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VVTESTOP v_vectype v_vvtestop) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_86 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_86]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_87 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VUNOP v_shape var_0) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1079⟩ => (((interp_wf_vunop__ii (v_shape) (var_0)).flatMap fun ⟨_, h_1080⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_87 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_87]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_88 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VBINOP v_shape var_0) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1081⟩ => (((interp_wf_vbinop__ii (v_shape) (var_0)).flatMap fun ⟨_, h_1082⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_88 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_88]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_89 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VTERNOP v_shape var_0) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1083⟩ => (((interp_wf_vternop__ii (v_shape) (var_0)).flatMap fun ⟨_, h_1084⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_89 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_89]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_90 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VTESTOP v_shape var_0) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1085⟩ => (((interp_wf_vtestop__ii (v_shape) (var_0)).flatMap fun ⟨_, h_1086⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_90 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_90]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_91 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VRELOP v_shape var_0) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1087⟩ => (((interp_wf_vrelop__ii (v_shape) (var_0)).flatMap fun ⟨_, h_1088⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_91 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_91]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_92 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSHIFTOP v_ishape var_0) => (((interp_wf_ishape_i (v_ishape)).flatMap fun ⟨_, h_1089⟩ => (((interp_wf_vshiftop__ii (v_ishape) (var_0)).flatMap fun ⟨_, h_1090⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_92 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_92]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_93 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VBITMASK v_ishape) => (((interp_wf_ishape_i (v_ishape)).flatMap fun ⟨_, h_1091⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_93 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_93]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_94 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSWIZZLOP v_bshape var_0) => (((interp_wf_bshape_i (v_bshape)).flatMap fun ⟨_, h_1092⟩ => (((interp_wf_vswizzlop__ii (v_bshape) (var_0)).flatMap fun ⟨_, h_1093⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_94 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_94]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_95 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSHUFFLE v_bshape laneidx_lst) => ((if h_1094 : ((.mk_dim (List.length laneidx_lst)) = (fun_dim (proj_bshape_0 v_bshape))) then
(((interp_wf_bshape_i (v_bshape)).flatMap fun ⟨_, h_1095⟩ => (((interp_allL (fun (v_laneidx : laneidx) => (interp_wf_uN_ii (8) (v_laneidx))) laneidx_lst).flatMap fun ⟨_, h_1096⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_95 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_95]⟩])))))
else []))
 | _ => []

partial def interp_wf_instr_i_instr_case_96 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VEXTUNOP ishape_1 ishape_2 var_0) => (((interp_wf_ishape_i (ishape_1)).flatMap fun ⟨_, h_1097⟩ => (((interp_wf_ishape_i (ishape_2)).flatMap fun ⟨_, h_1098⟩ => (((interp_wf_vextunop___iii (ishape_2) (ishape_1) (var_0)).flatMap fun ⟨_, h_1099⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_96 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_96]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_97 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VEXTBINOP ishape_1 ishape_2 var_0) => (((interp_wf_ishape_i (ishape_1)).flatMap fun ⟨_, h_1100⟩ => (((interp_wf_ishape_i (ishape_2)).flatMap fun ⟨_, h_1101⟩ => (((interp_wf_vextbinop___iii (ishape_2) (ishape_1) (var_0)).flatMap fun ⟨_, h_1102⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_97 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_97]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_98 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VEXTTERNOP ishape_1 ishape_2 var_0) => (((interp_wf_ishape_i (ishape_1)).flatMap fun ⟨_, h_1103⟩ => (((interp_wf_ishape_i (ishape_2)).flatMap fun ⟨_, h_1104⟩ => (((interp_wf_vextternop___iii (ishape_2) (ishape_1) (var_0)).flatMap fun ⟨_, h_1105⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_98 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_98]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_99 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VNARROW ishape_1 ishape_2 v_sx) => ((if h_1106 : ((lsize (fun_lanetype (proj_ishape_0 ishape_2))) = (2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1))))) then
((if h_1107 : ((2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1)))) <= 32) then
(((interp_wf_ishape_i (ishape_1)).flatMap fun ⟨_, h_1108⟩ => (((interp_wf_ishape_i (ishape_2)).flatMap fun ⟨_, h_1109⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_99 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_99]⟩])))))
else []))
else []))
 | _ => []

partial def interp_wf_instr_i_instr_case_100 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VCVTOP shape_1 shape_2 var_0) => (((interp_wf_shape_i (shape_1)).flatMap fun ⟨_, h_1110⟩ => (((interp_wf_shape_i (shape_2)).flatMap fun ⟨_, h_1111⟩ => (((interp_wf_vcvtop___iii (shape_2) (shape_1) (var_0)).flatMap fun ⟨_, h_1112⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_100 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_100]⟩])))))))
 | _ => []

partial def interp_wf_instr_i_instr_case_101 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VSPLAT v_shape) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1113⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_101 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_101]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_102 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VEXTRACT_LANE v_shape sx_opt v_laneidx) => ((if h_1114 : ((List.length ([.I32, .I64, .F32, .F64] : (List lanetype))) > 0) then
((if h_1115 : ((sx_opt = none) ↔ ((fun_lanetype v_shape) ∈ ([.I32, .I64, .F32, .F64] : (List lanetype)))) then
(((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1116⟩ => (((interp_wf_uN_ii (8) (v_laneidx)).flatMap fun ⟨_, h_1117⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_102 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_102]⟩])))))
else []))
else []))
 | _ => []

partial def interp_wf_instr_i_instr_case_103 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.VREPLACE_LANE v_shape v_laneidx) => (((interp_wf_shape_i (v_shape)).flatMap fun ⟨_, h_1118⟩ => (((interp_wf_uN_ii (8) (v_laneidx)).flatMap fun ⟨_, h_1119⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_103 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_103]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_104 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_I31_NUM v_u31) => (((interp_wf_uN_ii (31) (v_u31)).flatMap fun ⟨_, h_1120⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_104 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_104]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_105 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .REF_NULL_ADDR => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_105 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_105]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_106 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_STRUCT_ADDR v_structaddr) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_106 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_106]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_107 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_ARRAY_ADDR v_arrayaddr) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_107 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_107]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_108 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_FUNC_ADDR v_funcaddr) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_108 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_108]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_109 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_EXN_ADDR v_exnaddr) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_109 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_109]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_110 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_HOST_ADDR v_hostaddr) => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_110 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_110]⟩])
 | _ => []

partial def interp_wf_instr_i_instr_case_111 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.REF_EXTERN v_ref) => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_1121⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_111 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_111]⟩])))
 | _ => []

partial def interp_wf_instr_i_instr_case_112 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.LABEL_ v_n instr_lst instr_lst_0_lst) => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_1122⟩ => (((interp_allL (fun (instr_lst_0 : instr) => (interp_wf_instr_i (instr_lst_0))) instr_lst_0_lst).flatMap fun ⟨_, h_1123⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_112 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_112]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_113 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.FRAME_ v_n v_frame instr_lst) => (((interp_wf_frame_i (v_frame)).flatMap fun ⟨_, h_1124⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_1125⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_113 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_113]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_114 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | (.HANDLER_ v_n catch_lst instr_lst) => (((interp_allL (fun (v_catch : «catch») => (interp_wf_catch_i (v_catch))) catch_lst).flatMap fun ⟨_, h_1126⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_1127⟩ => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_114 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_114]⟩])))))
 | _ => []

partial def interp_wf_instr_i_instr_case_115 (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  match a0 with
 | .TRAP => ([⟨(), by subst_vars; first | (apply wf_instr.instr_case_115 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instr.instr_case_115]⟩])
 | _ => []

partial def interp_wf_instr_i (a0 : instr) : List {o : Unit // (wf_instr a0)} :=
  interp_wf_instr_i_instr_case_0 a0 ++
  interp_wf_instr_i_instr_case_1 a0 ++
  interp_wf_instr_i_instr_case_2 a0 ++
  interp_wf_instr_i_instr_case_3 a0 ++
  interp_wf_instr_i_instr_case_4 a0 ++
  interp_wf_instr_i_instr_case_5 a0 ++
  interp_wf_instr_i_instr_case_6 a0 ++
  interp_wf_instr_i_instr_case_7 a0 ++
  interp_wf_instr_i_instr_case_8 a0 ++
  interp_wf_instr_i_instr_case_9 a0 ++
  interp_wf_instr_i_instr_case_10 a0 ++
  interp_wf_instr_i_instr_case_11 a0 ++
  interp_wf_instr_i_instr_case_12 a0 ++
  interp_wf_instr_i_instr_case_13 a0 ++
  interp_wf_instr_i_instr_case_14 a0 ++
  interp_wf_instr_i_instr_case_15 a0 ++
  interp_wf_instr_i_instr_case_16 a0 ++
  interp_wf_instr_i_instr_case_17 a0 ++
  interp_wf_instr_i_instr_case_18 a0 ++
  interp_wf_instr_i_instr_case_19 a0 ++
  interp_wf_instr_i_instr_case_20 a0 ++
  interp_wf_instr_i_instr_case_21 a0 ++
  interp_wf_instr_i_instr_case_22 a0 ++
  interp_wf_instr_i_instr_case_23 a0 ++
  interp_wf_instr_i_instr_case_24 a0 ++
  interp_wf_instr_i_instr_case_25 a0 ++
  interp_wf_instr_i_instr_case_26 a0 ++
  interp_wf_instr_i_instr_case_27 a0 ++
  interp_wf_instr_i_instr_case_28 a0 ++
  interp_wf_instr_i_instr_case_29 a0 ++
  interp_wf_instr_i_instr_case_30 a0 ++
  interp_wf_instr_i_instr_case_31 a0 ++
  interp_wf_instr_i_instr_case_32 a0 ++
  interp_wf_instr_i_instr_case_33 a0 ++
  interp_wf_instr_i_instr_case_34 a0 ++
  interp_wf_instr_i_instr_case_35 a0 ++
  interp_wf_instr_i_instr_case_36 a0 ++
  interp_wf_instr_i_instr_case_37 a0 ++
  interp_wf_instr_i_instr_case_38 a0 ++
  interp_wf_instr_i_instr_case_39 a0 ++
  interp_wf_instr_i_instr_case_40 a0 ++
  interp_wf_instr_i_instr_case_41 a0 ++
  interp_wf_instr_i_instr_case_42 a0 ++
  interp_wf_instr_i_instr_case_43 a0 ++
  interp_wf_instr_i_instr_case_44 a0 ++
  interp_wf_instr_i_instr_case_45 a0 ++
  interp_wf_instr_i_instr_case_46 a0 ++
  interp_wf_instr_i_instr_case_47 a0 ++
  interp_wf_instr_i_instr_case_48 a0 ++
  interp_wf_instr_i_instr_case_49 a0 ++
  interp_wf_instr_i_instr_case_50 a0 ++
  interp_wf_instr_i_instr_case_51 a0 ++
  interp_wf_instr_i_instr_case_52 a0 ++
  interp_wf_instr_i_instr_case_53 a0 ++
  interp_wf_instr_i_instr_case_54 a0 ++
  interp_wf_instr_i_instr_case_55 a0 ++
  interp_wf_instr_i_instr_case_56 a0 ++
  interp_wf_instr_i_instr_case_57 a0 ++
  interp_wf_instr_i_instr_case_58 a0 ++
  interp_wf_instr_i_instr_case_59 a0 ++
  interp_wf_instr_i_instr_case_60 a0 ++
  interp_wf_instr_i_instr_case_61 a0 ++
  interp_wf_instr_i_instr_case_62 a0 ++
  interp_wf_instr_i_instr_case_63 a0 ++
  interp_wf_instr_i_instr_case_64 a0 ++
  interp_wf_instr_i_instr_case_65 a0 ++
  interp_wf_instr_i_instr_case_66 a0 ++
  interp_wf_instr_i_instr_case_67 a0 ++
  interp_wf_instr_i_instr_case_68 a0 ++
  interp_wf_instr_i_instr_case_69 a0 ++
  interp_wf_instr_i_instr_case_70 a0 ++
  interp_wf_instr_i_instr_case_71 a0 ++
  interp_wf_instr_i_instr_case_72 a0 ++
  interp_wf_instr_i_instr_case_73 a0 ++
  interp_wf_instr_i_instr_case_74 a0 ++
  interp_wf_instr_i_instr_case_75 a0 ++
  interp_wf_instr_i_instr_case_76 a0 ++
  interp_wf_instr_i_instr_case_77 a0 ++
  interp_wf_instr_i_instr_case_78 a0 ++
  interp_wf_instr_i_instr_case_79 a0 ++
  interp_wf_instr_i_instr_case_80 a0 ++
  interp_wf_instr_i_instr_case_81 a0 ++
  interp_wf_instr_i_instr_case_82 a0 ++
  interp_wf_instr_i_instr_case_83 a0 ++
  interp_wf_instr_i_instr_case_84 a0 ++
  interp_wf_instr_i_instr_case_85 a0 ++
  interp_wf_instr_i_instr_case_86 a0 ++
  interp_wf_instr_i_instr_case_87 a0 ++
  interp_wf_instr_i_instr_case_88 a0 ++
  interp_wf_instr_i_instr_case_89 a0 ++
  interp_wf_instr_i_instr_case_90 a0 ++
  interp_wf_instr_i_instr_case_91 a0 ++
  interp_wf_instr_i_instr_case_92 a0 ++
  interp_wf_instr_i_instr_case_93 a0 ++
  interp_wf_instr_i_instr_case_94 a0 ++
  interp_wf_instr_i_instr_case_95 a0 ++
  interp_wf_instr_i_instr_case_96 a0 ++
  interp_wf_instr_i_instr_case_97 a0 ++
  interp_wf_instr_i_instr_case_98 a0 ++
  interp_wf_instr_i_instr_case_99 a0 ++
  interp_wf_instr_i_instr_case_100 a0 ++
  interp_wf_instr_i_instr_case_101 a0 ++
  interp_wf_instr_i_instr_case_102 a0 ++
  interp_wf_instr_i_instr_case_103 a0 ++
  interp_wf_instr_i_instr_case_104 a0 ++
  interp_wf_instr_i_instr_case_105 a0 ++
  interp_wf_instr_i_instr_case_106 a0 ++
  interp_wf_instr_i_instr_case_107 a0 ++
  interp_wf_instr_i_instr_case_108 a0 ++
  interp_wf_instr_i_instr_case_109 a0 ++
  interp_wf_instr_i_instr_case_110 a0 ++
  interp_wf_instr_i_instr_case_111 a0 ++
  interp_wf_instr_i_instr_case_112 a0 ++
  interp_wf_instr_i_instr_case_113 a0 ++
  interp_wf_instr_i_instr_case_114 a0 ++
  interp_wf_instr_i_instr_case_115 a0

end

def interp_Step_pure_io_unreachable (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [.UNREACHABLE] => (((interp_wf_instr_i (.UNREACHABLE)).flatMap fun ⟨_, h_1⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.unreachable <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.unreachable]⟩])))))
 | _ => []

def interp_Step_pure_io_nop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [.NOP] => (((interp_wf_instr_i (.NOP)).flatMap fun ⟨_, h_3⟩ => ([⟨[], by subst_vars; first | (apply Step_pure.nop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.nop]⟩])))
 | _ => []

def interp_Step_pure_io_drop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_1, .DROP] => ((match interp_inv_instr_val y_1 with
 | some ⟨v_val, h_4⟩ => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_5⟩ => (((interp_wf_instr_i (.DROP)).flatMap fun ⟨_, h_6⟩ => ([⟨[], by subst_vars; first | (apply Step_pure.drop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.drop]⟩])))))
 | none => []))
 | _ => []

def interp_Step_pure_io_select_true (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_2, y_3, (.CONST .I32 c), (.SELECT t_lst_opt)] => ((if h_7 : ((proj_num__0 c) ≠ none) then
((if h_8 : ((proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0) then
((match interp_inv_instr_val y_2 with
 | some ⟨val_1, h_9⟩ => ((match interp_inv_instr_val y_3 with
 | some ⟨val_2, h_10⟩ => (((interp_wf_val_i (val_1)).flatMap fun ⟨_, h_11⟩ => (((interp_wf_val_i (val_2)).flatMap fun ⟨_, h_12⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_13⟩ => (((interp_wf_instr_i ((.SELECT t_lst_opt))).flatMap fun ⟨_, h_14⟩ => ([⟨([(instr_val val_1)] : (List instr)), by subst_vars; first | (apply Step_pure.select_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.select_true]⟩])))))))))
 | none => []))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_pure_io_select_false (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_4, y_5, (.CONST .I32 c), (.SELECT t_lst_opt)] => ((if h_15 : ((proj_num__0 c) ≠ none) then
((if h_16 : ((proj_uN_0 (Option.get! (proj_num__0 c))) = 0) then
((match interp_inv_instr_val y_4 with
 | some ⟨val_1, h_17⟩ => ((match interp_inv_instr_val y_5 with
 | some ⟨val_2, h_18⟩ => (((interp_wf_val_i (val_1)).flatMap fun ⟨_, h_19⟩ => (((interp_wf_val_i (val_2)).flatMap fun ⟨_, h_20⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_21⟩ => (((interp_wf_instr_i ((.SELECT t_lst_opt))).flatMap fun ⟨_, h_22⟩ => ([⟨([(instr_val val_2)] : (List instr)), by subst_vars; first | (apply Step_pure.select_false <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.select_false]⟩])))))))))
 | none => []))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_pure_io_if_true (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 c), (.IFELSE bt instr_1_lst instr_2_lst)] => ((if h_23 : ((proj_num__0 c) ≠ none) then
((if h_24 : ((proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0) then
(((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_25⟩ => (((interp_wf_instr_i ((.IFELSE bt instr_1_lst instr_2_lst))).flatMap fun ⟨_, h_26⟩ => (((interp_wf_instr_i ((.BLOCK bt instr_1_lst))).flatMap fun ⟨_, h_27⟩ => ([⟨([(.BLOCK bt instr_1_lst)] : (List instr)), by subst_vars; first | (apply Step_pure.if_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.if_true]⟩])))))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_if_false (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 c), (.IFELSE bt instr_1_lst instr_2_lst)] => ((if h_28 : ((proj_num__0 c) ≠ none) then
((if h_29 : ((proj_uN_0 (Option.get! (proj_num__0 c))) = 0) then
(((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_30⟩ => (((interp_wf_instr_i ((.IFELSE bt instr_1_lst instr_2_lst))).flatMap fun ⟨_, h_31⟩ => (((interp_wf_instr_i ((.BLOCK bt instr_2_lst))).flatMap fun ⟨_, h_32⟩ => ([⟨([(.BLOCK bt instr_2_lst)] : (List instr)), by subst_vars; first | (apply Step_pure.if_false <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.if_false]⟩])))))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_label_vals (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.LABEL_ v_n instr_lst y_6)] => ((match interp_invMap interp_inv_instr_val y_6 with
 | some ⟨val_lst, h_33⟩ => (((interp_wf_instr_i ((.LABEL_ v_n instr_lst (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)))).flatMap fun ⟨_, h_34⟩ => ([⟨(List.map (fun (v_val : val) => (instr_val v_val)) val_lst), by subst_vars; first | (apply Step_pure.label_vals <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.label_vals]⟩])))
 | none => []))
 | _ => []

def interp_Step_pure_io_br_label_zero (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.LABEL_ v_n instr'_lst y_7)] => (((interp_splits y_7).flatMap fun ⟨(a_8, b_9), h_35⟩ => (((interp_splits a_8).flatMap fun ⟨(a_10, b_11), h_36⟩ => (((interp_splits a_10).flatMap fun ⟨(a_12, b_13), h_37⟩ => ((match interp_invMap interp_inv_instr_val a_12 with
 | some ⟨val'_lst, h_38⟩ => ((match interp_invMap interp_inv_instr_val b_13 with
 | some ⟨val_lst, h_39⟩ => ((if h_40 : (v_n = (List.length val_lst)) then
((match b_11 with
 | [(.BR l)] => ((if h_42 : ((proj_uN_0 l) = 0) then
((match b_9 with
 | instr_lst => (((interp_wf_instr_i ((.LABEL_ v_n instr'_lst ((((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)) ++ ([(.BR l)] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_44⟩ => ((if h_45 : ((List.length val_lst) = v_n) then
([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr'_lst), by subst_vars; first | (apply Step_pure.br_label_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_label_zero]⟩])
else []))))))
else []))
 | _ => []))
else []))
 | none => []))
 | none => []))))))))
 | _ => []

def interp_Step_pure_io_br_label_succ (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.LABEL_ v_n instr'_lst y_14)] => (((interp_splits y_14).flatMap fun ⟨(a_15, b_16), h_46⟩ => (((interp_splits a_15).flatMap fun ⟨(a_17, b_18), h_47⟩ => ((match interp_invMap interp_inv_instr_val a_17 with
 | some ⟨val_lst, h_48⟩ => ((match b_18 with
 | [(.BR l)] => ((if h_50 : ((proj_uN_0 l) > 0) then
((match b_16 with
 | instr_lst => (((interp_wf_instr_i ((.LABEL_ v_n instr'_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_52⟩ => (((interp_wf_instr_i ((.BR (.mk_uN (Int.toNat ((Int.ofNat (proj_uN_0 l)) - (Int.ofNat 1))))))).flatMap fun ⟨_, h_53⟩ => ((if h_54 : (0 ≤ ((Int.ofNat (proj_uN_0 l)) - (Int.ofNat 1))) then
([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR (.mk_uN (Int.toNat ((Int.ofNat (proj_uN_0 l)) - (Int.ofNat 1)))))] : (List instr))), by subst_vars; first | (apply Step_pure.br_label_succ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_label_succ]⟩])
else []))))))))
else []))
 | _ => []))
 | none => []))))))
 | _ => []

def interp_Step_pure_io_br_handler (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.HANDLER_ v_n catch_lst y_19)] => (((interp_splits y_19).flatMap fun ⟨(a_20, b_21), h_55⟩ => (((interp_splits a_20).flatMap fun ⟨(a_22, b_23), h_56⟩ => ((match interp_invMap interp_inv_instr_val a_22 with
 | some ⟨val_lst, h_57⟩ => ((match b_23 with
 | [(.BR l)] => ((match b_21 with
 | instr_lst => (((interp_wf_instr_i ((.HANDLER_ v_n catch_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_60⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_61⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] : (List instr))), by subst_vars; first | (apply Step_pure.br_handler <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_handler]⟩])))))))
 | _ => []))
 | none => []))))))
 | _ => []

def interp_Step_pure_io_br_if_true (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 c), (.BR_IF l)] => ((if h_62 : ((proj_num__0 c) ≠ none) then
((if h_63 : ((proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0) then
(((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_64⟩ => (((interp_wf_instr_i ((.BR_IF l))).flatMap fun ⟨_, h_65⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_66⟩ => ([⟨([(.BR l)] : (List instr)), by subst_vars; first | (apply Step_pure.br_if_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_if_true]⟩])))))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_br_if_false (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 c), (.BR_IF l)] => ((if h_67 : ((proj_num__0 c) ≠ none) then
((if h_68 : ((proj_uN_0 (Option.get! (proj_num__0 c))) = 0) then
(((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_69⟩ => (((interp_wf_instr_i ((.BR_IF l))).flatMap fun ⟨_, h_70⟩ => ([⟨[], by subst_vars; first | (apply Step_pure.br_if_false <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_if_false]⟩])))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_br_table_lt (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 i), (.BR_TABLE l_lst l')] => ((if h_71 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length l_lst)) then
((if h_72 : ((proj_num__0 i) ≠ none) then
(((interp_wf_instr_i ((.CONST .I32 i))).flatMap fun ⟨_, h_73⟩ => (((interp_wf_instr_i ((.BR_TABLE l_lst l'))).flatMap fun ⟨_, h_74⟩ => (((interp_wf_instr_i ((.BR (l_lst[(proj_uN_0 (Option.get! (proj_num__0 i)))]!)))).flatMap fun ⟨_, h_75⟩ => ([⟨([(.BR (l_lst[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))] : (List instr)), by subst_vars; first | (apply Step_pure.br_table_lt <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_table_lt]⟩])))))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_br_table_ge (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 i), (.BR_TABLE l_lst l')] => ((if h_76 : ((proj_num__0 i) ≠ none) then
((if h_77 : ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length l_lst)) then
(((interp_wf_instr_i ((.CONST .I32 i))).flatMap fun ⟨_, h_78⟩ => (((interp_wf_instr_i ((.BR_TABLE l_lst l'))).flatMap fun ⟨_, h_79⟩ => (((interp_wf_instr_i ((.BR l'))).flatMap fun ⟨_, h_80⟩ => ([⟨([(.BR l')] : (List instr)), by subst_vars; first | (apply Step_pure.br_table_ge <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_table_ge]⟩])))))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_br_on_null_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_24, (.BR_ON_NULL l)] => ((match interp_inv_instr_val y_24 with
 | some ⟨v_val, h_81⟩ => ((if h_82 : (v_val = .REF_NULL_ADDR) then
(((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_83⟩ => (((interp_wf_instr_i ((.BR_ON_NULL l))).flatMap fun ⟨_, h_84⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_85⟩ => (((interp_wf_val_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_86⟩ => ([⟨([(.BR l)] : (List instr)), by subst_vars; first | (apply Step_pure.br_on_null_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_on_null_null]⟩])))))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_br_on_null_addr (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_25, (.BR_ON_NULL l)] => ((match interp_inv_instr_val y_25 with
 | some ⟨v_val, h_87⟩ => ((if h_88 : (v_val ≠ .REF_NULL_ADDR) then
(((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_89⟩ => (((interp_wf_instr_i ((.BR_ON_NULL l))).flatMap fun ⟨_, h_90⟩ => ([⟨([(instr_val v_val)] : (List instr)), by subst_vars; first | (apply Step_pure.br_on_null_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_on_null_addr]⟩])))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_br_on_non_null_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_26, (.BR_ON_NON_NULL l)] => ((match interp_inv_instr_val y_26 with
 | some ⟨v_val, h_91⟩ => ((if h_92 : (v_val = .REF_NULL_ADDR) then
(((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_93⟩ => (((interp_wf_instr_i ((.BR_ON_NON_NULL l))).flatMap fun ⟨_, h_94⟩ => (((interp_wf_val_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_95⟩ => ([⟨[], by subst_vars; first | (apply Step_pure.br_on_non_null_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_on_non_null_null]⟩])))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_br_on_non_null_addr (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_27, (.BR_ON_NON_NULL l)] => ((match interp_inv_instr_val y_27 with
 | some ⟨v_val, h_96⟩ => ((if h_97 : (v_val ≠ .REF_NULL_ADDR) then
(((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_98⟩ => (((interp_wf_instr_i ((.BR_ON_NON_NULL l))).flatMap fun ⟨_, h_99⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_100⟩ => ([⟨([(instr_val v_val), (.BR l)] : (List instr)), by subst_vars; first | (apply Step_pure.br_on_non_null_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.br_on_non_null_addr]⟩])))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_call_indirect (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CALL_INDIRECT x yy)] => (((interp_wf_instr_i ((.CALL_INDIRECT x yy))).flatMap fun ⟨_, h_101⟩ => (((interp_wf_instr_i ((.TABLE_GET x))).flatMap fun ⟨_, h_102⟩ => (((interp_wf_instr_i ((.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))))).flatMap fun ⟨_, h_103⟩ => (((interp_wf_instr_i ((.CALL_REF yy))).flatMap fun ⟨_, h_104⟩ => ([⟨([(.TABLE_GET x), (.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.CALL_REF yy)] : (List instr)), by subst_vars; first | (apply Step_pure.call_indirect <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.call_indirect]⟩])))))))))
 | _ => []

def interp_Step_pure_io_return_call_indirect (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.RETURN_CALL_INDIRECT x yy)] => (((interp_wf_instr_i ((.RETURN_CALL_INDIRECT x yy))).flatMap fun ⟨_, h_105⟩ => (((interp_wf_instr_i ((.TABLE_GET x))).flatMap fun ⟨_, h_106⟩ => (((interp_wf_instr_i ((.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))))).flatMap fun ⟨_, h_107⟩ => (((interp_wf_instr_i ((.RETURN_CALL_REF yy))).flatMap fun ⟨_, h_108⟩ => ([⟨([(.TABLE_GET x), (.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.RETURN_CALL_REF yy)] : (List instr)), by subst_vars; first | (apply Step_pure.return_call_indirect <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.return_call_indirect]⟩])))))))))
 | _ => []

def interp_Step_pure_io_frame_vals (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.FRAME_ v_n f y_28)] => ((match interp_invMap interp_inv_instr_val y_28 with
 | some ⟨val_lst, h_109⟩ => ((if h_110 : (v_n = (List.length val_lst)) then
(((interp_wf_instr_i ((.FRAME_ v_n f (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)))).flatMap fun ⟨_, h_111⟩ => ((if h_112 : ((List.length val_lst) = v_n) then
([⟨(List.map (fun (v_val : val) => (instr_val v_val)) val_lst), by subst_vars; first | (apply Step_pure.frame_vals <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.frame_vals]⟩])
else []))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_return_frame (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.FRAME_ v_n f y_29)] => (((interp_splits y_29).flatMap fun ⟨(a_30, b_31), h_113⟩ => (((interp_splits a_30).flatMap fun ⟨(a_32, b_33), h_114⟩ => ((if h_115 : (b_33 = ([.RETURN] : (List instr))) then
(((interp_splits a_32).flatMap fun ⟨(a_34, b_35), h_116⟩ => ((match interp_invMap interp_inv_instr_val a_34 with
 | some ⟨val'_lst, h_117⟩ => ((match interp_invMap interp_inv_instr_val b_35 with
 | some ⟨val_lst, h_118⟩ => ((if h_119 : (v_n = (List.length val_lst)) then
((match b_31 with
 | instr_lst => (((interp_wf_instr_i ((.FRAME_ v_n f ((((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)) ++ ([.RETURN] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_121⟩ => ((if h_122 : ((List.length val_lst) = v_n) then
([⟨(List.map (fun (v_val : val) => (instr_val v_val)) val_lst), by subst_vars; first | (apply Step_pure.return_frame <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.return_frame]⟩])
else []))))))
else []))
 | none => []))
 | none => []))))
else []))))))
 | _ => []

def interp_Step_pure_io_return_label (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.LABEL_ v_n instr'_lst y_36)] => (((interp_splits y_36).flatMap fun ⟨(a_37, b_38), h_123⟩ => (((interp_splits a_37).flatMap fun ⟨(a_39, b_40), h_124⟩ => ((if h_125 : (b_40 = ([.RETURN] : (List instr))) then
((match interp_invMap interp_inv_instr_val a_39 with
 | some ⟨val_lst, h_126⟩ => ((match b_38 with
 | instr_lst => (((interp_wf_instr_i ((.LABEL_ v_n instr'_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_128⟩ => (((interp_wf_instr_i (.RETURN)).flatMap fun ⟨_, h_129⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] : (List instr))), by subst_vars; first | (apply Step_pure.return_label <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.return_label]⟩])))))))
 | none => []))
else []))))))
 | _ => []

def interp_Step_pure_io_return_handler (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.HANDLER_ v_n catch_lst y_41)] => (((interp_splits y_41).flatMap fun ⟨(a_42, b_43), h_130⟩ => (((interp_splits a_42).flatMap fun ⟨(a_44, b_45), h_131⟩ => ((if h_132 : (b_45 = ([.RETURN] : (List instr))) then
((match interp_invMap interp_inv_instr_val a_44 with
 | some ⟨val_lst, h_133⟩ => ((match b_43 with
 | instr_lst => (((interp_wf_instr_i ((.HANDLER_ v_n catch_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] : (List instr))) ++ instr_lst)))).flatMap fun ⟨_, h_135⟩ => (((interp_wf_instr_i (.RETURN)).flatMap fun ⟨_, h_136⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] : (List instr))), by subst_vars; first | (apply Step_pure.return_handler <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.return_handler]⟩])))))))
 | none => []))
else []))))))
 | _ => []

def interp_Step_pure_io_handler_vals (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.HANDLER_ v_n catch_lst y_46)] => ((match interp_invMap interp_inv_instr_val y_46 with
 | some ⟨val_lst, h_137⟩ => (((interp_wf_instr_i ((.HANDLER_ v_n catch_lst (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)))).flatMap fun ⟨_, h_138⟩ => ([⟨(List.map (fun (v_val : val) => (instr_val v_val)) val_lst), by subst_vars; first | (apply Step_pure.handler_vals <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.handler_vals]⟩])))
 | none => []))
 | _ => []

def interp_Step_pure_io_trap_instrs (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | y_47 => (((interp_splits y_47).flatMap fun ⟨(a_48, b_49), h_139⟩ => ((match interp_invMap interp_inv_instr_val a_48 with
 | some ⟨val_lst, h_140⟩ => (((interp_splits b_49).flatMap fun ⟨(a_50, b_51), h_141⟩ => ((if h_142 : (a_50 = ([.TRAP] : (List instr))) then
((match b_51 with
 | instr_lst => ((if h_144 : ((val_lst ≠ []) ∨ (instr_lst ≠ [])) then
(((interp_allL (fun (v_val : val) => (interp_wf_val_i (v_val))) val_lst).flatMap fun ⟨_, h_145⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_146⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_147⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.trap_instrs <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.trap_instrs]⟩])))))))
else []))))
else []))))
 | none => []))))

def interp_Step_pure_io_trap_label (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.LABEL_ v_n instr'_lst [.TRAP])] => (((interp_wf_instr_i ((.LABEL_ v_n instr'_lst ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_148⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_149⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.trap_label <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.trap_label]⟩])))))
 | _ => []

def interp_Step_pure_io_trap_handler (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.HANDLER_ v_n catch_lst [.TRAP])] => (((interp_wf_instr_i ((.HANDLER_ v_n catch_lst ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_150⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_151⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.trap_handler <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.trap_handler]⟩])))))
 | _ => []

def interp_Step_pure_io_trap_frame (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.FRAME_ v_n f [.TRAP])] => (((interp_wf_instr_i ((.FRAME_ v_n f ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_152⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_153⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.trap_frame <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.trap_frame]⟩])))))
 | _ => []

def interp_Step_pure_io_local_tee (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_52, (.LOCAL_TEE x)] => ((match interp_inv_instr_val y_52 with
 | some ⟨v_val, h_154⟩ => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_155⟩ => (((interp_wf_instr_i ((.LOCAL_TEE x))).flatMap fun ⟨_, h_156⟩ => (((interp_wf_instr_i ((.LOCAL_SET x))).flatMap fun ⟨_, h_157⟩ => ([⟨([(instr_val v_val), (instr_val v_val), (.LOCAL_SET x)] : (List instr)), by subst_vars; first | (apply Step_pure.local_tee <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.local_tee]⟩])))))))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_i31 (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST .I32 i), .REF_I31] => ((if h_158 : ((proj_num__0 i) ≠ none) then
(((interp_wf_instr_i ((.CONST .I32 i))).flatMap fun ⟨_, h_159⟩ => (((interp_wf_instr_i (.REF_I31)).flatMap fun ⟨_, h_160⟩ => (((interp_wf_instr_i ((.REF_I31_NUM (wrap__ 32 31 (Option.get! (proj_num__0 i)))))).flatMap fun ⟨_, h_161⟩ => ([⟨([(.REF_I31_NUM (wrap__ 32 31 (Option.get! (proj_num__0 i))))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_i31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_i31]⟩])))))))
else []))
 | _ => []

def interp_Step_pure_io_ref_is_null_true (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_53, .REF_IS_NULL] => ((match interp_inv_instr_ref y_53 with
 | some ⟨v_ref, h_162⟩ => ((if h_163 : (v_ref = .REF_NULL_ADDR) then
(((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_164⟩ => (((interp_wf_instr_i (.REF_IS_NULL)).flatMap fun ⟨_, h_165⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1))))).flatMap fun ⟨_, h_166⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_167⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_is_null_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_is_null_true]⟩])))))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_is_null_false (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_54, .REF_IS_NULL] => ((match interp_inv_instr_ref y_54 with
 | some ⟨v_ref, h_168⟩ => ((if h_169 : (v_ref ≠ .REF_NULL_ADDR) then
(((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_170⟩ => (((interp_wf_instr_i (.REF_IS_NULL)).flatMap fun ⟨_, h_171⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))))).flatMap fun ⟨_, h_172⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_is_null_false <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_is_null_false]⟩])))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_as_non_null_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_55, .REF_AS_NON_NULL] => ((match interp_inv_instr_ref y_55 with
 | some ⟨v_ref, h_173⟩ => ((if h_174 : (v_ref = .REF_NULL_ADDR) then
(((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_175⟩ => (((interp_wf_instr_i (.REF_AS_NON_NULL)).flatMap fun ⟨_, h_176⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_177⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_178⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.ref_as_non_null_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_as_non_null_null]⟩])))))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_as_non_null_addr (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_56, .REF_AS_NON_NULL] => ((match interp_inv_instr_ref y_56 with
 | some ⟨v_ref, h_179⟩ => ((if h_180 : (v_ref ≠ .REF_NULL_ADDR) then
(((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_181⟩ => (((interp_wf_instr_i (.REF_AS_NON_NULL)).flatMap fun ⟨_, h_182⟩ => ([⟨([(instr_ref v_ref)] : (List instr)), by subst_vars; first | (apply Step_pure.ref_as_non_null_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_as_non_null_addr]⟩])))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_eq_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_57, y_58, .REF_EQ] => ((match interp_inv_instr_ref y_57 with
 | some ⟨ref_1, h_183⟩ => ((if h_184 : (ref_1 = .REF_NULL_ADDR) then
((match interp_inv_instr_ref y_58 with
 | some ⟨ref_2, h_185⟩ => ((if h_186 : (ref_2 = .REF_NULL_ADDR) then
(((interp_wf_ref_i (ref_1)).flatMap fun ⟨_, h_187⟩ => (((interp_wf_ref_i (ref_2)).flatMap fun ⟨_, h_188⟩ => (((interp_wf_instr_i (.REF_EQ)).flatMap fun ⟨_, h_189⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1))))).flatMap fun ⟨_, h_190⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_191⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_eq_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_eq_null]⟩])))))))))))
else []))
 | none => []))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_eq_true (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_59, y_60, .REF_EQ] => ((match interp_inv_instr_ref y_59 with
 | some ⟨ref_1, h_192⟩ => ((match interp_inv_instr_ref y_60 with
 | some ⟨ref_2, h_193⟩ => ((if h_194 : ((ref_1 ≠ .REF_NULL_ADDR) ∨ (ref_2 ≠ .REF_NULL_ADDR)) then
((if h_195 : (ref_1 = ref_2) then
(((interp_wf_ref_i (ref_1)).flatMap fun ⟨_, h_196⟩ => (((interp_wf_ref_i (ref_2)).flatMap fun ⟨_, h_197⟩ => (((interp_wf_instr_i (.REF_EQ)).flatMap fun ⟨_, h_198⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1))))).flatMap fun ⟨_, h_199⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_eq_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_eq_true]⟩])))))))))
else []))
else []))
 | none => []))
 | none => []))
 | _ => []

def interp_Step_pure_io_ref_eq_false (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_61, y_62, .REF_EQ] => ((match interp_inv_instr_ref y_61 with
 | some ⟨ref_1, h_200⟩ => ((match interp_inv_instr_ref y_62 with
 | some ⟨ref_2, h_201⟩ => ((if h_202 : (ref_1 ≠ ref_2) then
((if h_203 : ((ref_1 ≠ .REF_NULL_ADDR) ∨ (ref_2 ≠ .REF_NULL_ADDR)) then
(((interp_wf_ref_i (ref_1)).flatMap fun ⟨_, h_204⟩ => (((interp_wf_ref_i (ref_2)).flatMap fun ⟨_, h_205⟩ => (((interp_wf_instr_i (.REF_EQ)).flatMap fun ⟨_, h_206⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))))).flatMap fun ⟨_, h_207⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))] : (List instr)), by subst_vars; first | (apply Step_pure.ref_eq_false <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.ref_eq_false]⟩])))))))))
else []))
else []))
 | none => []))
 | none => []))
 | _ => []

def interp_Step_pure_io_i31_get_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [.REF_NULL_ADDR, (.I31_GET v_sx)] => (((interp_wf_instr_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_208⟩ => (((interp_wf_instr_i ((.I31_GET v_sx))).flatMap fun ⟨_, h_209⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_210⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.i31_get_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.i31_get_null]⟩])))))))
 | _ => []

def interp_Step_pure_io_i31_get_num (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.REF_I31_NUM i), (.I31_GET v_sx)] => (((interp_wf_instr_i ((.REF_I31_NUM i))).flatMap fun ⟨_, h_211⟩ => (((interp_wf_instr_i ((.I31_GET v_sx))).flatMap fun ⟨_, h_212⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (extend__ 31 32 v_sx i))))).flatMap fun ⟨_, h_213⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (extend__ 31 32 v_sx i)))] : (List instr)), by subst_vars; first | (apply Step_pure.i31_get_num <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.i31_get_num]⟩])))))))
 | _ => []

def interp_Step_pure_io_array_new (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_63, (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW x)] => ((match interp_inv_instr_val y_63 with
 | some ⟨v_val, h_214⟩ => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_215⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))))).flatMap fun ⟨_, h_216⟩ => (((interp_wf_instr_i ((.ARRAY_NEW x))).flatMap fun ⟨_, h_217⟩ => (((interp_wf_instr_i ((.ARRAY_NEW_FIXED x (.mk_uN v_n)))).flatMap fun ⟨_, h_218⟩ => ([⟨((List.replicate v_n (instr_val v_val)) ++ ([(.ARRAY_NEW_FIXED x (.mk_uN v_n))] : (List instr))), by subst_vars; first | (apply Step_pure.array_new <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.array_new]⟩])))))))))
 | none => []))
 | _ => []

def interp_Step_pure_io_extern_convert_any_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_64, .EXTERN_CONVERT_ANY] => ((match interp_inv_instr_ref y_64 with
 | some ⟨v_ref, h_219⟩ => ((if h_220 : (v_ref = .REF_NULL_ADDR) then
(((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_221⟩ => (((interp_wf_instr_i (.EXTERN_CONVERT_ANY)).flatMap fun ⟨_, h_222⟩ => (((interp_wf_instr_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_223⟩ => ([⟨([.REF_NULL_ADDR] : (List instr)), by subst_vars; first | (apply Step_pure.extern_convert_any_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.extern_convert_any_null]⟩])))))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_extern_convert_any_addr (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [y_65, .EXTERN_CONVERT_ANY] => ((match interp_inv_instr_ref y_65 with
 | some ⟨v_ref, h_224⟩ => ((if h_225 : (v_ref ≠ .REF_NULL_ADDR) then
(((interp_wf_instr_i (.EXTERN_CONVERT_ANY)).flatMap fun ⟨_, h_226⟩ => (((interp_wf_instr_i ((.REF_EXTERN v_ref))).flatMap fun ⟨_, h_227⟩ => ([⟨([(.REF_EXTERN v_ref)] : (List instr)), by subst_vars; first | (apply Step_pure.extern_convert_any_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.extern_convert_any_addr]⟩])))))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_any_convert_extern_null (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [.REF_NULL_ADDR, .ANY_CONVERT_EXTERN] => (((interp_wf_instr_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_228⟩ => (((interp_wf_instr_i (.ANY_CONVERT_EXTERN)).flatMap fun ⟨_, h_229⟩ => ([⟨([.REF_NULL_ADDR] : (List instr)), by subst_vars; first | (apply Step_pure.any_convert_extern_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.any_convert_extern_null]⟩])))))
 | _ => []

def interp_Step_pure_io_any_convert_extern_addr (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.REF_EXTERN v_ref), .ANY_CONVERT_EXTERN] => (((interp_wf_instr_i ((.REF_EXTERN v_ref))).flatMap fun ⟨_, h_230⟩ => (((interp_wf_instr_i (.ANY_CONVERT_EXTERN)).flatMap fun ⟨_, h_231⟩ => ([⟨([(instr_ref v_ref)] : (List instr)), by subst_vars; first | (apply Step_pure.any_convert_extern_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.any_convert_extern_addr]⟩])))))
 | _ => []

def interp_Step_pure_io_unop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.UNOP y_66 unop)] => ((if h_232 : (y_66 = nt) then
(((interp_fun_unop__iiio (nt) (unop) (c_1)).flatMap fun ⟨o_67, h_233⟩ => (match o_67 with
 | var_0 => ((if h_234 : ((List.length (Option.get! var_0)) > 0) then
((if h_235 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_236⟩ => (((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_237⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_238⟩ => (((interp_wf_instr_i ((.UNOP nt unop))).flatMap fun ⟨_, h_239⟩ => (((interp_wf_instr_i ((.CONST nt c))).flatMap fun ⟨_, h_240⟩ => ([⟨([(.CONST nt c)] : (List instr)), by subst_vars; first | (apply Step_pure.unop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.unop_val]⟩])))))))))))
else []))
else [])))))
else []))
 | _ => []

def interp_Step_pure_io_unop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.UNOP y_68 unop)] => ((if h_241 : (y_68 = nt) then
(((interp_fun_unop__iiio (nt) (unop) (c_1)).flatMap fun ⟨o_69, h_242⟩ => (match o_69 with
 | var_0 => ((if h_243 : (var_0 ≠ none) then
((if h_244 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_245⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_246⟩ => (((interp_wf_instr_i ((.UNOP nt unop))).flatMap fun ⟨_, h_247⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_248⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.unop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.unop_trap]⟩])))))))))
else []))
else [])))))
else []))
 | _ => []

def interp_Step_pure_io_binop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.CONST y_70 c_2), (.BINOP y_71 binop)] => ((if h_249 : (y_70 = nt) then
((if h_250 : (y_71 = nt) then
(((interp_fun_binop__iiiio (nt) (binop) (c_1) (c_2)).flatMap fun ⟨o_72, h_251⟩ => (match o_72 with
 | var_0 => ((if h_252 : ((List.length (Option.get! var_0)) > 0) then
((if h_253 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_254⟩ => (((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_255⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_256⟩ => (((interp_wf_instr_i ((.CONST nt c_2))).flatMap fun ⟨_, h_257⟩ => (((interp_wf_instr_i ((.BINOP nt binop))).flatMap fun ⟨_, h_258⟩ => (((interp_wf_instr_i ((.CONST nt c))).flatMap fun ⟨_, h_259⟩ => ([⟨([(.CONST nt c)] : (List instr)), by subst_vars; first | (apply Step_pure.binop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.binop_val]⟩])))))))))))))
else []))
else [])))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_binop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.CONST y_73 c_2), (.BINOP y_74 binop)] => ((if h_260 : (y_73 = nt) then
((if h_261 : (y_74 = nt) then
(((interp_fun_binop__iiiio (nt) (binop) (c_1) (c_2)).flatMap fun ⟨o_75, h_262⟩ => (match o_75 with
 | var_0 => ((if h_263 : (var_0 ≠ none) then
((if h_264 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_265⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_266⟩ => (((interp_wf_instr_i ((.CONST nt c_2))).flatMap fun ⟨_, h_267⟩ => (((interp_wf_instr_i ((.BINOP nt binop))).flatMap fun ⟨_, h_268⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_269⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.binop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.binop_trap]⟩])))))))))))
else []))
else [])))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_testop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.TESTOP y_76 testop)] => ((if h_270 : (y_76 = nt) then
((if h_271 : ((fun_testop_ nt testop c_1) ≠ none) then
(((interp_cand_proj_num__0 ((Option.get! (fun_testop_ nt testop c_1)))).flatMap fun c => ((if h_274 : ((Option.get! (proj_num__0 c)) = (Option.get! (fun_testop_ nt testop c_1))) then
((if h_275 : ((proj_num__0 c) ≠ none) then
(((interp_wf_uN_ii (32) ((Option.get! (fun_testop_ nt testop c_1)))).flatMap fun ⟨_, h_276⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_277⟩ => (((interp_wf_instr_i ((.TESTOP nt testop))).flatMap fun ⟨_, h_278⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_279⟩ => ([⟨([(.CONST .I32 c)] : (List instr)), by subst_vars; first | (apply Step_pure.testop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.testop]⟩])))))))))
else []))
else []))))
else []))
else []))
 | _ => []

def interp_Step_pure_io_relop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt c_1), (.CONST y_77 c_2), (.RELOP y_78 relop)] => ((if h_280 : (y_77 = nt) then
((if h_281 : (y_78 = nt) then
((if h_282 : ((fun_relop_ nt relop c_1 c_2) ≠ none) then
(((interp_cand_proj_num__0 ((Option.get! (fun_relop_ nt relop c_1 c_2)))).flatMap fun c => ((if h_285 : ((Option.get! (proj_num__0 c)) = (Option.get! (fun_relop_ nt relop c_1 c_2))) then
((if h_286 : ((proj_num__0 c) ≠ none) then
(((interp_wf_uN_ii (32) ((Option.get! (fun_relop_ nt relop c_1 c_2)))).flatMap fun ⟨_, h_287⟩ => (((interp_wf_instr_i ((.CONST nt c_1))).flatMap fun ⟨_, h_288⟩ => (((interp_wf_instr_i ((.CONST nt c_2))).flatMap fun ⟨_, h_289⟩ => (((interp_wf_instr_i ((.RELOP nt relop))).flatMap fun ⟨_, h_290⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_291⟩ => ([⟨([(.CONST .I32 c)] : (List instr)), by subst_vars; first | (apply Step_pure.relop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.relop]⟩])))))))))))
else []))
else []))))
else []))
else []))
else []))
 | _ => []

def interp_Step_pure_io_cvtop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt_1 c_1), (.CVTOP nt_2 y_79 cvtop)] => ((if h_292 : (y_79 = nt_1) then
(((interp_fun_cvtop___iiiio (nt_1) (nt_2) (cvtop) (c_1)).flatMap fun ⟨o_80, h_293⟩ => (match o_80 with
 | var_0 => ((if h_294 : ((List.length (Option.get! var_0)) > 0) then
((if h_295 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_296⟩ => (((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt_2) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_297⟩ => (((interp_wf_instr_i ((.CONST nt_1 c_1))).flatMap fun ⟨_, h_298⟩ => (((interp_wf_instr_i ((.CVTOP nt_2 nt_1 cvtop))).flatMap fun ⟨_, h_299⟩ => (((interp_wf_instr_i ((.CONST nt_2 c))).flatMap fun ⟨_, h_300⟩ => ([⟨([(.CONST nt_2 c)] : (List instr)), by subst_vars; first | (apply Step_pure.cvtop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.cvtop_val]⟩])))))))))))
else []))
else [])))))
else []))
 | _ => []

def interp_Step_pure_io_cvtop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.CONST nt_1 c_1), (.CVTOP nt_2 y_81 cvtop)] => ((if h_301 : (y_81 = nt_1) then
(((interp_fun_cvtop___iiiio (nt_1) (nt_2) (cvtop) (c_1)).flatMap fun ⟨o_82, h_302⟩ => (match o_82 with
 | var_0 => ((if h_303 : (var_0 ≠ none) then
((if h_304 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : num_) => (interp_wf_num__ii (nt_2) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_305⟩ => (((interp_wf_instr_i ((.CONST nt_1 c_1))).flatMap fun ⟨_, h_306⟩ => (((interp_wf_instr_i ((.CVTOP nt_2 nt_1 cvtop))).flatMap fun ⟨_, h_307⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_308⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.cvtop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.cvtop_trap]⟩])))))))))
else []))
else [])))))
else []))
 | _ => []

def interp_Step_pure_io_vvunop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VVUNOP .V128 v_vvunop)] => ((if h_309 : ((List.length (vvunop_ .V128 v_vvunop c_1)) > 0) then
((((vvunop_ .V128 v_vvunop c_1)).attach.flatMap fun ⟨c, h_310⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (vvunop_ .V128 v_vvunop c_1)).flatMap fun ⟨_, h_311⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_312⟩ => (((interp_wf_instr_i ((.VVUNOP .V128 v_vvunop))).flatMap fun ⟨_, h_313⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_314⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vvunop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vvunop]⟩])))))))))))
else []))
 | _ => []

def interp_Step_pure_io_vvbinop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VVBINOP .V128 v_vvbinop)] => ((if h_315 : ((List.length (vvbinop_ .V128 v_vvbinop c_1 c_2)) > 0) then
((((vvbinop_ .V128 v_vvbinop c_1 c_2)).attach.flatMap fun ⟨c, h_316⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (vvbinop_ .V128 v_vvbinop c_1 c_2)).flatMap fun ⟨_, h_317⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_318⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_319⟩ => (((interp_wf_instr_i ((.VVBINOP .V128 v_vvbinop))).flatMap fun ⟨_, h_320⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_321⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vvbinop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vvbinop]⟩])))))))))))))
else []))
 | _ => []

def interp_Step_pure_io_vvternop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VVTERNOP .V128 v_vvternop)] => ((if h_322 : ((List.length (vvternop_ .V128 v_vvternop c_1 c_2 c_3)) > 0) then
((((vvternop_ .V128 v_vvternop c_1 c_2 c_3)).attach.flatMap fun ⟨c, h_323⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (vvternop_ .V128 v_vvternop c_1 c_2 c_3)).flatMap fun ⟨_, h_324⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_325⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_326⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_3))).flatMap fun ⟨_, h_327⟩ => (((interp_wf_instr_i ((.VVTERNOP .V128 v_vvternop))).flatMap fun ⟨_, h_328⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_329⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vvternop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vvternop]⟩])))))))))))))))
else []))
 | _ => []

def interp_Step_pure_io_vvtestop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VVTESTOP .V128 .ANY_TRUE)] => (((interp_cand_proj_num__0 ((inez_ (vsize .V128) c_1))).flatMap fun c => ((if h_332 : ((Option.get! (proj_num__0 c)) = (inez_ (vsize .V128) c_1)) then
((if h_333 : ((proj_num__0 c) ≠ none) then
(((interp_wf_uN_ii (32) ((inez_ (vsize .V128) c_1))).flatMap fun ⟨_, h_334⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_335⟩ => (((interp_wf_instr_i ((.VVTESTOP .V128 .ANY_TRUE))).flatMap fun ⟨_, h_336⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_337⟩ => ([⟨([(.CONST .I32 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vvtestop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vvtestop]⟩])))))))))
else []))
else []))))
 | _ => []

def interp_Step_pure_io_vunop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VUNOP sh vunop)] => (((interp_fun_vunop__iiio (sh) (vunop) (c_1)).flatMap fun ⟨o_83, h_338⟩ => (match o_83 with
 | var_0 => ((if h_339 : ((List.length (Option.get! var_0)) > 0) then
((if h_340 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_341⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_342⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_343⟩ => (((interp_wf_instr_i ((.VUNOP sh vunop))).flatMap fun ⟨_, h_344⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_345⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vunop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vunop_val]⟩])))))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vunop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VUNOP sh vunop)] => (((interp_fun_vunop__iiio (sh) (vunop) (c_1)).flatMap fun ⟨o_84, h_346⟩ => (match o_84 with
 | var_0 => ((if h_347 : (var_0 ≠ none) then
((if h_348 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_349⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_350⟩ => (((interp_wf_instr_i ((.VUNOP sh vunop))).flatMap fun ⟨_, h_351⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_352⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.vunop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vunop_trap]⟩])))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vbinop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] => (((interp_fun_vbinop__iiiio (sh) (vbinop) (c_1) (c_2)).flatMap fun ⟨o_85, h_353⟩ => (match o_85 with
 | var_0 => ((if h_354 : ((List.length (Option.get! var_0)) > 0) then
((if h_355 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_356⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_357⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_358⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_359⟩ => (((interp_wf_instr_i ((.VBINOP sh vbinop))).flatMap fun ⟨_, h_360⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_361⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vbinop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vbinop_val]⟩])))))))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vbinop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] => (((interp_fun_vbinop__iiiio (sh) (vbinop) (c_1) (c_2)).flatMap fun ⟨o_86, h_362⟩ => (match o_86 with
 | var_0 => ((if h_363 : (var_0 ≠ none) then
((if h_364 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_365⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_366⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_367⟩ => (((interp_wf_instr_i ((.VBINOP sh vbinop))).flatMap fun ⟨_, h_368⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_369⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.vbinop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vbinop_trap]⟩])))))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vternop_val (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] => (((interp_fun_vternop__iiiiio (sh) (vternop) (c_1) (c_2) (c_3)).flatMap fun ⟨o_87, h_370⟩ => (match o_87 with
 | var_0 => ((if h_371 : ((List.length (Option.get! var_0)) > 0) then
((if h_372 : (var_0 ≠ none) then
((((Option.get! var_0)).attach.flatMap fun ⟨c, h_373⟩ => (((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_374⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_375⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_376⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_3))).flatMap fun ⟨_, h_377⟩ => (((interp_wf_instr_i ((.VTERNOP sh vternop))).flatMap fun ⟨_, h_378⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_379⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vternop_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vternop_val]⟩])))))))))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vternop_trap (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] => (((interp_fun_vternop__iiiiio (sh) (vternop) (c_1) (c_2) (c_3)).flatMap fun ⟨o_88, h_380⟩ => (match o_88 with
 | var_0 => ((if h_381 : (var_0 ≠ none) then
((if h_382 : ((Option.get! var_0) = []) then
(((interp_allL (fun (iter : vec_) => (interp_wf_uN_ii (128) (iter))) (Option.get! var_0)).flatMap fun ⟨_, h_383⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_384⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_385⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_3))).flatMap fun ⟨_, h_386⟩ => (((interp_wf_instr_i ((.VTERNOP sh vternop))).flatMap fun ⟨_, h_387⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_388⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_pure.vternop_trap <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vternop_trap]⟩])))))))))))))
else []))
else [])))))
 | _ => []

def interp_Step_pure_io_vrelop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VRELOP sh vrelop)] => (((interp_fun_vrelop__iiiio (sh) (vrelop) (c_1) (c_2)).flatMap fun ⟨o_92, h_418⟩ => (match o_92 with
 | var_0 => ((if h_419 : (var_0 ≠ none) then
(((fun (c : vec_) (h_420 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_421⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_422⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_423⟩ => (((interp_wf_instr_i ((.VRELOP sh vrelop))).flatMap fun ⟨_, h_424⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_425⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vrelop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vrelop]⟩])))))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io_vshiftop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.CONST .I32 i), (.VSHIFTOP sh vshiftop)] => ((if h_426 : ((proj_num__0 i) ≠ none) then
(((interp_fun_vshiftop__iiiio (sh) (vshiftop) (c_1) ((Option.get! (proj_num__0 i)))).flatMap fun ⟨o_93, h_427⟩ => (match o_93 with
 | var_0 => ((if h_428 : (var_0 ≠ none) then
(((fun (c : vec_) (h_429 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_430⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_431⟩ => (((interp_wf_instr_i ((.CONST .I32 i))).flatMap fun ⟨_, h_432⟩ => (((interp_wf_instr_i ((.VSHIFTOP sh vshiftop))).flatMap fun ⟨_, h_433⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_434⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vshiftop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vshiftop]⟩])))))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
else []))
 | _ => []

def interp_Step_pure_io_vbitmask (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VBITMASK sh)] => (((interp_fun_vbitmaskop__iio (sh) (c_1)).flatMap fun ⟨o_94, h_435⟩ => (match o_94 with
 | var_0 => (((interp_cand_proj_num__0 (var_0)).flatMap fun c => ((if h_438 : ((Option.get! (proj_num__0 c)) = var_0) then
((if h_439 : ((proj_num__0 c) ≠ none) then
(((interp_wf_uN_ii (32) (var_0)).flatMap fun ⟨_, h_440⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_441⟩ => (((interp_wf_instr_i ((.VBITMASK sh))).flatMap fun ⟨_, h_442⟩ => (((interp_wf_instr_i ((.CONST .I32 c))).flatMap fun ⟨_, h_443⟩ => ([⟨([(.CONST .I32 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vbitmask <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vbitmask]⟩])))))))))
else []))
else [])))))))
 | _ => []

def interp_Step_pure_io_vswizzlop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSWIZZLOP sh swizzlop)] => (((interp_fun_vswizzlop__iiiio (sh) (swizzlop) (c_1) (c_2)).flatMap fun ⟨o_95, h_444⟩ => (match o_95 with
 | var_0 => ((if h_445 : (var_0 ≠ none) then
(((fun (c : vec_) (h_446 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_447⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_448⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_449⟩ => (((interp_wf_instr_i ((.VSWIZZLOP sh swizzlop))).flatMap fun ⟨_, h_450⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_451⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vswizzlop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vswizzlop]⟩])))))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io_vshuffle (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSHUFFLE sh i_lst)] => ((if h_452 : ((vshufflop_ sh i_lst c_1 c_2) ≠ none) then
(((fun (c : vec_) (h_453 : ((Option.get! (vshufflop_ sh i_lst c_1 c_2)) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! (vshufflop_ sh i_lst c_1 c_2)))).flatMap fun ⟨_, h_454⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_455⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_456⟩ => (((interp_wf_instr_i ((.VSHUFFLE sh i_lst))).flatMap fun ⟨_, h_457⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_458⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vshuffle <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vshuffle]⟩])))))))))))) ((Option.get! (vshufflop_ sh i_lst c_1 c_2)) : vec_) rfl))
else []))
 | _ => []

def interp_Step_pure_io_vextract_lane_num (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X y_97 (.mk_dim v_M)) none i)] => ((match interp_inv_lanetype_numtype y_97 with
 | some ⟨nt, h_476⟩ => ((if h_477 : ((lunpacknum_ (lanetype_numtype nt) ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)) ≠ none) then
((if h_478 : ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1))) then
(((fun (c_2 : num_) (h_479 : ((Option.get! (lunpacknum_ (lanetype_numtype nt) ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!))) : num_) = c_2) => (((interp_wf_num__ii ((lunpack (lanetype_numtype nt))) ((Option.get! (lunpacknum_ (lanetype_numtype nt) ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!))))).flatMap fun ⟨_, h_480⟩ => (((interp_allL (fun (iter : lane_) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_numtype nt) (.mk_dim v_M)))) (iter))) (lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)).flatMap fun ⟨_, h_481⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_482⟩ => (((interp_wf_instr_i ((.VEXTRACT_LANE (.X (lanetype_numtype nt) (.mk_dim v_M)) none i))).flatMap fun ⟨_, h_483⟩ => (((interp_wf_instr_i ((.CONST nt c_2))).flatMap fun ⟨_, h_484⟩ => (((interp_wf_shape_i ((.X (lanetype_numtype nt) (.mk_dim v_M)))).flatMap fun ⟨_, h_485⟩ => ([⟨([(.CONST nt c_2)] : (List instr)), by subst_vars; first | (apply Step_pure.vextract_lane_num <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vextract_lane_num]⟩])))))))))))))) ((Option.get! (lunpacknum_ (lanetype_numtype nt) ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!))) : num_) rfl))
else []))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_vextract_lane_pack (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X y_98 (.mk_dim v_M)) (some v_sx) i)] => ((match interp_inv_lanetype_packtype y_98 with
 | some ⟨pt, h_486⟩ => ((if h_487 : ((proj_lane__0 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)) ≠ none) then
((if h_488 : ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1))) then
(((interp_cand_proj_num__0 ((extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)))))).flatMap fun c_2 => ((if h_491 : ((Option.get! (proj_num__0 c_2)) = (extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!))))) then
((if h_492 : ((proj_num__0 c_2) ≠ none) then
(((interp_wf_uN_ii (32) ((extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)))))).flatMap fun ⟨_, h_493⟩ => (((interp_allL (fun (iter : lane_) => (interp_wf_lane__ii ((fun_lanetype (.X (lanetype_packtype pt) (.mk_dim v_M)))) (iter))) (lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)).flatMap fun ⟨_, h_494⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_495⟩ => (((interp_wf_instr_i ((.VEXTRACT_LANE (.X (lanetype_packtype pt) (.mk_dim v_M)) (some v_sx) i))).flatMap fun ⟨_, h_496⟩ => (((interp_wf_instr_i ((.CONST .I32 c_2))).flatMap fun ⟨_, h_497⟩ => (((interp_wf_shape_i ((.X (lanetype_packtype pt) (.mk_dim v_M)))).flatMap fun ⟨_, h_498⟩ => ([⟨([(.CONST .I32 c_2)] : (List instr)), by subst_vars; first | (apply Step_pure.vextract_lane_pack <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vextract_lane_pack]⟩])))))))))))))
else []))
else []))))
else []))
else []))
 | none => []))
 | _ => []

def interp_Step_pure_io_vreplace_lane (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.CONST y_99 c_2), (.VREPLACE_LANE (.X v_Lnn (.mk_dim v_M)) i)] => ((if h_499 : (y_99 = (lunpack v_Lnn)) then
((if h_500 : ((lpacknum_ v_Lnn c_2) ≠ none) then
(((fun (c : vec_) (h_501 : ((inv_lanes_ (.X v_Lnn (.mk_dim v_M)) (List.modify (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1) (proj_uN_0 i) (fun (_ : lane_) => (Option.get! (lpacknum_ v_Lnn c_2))))) : vec_) = c) => (((interp_wf_uN_ii (128) ((inv_lanes_ (.X v_Lnn (.mk_dim v_M)) (List.modify (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1) (proj_uN_0 i) (fun (_ : lane_) => (Option.get! (lpacknum_ v_Lnn c_2))))))).flatMap fun ⟨_, h_502⟩ => (((interp_allL (fun (iter : lane_) => (interp_wf_lane__ii ((fun_lanetype (.X v_Lnn (.mk_dim v_M)))) (iter))) (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1)).flatMap fun ⟨_, h_503⟩ => (((interp_wf_lane__ii ((fun_lanetype (.X v_Lnn (.mk_dim v_M)))) ((Option.get! (lpacknum_ v_Lnn c_2)))).flatMap fun ⟨_, h_504⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_505⟩ => (((interp_wf_instr_i ((.CONST (lunpack v_Lnn) c_2))).flatMap fun ⟨_, h_506⟩ => (((interp_wf_instr_i ((.VREPLACE_LANE (.X v_Lnn (.mk_dim v_M)) i))).flatMap fun ⟨_, h_507⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_508⟩ => (((interp_wf_shape_i ((.X v_Lnn (.mk_dim v_M)))).flatMap fun ⟨_, h_509⟩ => ((if h_510 : ((proj_uN_0 i) < (List.length (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1))) then
([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vreplace_lane <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vreplace_lane]⟩])
else []))))))))))))))))))) ((inv_lanes_ (.X v_Lnn (.mk_dim v_M)) (List.modify (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1) (proj_uN_0 i) (fun (_ : lane_) => (Option.get! (lpacknum_ v_Lnn c_2))))) : vec_) rfl))
else []))
else []))
 | _ => []

def interp_Step_pure_io_vextunop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VEXTUNOP sh_2 sh_1 vextunop)] => (((interp_fun_vextunop___iiiio (sh_1) (sh_2) (vextunop) (c_1)).flatMap fun ⟨o_100, h_511⟩ => (match o_100 with
 | var_0 => ((if h_512 : (var_0 ≠ none) then
(((fun (c : vec_) (h_513 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_514⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_515⟩ => (((interp_wf_instr_i ((.VEXTUNOP sh_2 sh_1 vextunop))).flatMap fun ⟨_, h_516⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_517⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vextunop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vextunop]⟩])))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io_vextbinop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VEXTBINOP sh_2 sh_1 vextbinop)] => (((interp_fun_vextbinop___iiiiio (sh_1) (sh_2) (vextbinop) (c_1) (c_2)).flatMap fun ⟨o_101, h_518⟩ => (match o_101 with
 | var_0 => ((if h_519 : (var_0 ≠ none) then
(((fun (c : vec_) (h_520 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_521⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_522⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_523⟩ => (((interp_wf_instr_i ((.VEXTBINOP sh_2 sh_1 vextbinop))).flatMap fun ⟨_, h_524⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_525⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vextbinop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vextbinop]⟩])))))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io_vextternop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VEXTTERNOP sh_2 sh_1 vextternop)] => (((interp_fun_vextternop___iiiiiio (sh_1) (sh_2) (vextternop) (c_1) (c_2) (c_3)).flatMap fun ⟨o_102, h_526⟩ => (match o_102 with
 | var_0 => ((if h_527 : (var_0 ≠ none) then
(((fun (c : vec_) (h_528 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_529⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_530⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_531⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_3))).flatMap fun ⟨_, h_532⟩ => (((interp_wf_instr_i ((.VEXTTERNOP sh_2 sh_1 vextternop))).flatMap fun ⟨_, h_533⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_534⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vextternop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vextternop]⟩])))))))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io_vnarrow (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VNARROW sh_2 sh_1 v_sx)] => (((interp_fun_vnarrowop___iiiiio ((proj_ishape_0 sh_1)) ((proj_ishape_0 sh_2)) (v_sx) (c_1) (c_2)).flatMap fun ⟨o_103, h_535⟩ => (match o_103 with
 | var_0 => (((fun (c : vec_) (h_536 : (var_0 : vec_) = c) => (((interp_wf_uN_ii (128) (var_0)).flatMap fun ⟨_, h_537⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_538⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_2))).flatMap fun ⟨_, h_539⟩ => (((interp_wf_instr_i ((.VNARROW sh_2 sh_1 v_sx))).flatMap fun ⟨_, h_540⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_541⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vnarrow <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vnarrow]⟩])))))))))))) (var_0 : vec_) rfl)))))
 | _ => []

def interp_Step_pure_io_vcvtop (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  match a0 with
 | [(.VCONST .V128 c_1), (.VCVTOP sh_2 sh_1 vcvtop)] => (((interp_fun_vcvtop___iiiio (sh_1) (sh_2) (vcvtop) (c_1)).flatMap fun ⟨o_104, h_542⟩ => (match o_104 with
 | var_0 => ((if h_543 : (var_0 ≠ none) then
(((fun (c : vec_) (h_544 : ((Option.get! var_0) : vec_) = c) => (((interp_wf_uN_ii (128) ((Option.get! var_0))).flatMap fun ⟨_, h_545⟩ => (((interp_wf_instr_i ((.VCONST .V128 c_1))).flatMap fun ⟨_, h_546⟩ => (((interp_wf_instr_i ((.VCVTOP sh_2 sh_1 vcvtop))).flatMap fun ⟨_, h_547⟩ => (((interp_wf_instr_i ((.VCONST .V128 c))).flatMap fun ⟨_, h_548⟩ => ([⟨([(.VCONST .V128 c)] : (List instr)), by subst_vars; first | (apply Step_pure.vcvtop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_pure.vcvtop]⟩])))))))))) ((Option.get! var_0) : vec_) rfl))
else [])))))
 | _ => []

def interp_Step_pure_io (a0 : (List instr)) : List {o : (List instr) // (Step_pure a0 o)} :=
  interp_Step_pure_io_unreachable a0 ++
  interp_Step_pure_io_nop a0 ++
  interp_Step_pure_io_drop a0 ++
  interp_Step_pure_io_select_true a0 ++
  interp_Step_pure_io_select_false a0 ++
  interp_Step_pure_io_if_true a0 ++
  interp_Step_pure_io_if_false a0 ++
  interp_Step_pure_io_label_vals a0 ++
  interp_Step_pure_io_br_label_zero a0 ++
  interp_Step_pure_io_br_label_succ a0 ++
  interp_Step_pure_io_br_handler a0 ++
  interp_Step_pure_io_br_if_true a0 ++
  interp_Step_pure_io_br_if_false a0 ++
  interp_Step_pure_io_br_table_lt a0 ++
  interp_Step_pure_io_br_table_ge a0 ++
  interp_Step_pure_io_br_on_null_null a0 ++
  interp_Step_pure_io_br_on_null_addr a0 ++
  interp_Step_pure_io_br_on_non_null_null a0 ++
  interp_Step_pure_io_br_on_non_null_addr a0 ++
  interp_Step_pure_io_call_indirect a0 ++
  interp_Step_pure_io_return_call_indirect a0 ++
  interp_Step_pure_io_frame_vals a0 ++
  interp_Step_pure_io_return_frame a0 ++
  interp_Step_pure_io_return_label a0 ++
  interp_Step_pure_io_return_handler a0 ++
  interp_Step_pure_io_handler_vals a0 ++
  interp_Step_pure_io_trap_instrs a0 ++
  interp_Step_pure_io_trap_label a0 ++
  interp_Step_pure_io_trap_handler a0 ++
  interp_Step_pure_io_trap_frame a0 ++
  interp_Step_pure_io_local_tee a0 ++
  interp_Step_pure_io_ref_i31 a0 ++
  interp_Step_pure_io_ref_is_null_true a0 ++
  interp_Step_pure_io_ref_is_null_false a0 ++
  interp_Step_pure_io_ref_as_non_null_null a0 ++
  interp_Step_pure_io_ref_as_non_null_addr a0 ++
  interp_Step_pure_io_ref_eq_null a0 ++
  interp_Step_pure_io_ref_eq_true a0 ++
  interp_Step_pure_io_ref_eq_false a0 ++
  interp_Step_pure_io_i31_get_null a0 ++
  interp_Step_pure_io_i31_get_num a0 ++
  interp_Step_pure_io_array_new a0 ++
  interp_Step_pure_io_extern_convert_any_null a0 ++
  interp_Step_pure_io_extern_convert_any_addr a0 ++
  interp_Step_pure_io_any_convert_extern_null a0 ++
  interp_Step_pure_io_any_convert_extern_addr a0 ++
  interp_Step_pure_io_unop_val a0 ++
  interp_Step_pure_io_unop_trap a0 ++
  interp_Step_pure_io_binop_val a0 ++
  interp_Step_pure_io_binop_trap a0 ++
  interp_Step_pure_io_testop a0 ++
  interp_Step_pure_io_relop a0 ++
  interp_Step_pure_io_cvtop_val a0 ++
  interp_Step_pure_io_cvtop_trap a0 ++
  interp_Step_pure_io_vvunop a0 ++
  interp_Step_pure_io_vvbinop a0 ++
  interp_Step_pure_io_vvternop a0 ++
  interp_Step_pure_io_vvtestop a0 ++
  interp_Step_pure_io_vunop_val a0 ++
  interp_Step_pure_io_vunop_trap a0 ++
  interp_Step_pure_io_vbinop_val a0 ++
  interp_Step_pure_io_vbinop_trap a0 ++
  interp_Step_pure_io_vternop_val a0 ++
  interp_Step_pure_io_vternop_trap a0 ++
  interp_Step_pure_io_vrelop a0 ++
  interp_Step_pure_io_vshiftop a0 ++
  interp_Step_pure_io_vbitmask a0 ++
  interp_Step_pure_io_vswizzlop a0 ++
  interp_Step_pure_io_vshuffle a0 ++
  interp_Step_pure_io_vextract_lane_num a0 ++
  interp_Step_pure_io_vextract_lane_pack a0 ++
  interp_Step_pure_io_vreplace_lane a0 ++
  interp_Step_pure_io_vextunop a0 ++
  interp_Step_pure_io_vextbinop a0 ++
  interp_Step_pure_io_vextternop a0 ++
  interp_Step_pure_io_vnarrow a0 ++
  interp_Step_pure_io_vcvtop a0

def interp_wf_fieldval_i_fieldval_case_0 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.CONST v_numtype var_0) => (((interp_wf_num__ii (v_numtype) (var_0)).flatMap fun ⟨_, h_4553⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_0]⟩])))
 | _ => []

def interp_wf_fieldval_i_fieldval_case_1 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.VCONST v_vectype var_0) => (((interp_wf_uN_ii ((vsize v_vectype)) (var_0)).flatMap fun ⟨_, h_4554⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_1]⟩])))
 | _ => []

def interp_wf_fieldval_i_fieldval_case_2 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_I31_NUM v_u31) => (((interp_wf_uN_ii (31) (v_u31)).flatMap fun ⟨_, h_4555⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_2]⟩])))
 | _ => []

def interp_wf_fieldval_i_fieldval_case_3 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | .REF_NULL_ADDR => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_3]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_4 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_STRUCT_ADDR v_structaddr) => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_4]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_5 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_ARRAY_ADDR v_arrayaddr) => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_5]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_6 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_FUNC_ADDR v_funcaddr) => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_6]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_7 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_EXN_ADDR v_exnaddr) => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_7 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_7]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_8 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_HOST_ADDR v_hostaddr) => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_8 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_8]⟩])
 | _ => []

def interp_wf_fieldval_i_fieldval_case_9 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.REF_EXTERN v_ref) => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_4556⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_9 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_9]⟩])))
 | _ => []

def interp_wf_fieldval_i_fieldval_case_10 (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  match a0 with
 | (.PACK v_packtype var_0) => (((interp_wf_uN_ii ((psize v_packtype)) (var_0)).flatMap fun ⟨_, h_4557⟩ => ([⟨(), by subst_vars; first | (apply wf_fieldval.fieldval_case_10 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_fieldval.fieldval_case_10]⟩])))
 | _ => []

def interp_wf_fieldval_i (a0 : fieldval) : List {o : Unit // (wf_fieldval a0)} :=
  interp_wf_fieldval_i_fieldval_case_0 a0 ++
  interp_wf_fieldval_i_fieldval_case_1 a0 ++
  interp_wf_fieldval_i_fieldval_case_2 a0 ++
  interp_wf_fieldval_i_fieldval_case_3 a0 ++
  interp_wf_fieldval_i_fieldval_case_4 a0 ++
  interp_wf_fieldval_i_fieldval_case_5 a0 ++
  interp_wf_fieldval_i_fieldval_case_6 a0 ++
  interp_wf_fieldval_i_fieldval_case_7 a0 ++
  interp_wf_fieldval_i_fieldval_case_8 a0 ++
  interp_wf_fieldval_i_fieldval_case_9 a0 ++
  interp_wf_fieldval_i_fieldval_case_10 a0

def interp_wf_arrayinst_i_arrayinst_case_ (a0 : arrayinst) : List {o : Unit // (wf_arrayinst a0)} :=
  match a0 with
 | { TYPE := var_0, FIELDS := var_1_lst } => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_4152⟩ => (((interp_allL (fun (var_1 : fieldval) => (interp_wf_fieldval_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4153⟩ => ([⟨(), by subst_vars; first | (apply wf_arrayinst.arrayinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_arrayinst.arrayinst_case_]⟩])))))

def interp_wf_arrayinst_i (a0 : arrayinst) : List {o : Unit // (wf_arrayinst a0)} :=
  interp_wf_arrayinst_i_arrayinst_case_ a0

def interp_fun_type_iio_fun_type_case_0 (a0 : state) (a1 : typeidx) : List {o : deftype // (fun_type a0 a1 o)} :=
  match a0, a1 with
 | z, x => (((interp_wf_frame_i ((fof z))).flatMap fun ⟨_, h_4151⟩ => ([⟨((((fof z).MODULE).TYPES)[(proj_uN_0 x)]!), by subst_vars; first | (apply fun_type.fun_type_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_type.fun_type_case_0]⟩])))

def interp_fun_type_iio (a0 : state) (a1 : typeidx) : List {o : deftype // (fun_type a0 a1 o)} :=
  interp_fun_type_iio_fun_type_case_0 a0 a1

def interp_wf_limits_i_limits_case_0 (a0 : limits) : List {o : Unit // (wf_limits a0)} :=
  match a0 with
 | (.mk_limits v_u64 u64_opt) => (((interp_wf_uN_ii (64) (v_u64)).flatMap fun ⟨_, h_4706⟩ => (((interp_allL (fun (v_u64 : u64) => (interp_wf_uN_ii (64) (v_u64))) (Option.toList u64_opt)).flatMap fun ⟨_, h_4707⟩ => ([⟨(), by subst_vars; first | (apply wf_limits.limits_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_limits.limits_case_0]⟩])))))

def interp_wf_limits_i (a0 : limits) : List {o : Unit // (wf_limits a0)} :=
  interp_wf_limits_i_limits_case_0 a0

def interp_wf_memtype_i_memtype_case_0 (a0 : memtype) : List {o : Unit // (wf_memtype a0)} :=
  match a0 with
 | (.PAGE v_addrtype v_limits) => (((interp_wf_limits_i (v_limits)).flatMap fun ⟨_, h_4540⟩ => ([⟨(), by subst_vars; first | (apply wf_memtype.memtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_memtype.memtype_case_0]⟩])))

def interp_wf_memtype_i (a0 : memtype) : List {o : Unit // (wf_memtype a0)} :=
  interp_wf_memtype_i_memtype_case_0 a0

def interp_wf_meminst_i_meminst_case_ (a0 : meminst) : List {o : Unit // (wf_meminst a0)} :=
  match a0 with
 | { TYPE := var_0, BYTES := var_1_lst } => (((interp_wf_memtype_i (var_0)).flatMap fun ⟨_, h_4123⟩ => (((interp_allL (fun (var_1 : byte) => (interp_wf_byte_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4124⟩ => ([⟨(), by subst_vars; first | (apply wf_meminst.meminst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_meminst.meminst_case_]⟩])))))

def interp_wf_meminst_i (a0 : meminst) : List {o : Unit // (wf_meminst a0)} :=
  interp_wf_meminst_i_meminst_case_ a0

def interp_fun_growmem_iio (a0 : meminst) (a1 : Nat) : List {o : (Option meminst) // (fun_growmem a0 a1 o)} :=
  []

def interp_wf_tabletype_i_tabletype_case_0 (a0 : tabletype) : List {o : Unit // (wf_tabletype a0)} :=
  match a0 with
 | (.mk_tabletype v_addrtype v_limits v_reftype) => (((interp_wf_limits_i (v_limits)).flatMap fun ⟨_, h_4536⟩ => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_4537⟩ => ([⟨(), by subst_vars; first | (apply wf_tabletype.tabletype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_tabletype.tabletype_case_0]⟩])))))

def interp_wf_tabletype_i (a0 : tabletype) : List {o : Unit // (wf_tabletype a0)} :=
  interp_wf_tabletype_i_tabletype_case_0 a0

def interp_wf_tableinst_i_tableinst_case_ (a0 : tableinst) : List {o : Unit // (wf_tableinst a0)} :=
  match a0 with
 | { TYPE := var_0, REFS := var_1_lst } => (((interp_wf_tabletype_i (var_0)).flatMap fun ⟨_, h_4101⟩ => (((interp_allL (fun (var_1 : ref) => (interp_wf_ref_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4102⟩ => ([⟨(), by subst_vars; first | (apply wf_tableinst.tableinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_tableinst.tableinst_case_]⟩])))))

def interp_wf_tableinst_i (a0 : tableinst) : List {o : Unit // (wf_tableinst a0)} :=
  interp_wf_tableinst_i_tableinst_case_ a0

def interp_fun_growtable_iiio (a0 : tableinst) (a1 : Nat) (a2 : ref) : List {o : (Option tableinst) // (fun_growtable a0 a1 a2 o)} :=
  []

def interp_wf_exninst_i_exninst_case_ (a0 : exninst) : List {o : Unit // (wf_exninst a0)} :=
  match a0 with
 | { TAG := var_0, FIELDS := var_1_lst } => (((interp_allL (fun (var_1 : val) => (interp_wf_val_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4100⟩ => ([⟨(), by subst_vars; first | (apply wf_exninst.exninst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_exninst.exninst_case_]⟩])))

def interp_wf_exninst_i (a0 : exninst) : List {o : Unit // (wf_exninst a0)} :=
  interp_wf_exninst_i_exninst_case_ a0

def interp_wf_taginst_i_taginst_case_ (a0 : taginst) : List {o : Unit // (wf_taginst a0)} :=
  match a0 with
 | { TYPE := var_0 } => (((interp_wf_typeuse_i (var_0)).flatMap fun ⟨_, h_4092⟩ => ([⟨(), by subst_vars; first | (apply wf_taginst.taginst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_taginst.taginst_case_]⟩])))

def interp_wf_taginst_i (a0 : taginst) : List {o : Unit // (wf_taginst a0)} :=
  interp_wf_taginst_i_taginst_case_ a0

def interp_fun_unrollrt_io (a0 : rectype) : List {o : rectype // (fun_unrollrt a0 o)} :=
  []

def interp_fun_unrolldt_io_fun_unrolldt_case_0 (a0 : deftype) : List {o : subtype // (fun_unrolldt a0 o)} :=
  match a0 with
 | (._DEF v_rectype i) => (((interp_fun_unrollrt_io (v_rectype)).flatMap fun ⟨o_364, h_4545⟩ => (match o_364 with
 | var_0 => ((match h_4546 : (var_0 : rectype) with
 | (.REC (.mk_list subtype_lst)) => (((interp_wf_rectype_i ((.REC (.mk_list subtype_lst)))).flatMap fun ⟨_, h_4547⟩ => ([⟨(subtype_lst[i]!), by subst_vars; first | (apply fun_unrolldt.fun_unrolldt_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_unrolldt.fun_unrolldt_case_0]⟩]))))))))

def interp_fun_unrolldt_io (a0 : deftype) : List {o : subtype // (fun_unrolldt a0 o)} :=
  interp_fun_unrolldt_io_fun_unrolldt_case_0 a0

def interp_Expand_io_mk_Expand (a0 : deftype) : List {o : comptype // (Expand a0 o)} :=
  match a0 with
 | v_deftype => (((interp_fun_unrolldt_io (v_deftype)).flatMap fun ⟨o_342, h_4086⟩ => (match o_342 with
 | var_0 => ((match h_4087 : (var_0 : subtype) with
 | (.SUB final_opt typeuse_lst v_comptype) => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_4088⟩ => (((interp_wf_subtype_i (var_0)).flatMap fun ⟨_, h_4089⟩ => (((interp_wf_subtype_i ((.SUB final_opt typeuse_lst v_comptype))).flatMap fun ⟨_, h_4090⟩ => ([⟨v_comptype, by subst_vars; first | (apply Expand.mk_Expand <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Expand.mk_Expand]⟩]))))))))))))

def interp_Expand_io (a0 : deftype) : List {o : comptype // (Expand a0 o)} :=
  interp_Expand_io_mk_Expand a0

def interp_fun_default__io_fun_default__case_0 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | .I32 => ([⟨(some (some (.CONST (numtype_addrtype .I32) (.mk_num__0 .I32 (.mk_uN 0))))), by subst_vars; first | (apply fun_default_.fun_default__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_0]⟩])
 | _ => []

def interp_fun_default__io_fun_default__case_1 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | .I64 => ([⟨(some (some (.CONST (numtype_addrtype .I64) (.mk_num__0 .I64 (.mk_uN 0))))), by subst_vars; first | (apply fun_default_.fun_default__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_1]⟩])
 | _ => []

def interp_fun_default__io_fun_default__case_2 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | .F32 => (((interp_fun_fzero_io ((size (numtype_Fnn .F32)))).flatMap fun ⟨o_362, h_4542⟩ => (match o_362 with
 | var_0 => ([⟨(some (some (.CONST (numtype_Fnn .F32) (.mk_num__1 .F32 var_0)))), by subst_vars; first | (apply fun_default_.fun_default__case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_2]⟩]))))
 | _ => []

def interp_fun_default__io_fun_default__case_3 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | .F64 => (((interp_fun_fzero_io ((size (numtype_Fnn .F64)))).flatMap fun ⟨o_363, h_4543⟩ => (match o_363 with
 | var_0 => ([⟨(some (some (.CONST (numtype_Fnn .F64) (.mk_num__1 .F64 var_0)))), by subst_vars; first | (apply fun_default_.fun_default__case_3 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_3]⟩]))))
 | _ => []

def interp_fun_default__io_fun_default__case_4 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | .V128 => ([⟨(some (some (.VCONST .V128 (.mk_uN 0)))), by subst_vars; first | (apply fun_default_.fun_default__case_4 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_4]⟩])
 | _ => []

def interp_fun_default__io_fun_default__case_5 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | (.REF (some .NULL) ht) => ([⟨(some (some .REF_NULL_ADDR)), by subst_vars; first | (apply fun_default_.fun_default__case_5 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_5]⟩])
 | _ => []

def interp_fun_default__io_fun_default__case_6 (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  match a0 with
 | (.REF none ht) => ([⟨(some none), by subst_vars; first | (apply fun_default_.fun_default__case_6 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_default_.fun_default__case_6]⟩])
 | _ => []

def interp_fun_default__io (a0 : valtype) : List {o : (Option (Option val)) // (fun_default_ a0 o)} :=
  interp_fun_default__io_fun_default__case_0 a0 ++
  interp_fun_default__io_fun_default__case_1 a0 ++
  interp_fun_default__io_fun_default__case_2 a0 ++
  interp_fun_default__io_fun_default__case_3 a0 ++
  interp_fun_default__io_fun_default__case_4 a0 ++
  interp_fun_default__io_fun_default__case_5 a0 ++
  interp_fun_default__io_fun_default__case_6 a0

def interp_wf_datainst_i_datainst_case_ (a0 : datainst) : List {o : Unit // (wf_datainst a0)} :=
  match a0 with
 | { BYTES := var_0_lst } => (((interp_allL (fun (var_0 : byte) => (interp_wf_byte_i (var_0))) var_0_lst).flatMap fun ⟨_, h_4541⟩ => ([⟨(), by subst_vars; first | (apply wf_datainst.datainst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_datainst.datainst_case_]⟩])))

def interp_wf_datainst_i (a0 : datainst) : List {o : Unit // (wf_datainst a0)} :=
  interp_wf_datainst_i_datainst_case_ a0

def interp_wf_eleminst_i_eleminst_case_ (a0 : eleminst) : List {o : Unit // (wf_eleminst a0)} :=
  match a0 with
 | { TYPE := var_0, REFS := var_1_lst } => (((interp_wf_reftype_i (var_0)).flatMap fun ⟨_, h_4538⟩ => (((interp_allL (fun (var_1 : ref) => (interp_wf_ref_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4539⟩ => ([⟨(), by subst_vars; first | (apply wf_eleminst.eleminst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_eleminst.eleminst_case_]⟩])))))

def interp_wf_eleminst_i (a0 : eleminst) : List {o : Unit // (wf_eleminst a0)} :=
  interp_wf_eleminst_i_eleminst_case_ a0

def interp_wf_globaltype_i_globaltype_case_0 (a0 : globaltype) : List {o : Unit // (wf_globaltype a0)} :=
  match a0 with
 | (.mk_globaltype mut_opt v_valtype) => (((interp_wf_valtype_i (v_valtype)).flatMap fun ⟨_, h_4705⟩ => ([⟨(), by subst_vars; first | (apply wf_globaltype.globaltype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_globaltype.globaltype_case_0]⟩])))

def interp_wf_globaltype_i (a0 : globaltype) : List {o : Unit // (wf_globaltype a0)} :=
  interp_wf_globaltype_i_globaltype_case_0 a0

def interp_wf_globalinst_i_globalinst_case_ (a0 : globalinst) : List {o : Unit // (wf_globalinst a0)} :=
  match a0 with
 | { TYPE := var_0, VALUE := var_1 } => (((interp_wf_globaltype_i (var_0)).flatMap fun ⟨_, h_4534⟩ => (((interp_wf_val_i (var_1)).flatMap fun ⟨_, h_4535⟩ => ([⟨(), by subst_vars; first | (apply wf_globalinst.globalinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_globalinst.globalinst_case_]⟩])))))

def interp_wf_globalinst_i (a0 : globalinst) : List {o : Unit // (wf_globalinst a0)} :=
  interp_wf_globalinst_i_globalinst_case_ a0

def interp_wf_local_i_local_case_0 (a0 : «local») : List {o : Unit // (wf_local a0)} :=
  match a0 with
 | (.LOCAL v_valtype) => (((interp_wf_valtype_i (v_valtype)).flatMap fun ⟨_, h_4869⟩ => ([⟨(), by subst_vars; first | (apply wf_local.local_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_local.local_case_0]⟩])))

def interp_wf_local_i (a0 : «local») : List {o : Unit // (wf_local a0)} :=
  interp_wf_local_i_local_case_0 a0

def interp_wf_funccode_i_funccode_case_0 (a0 : funccode) : List {o : Unit // (wf_funccode a0)} :=
  match a0 with
 | (.FUNC v_typeidx local_lst v_expr) => (((interp_wf_uN_ii (32) (v_typeidx)).flatMap fun ⟨_, h_4702⟩ => (((interp_allL (fun (v_local : «local») => (interp_wf_local_i (v_local))) local_lst).flatMap fun ⟨_, h_4703⟩ => (((interp_allL (fun (v_expr : instr) => (interp_wf_instr_i (v_expr))) v_expr).flatMap fun ⟨_, h_4704⟩ => ([⟨(), by subst_vars; first | (apply wf_funccode.funccode_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_funccode.funccode_case_0]⟩])))))))
 | _ => []

def interp_wf_funccode_i_funccode_case_1 (a0 : funccode) : List {o : Unit // (wf_funccode a0)} :=
  match a0 with
 | .mk_funccode => ([⟨(), by subst_vars; first | (apply wf_funccode.funccode_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_funccode.funccode_case_1]⟩])
 | _ => []

def interp_wf_funccode_i (a0 : funccode) : List {o : Unit // (wf_funccode a0)} :=
  interp_wf_funccode_i_funccode_case_0 a0 ++
  interp_wf_funccode_i_funccode_case_1 a0

def interp_wf_funcinst_i_funcinst_case_ (a0 : funcinst) : List {o : Unit // (wf_funcinst a0)} :=
  match a0 with
 | { TYPE := var_0, MODULE := var_1, CODE := var_2 } => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_4531⟩ => (((interp_wf_moduleinst_i (var_1)).flatMap fun ⟨_, h_4532⟩ => (((interp_wf_funccode_i (var_2)).flatMap fun ⟨_, h_4533⟩ => ([⟨(), by subst_vars; first | (apply wf_funcinst.funcinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_funcinst.funcinst_case_]⟩])))))))

def interp_wf_funcinst_i (a0 : funcinst) : List {o : Unit // (wf_funcinst a0)} :=
  interp_wf_funcinst_i_funcinst_case_ a0

def interp_wf_localtype_i_localtype_case_0 (a0 : localtype) : List {o : Unit // (wf_localtype a0)} :=
  match a0 with
 | (.mk_localtype v_init v_valtype) => (((interp_wf_valtype_i (v_valtype)).flatMap fun ⟨_, h_4865⟩ => ([⟨(), by subst_vars; first | (apply wf_localtype.localtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_localtype.localtype_case_0]⟩])))

def interp_wf_localtype_i (a0 : localtype) : List {o : Unit // (wf_localtype a0)} :=
  interp_wf_localtype_i_localtype_case_0 a0

def interp_wf_context_i_context_case_ (a0 : context) : List {o : Unit // (wf_context a0)} :=
  match a0 with
 | { TYPES := var_0_lst, TAGS := var_1_lst, GLOBALS := var_2_lst, MEMS := var_3_lst, TABLES := var_4_lst, FUNCS := var_5_lst, DATAS := var_6_lst, ELEMS := var_7_lst, LOCALS := var_8_lst, LABELS := var_9_lst, RETURN := var_10_opt, REFS := var_11_lst, RECS := var_12_lst } => (((interp_allL (fun (var_0 : deftype) => (interp_wf_deftype_i (var_0))) var_0_lst).flatMap fun ⟨_, h_4685⟩ => (((interp_allL (fun (var_1 : tagtype) => (interp_wf_typeuse_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4686⟩ => (((interp_allL (fun (var_2 : globaltype) => (interp_wf_globaltype_i (var_2))) var_2_lst).flatMap fun ⟨_, h_4687⟩ => (((interp_allL (fun (var_3 : memtype) => (interp_wf_memtype_i (var_3))) var_3_lst).flatMap fun ⟨_, h_4688⟩ => (((interp_allL (fun (var_4 : tabletype) => (interp_wf_tabletype_i (var_4))) var_4_lst).flatMap fun ⟨_, h_4689⟩ => (((interp_allL (fun (var_5 : deftype) => (interp_wf_deftype_i (var_5))) var_5_lst).flatMap fun ⟨_, h_4690⟩ => (((interp_allL (fun (var_7 : elemtype) => (interp_wf_reftype_i (var_7))) var_7_lst).flatMap fun ⟨_, h_4691⟩ => (((interp_allL (fun (var_8 : localtype) => (interp_wf_localtype_i (var_8))) var_8_lst).flatMap fun ⟨_, h_4692⟩ => (((interp_allL (fun (var_9 : resulttype) => (if h_4700 : ((List.length (List.map (fun (X_17413 : valtype) => X_17413) (proj_list_0 valtype var_9))) < (2 ^ 32)) then [⟨(), h_4700⟩] else [])) var_9_lst).flatMap fun ⟨_, h_4693⟩ => (((interp_allL (fun (var_9 : resulttype) => (interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype var_9))) var_9_lst).flatMap fun ⟨_, h_4694⟩ => (((interp_allL (fun (var_10 : resulttype) => (if h_4699 : ((List.length (List.map (fun (X_17414 : valtype) => X_17414) (proj_list_0 valtype var_10))) < (2 ^ 32)) then [⟨(), h_4699⟩] else [])) (Option.toList var_10_opt)).flatMap fun ⟨_, h_4695⟩ => (((interp_allL (fun (var_10 : resulttype) => (interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype var_10))) (Option.toList var_10_opt)).flatMap fun ⟨_, h_4696⟩ => (((interp_allL (fun (var_11 : funcidx) => (interp_wf_uN_ii (32) (var_11))) var_11_lst).flatMap fun ⟨_, h_4697⟩ => (((interp_allL (fun (var_12 : subtype) => (interp_wf_subtype_i (var_12))) var_12_lst).flatMap fun ⟨_, h_4698⟩ => ([⟨(), by subst_vars; first | (apply wf_context.context_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_context.context_case_]⟩])))))))))))))))))))))))))))))

def interp_wf_context_i (a0 : context) : List {o : Unit // (wf_context a0)} :=
  interp_wf_context_i_context_case_ a0

def interp_fun_subst_rectype_iiio (a0 : rectype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : rectype // (fun_subst_rectype a0 a1 a2 o)} :=
  []

def interp_fun_subst_deftype_iiio_fun_subst_deftype_case_0 (a0 : deftype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : deftype // (fun_subst_deftype a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (._DEF qt i), tv_lst, tu_lst => (((interp_fun_subst_rectype_iiio (qt) (tv_lst) (tu_lst)).flatMap fun ⟨o_393, h_4994⟩ => (match o_393 with
 | var_1 => ((match o_393 with
 | var_0 => (((interp_wf_deftype_i ((._DEF var_1 i))).flatMap fun ⟨_, h_4996⟩ => ([⟨(._DEF var_0 i), by subst_vars; first | (apply fun_subst_deftype.fun_subst_deftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_deftype.fun_subst_deftype_case_0]⟩]))))))))

def interp_fun_subst_deftype_iiio (a0 : deftype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : deftype // (fun_subst_deftype a0 a1 a2 o)} :=
  interp_fun_subst_deftype_iiio_fun_subst_deftype_case_0 a0 a1 a2

def interp_fun_subst_all_deftype_iio (a0 : deftype) (a1 : (List typeuse)) : List {o : deftype // (fun_subst_all_deftype a0 a1 o)} :=
  []

mutual

partial def interp_fun_clos_deftypes_io_fun_clos_deftypes_case_0 (a0 : (List deftype)) : List {o : (List deftype) // (fun_clos_deftypes a0 o)} :=
  match a0 with
 | [] => ([⟨[], by subst_vars; first | (apply fun_clos_deftypes.fun_clos_deftypes_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_clos_deftypes.fun_clos_deftypes_case_0]⟩])
 | _ => []

partial def interp_fun_clos_deftypes_io_fun_clos_deftypes_case_1 (a0 : (List deftype)) : List {o : (List deftype) // (fun_clos_deftypes a0 o)} :=
  match a0 with
 | y_397 => (((interp_splits y_397).flatMap fun ⟨(a_398, b_399), h_5075⟩ => ((match a_398 with
 | dt_lst => ((match b_399 with
 | [dt_n] => (((interp_fun_clos_deftypes_io (dt_lst)).flatMap fun ⟨o_400, h_5078⟩ => (match o_400 with
 | var_3 => ((match o_400 with
 | var_1 => (((fun (dt'_lst : (List deftype)) (h_5083 : (var_1 : (List deftype)) = dt'_lst) => (((interp_fun_subst_all_deftype_iio (dt_n) ((List.map (fun (dt'_2 : deftype) => (typeuse_deftype dt'_2)) dt'_lst))).flatMap fun ⟨o_401, h_5084⟩ => (match o_401 with
 | var_2 => ((match o_401 with
 | var_0 => (((interp_wf_deftype_i (var_2)).flatMap fun ⟨_, h_5086⟩ => (((interp_allL (fun (iter_8 : deftype) => (interp_wf_deftype_i (iter_8))) var_3).flatMap fun ⟨_, h_5087⟩ => ([⟨(dt'_lst ++ ([var_0] : (List deftype))), by subst_vars; first | (apply fun_clos_deftypes.fun_clos_deftypes_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_clos_deftypes.fun_clos_deftypes_case_1]⟩]))))))))))) (var_1 : (List deftype)) rfl)))))))
 | _ => []))))))

partial def interp_fun_clos_deftypes_io (a0 : (List deftype)) : List {o : (List deftype) // (fun_clos_deftypes a0 o)} :=
  interp_fun_clos_deftypes_io_fun_clos_deftypes_case_0 a0 ++
  interp_fun_clos_deftypes_io_fun_clos_deftypes_case_1 a0

end

def interp_fun_clos_deftype_iio_fun_clos_deftype_case_0 (a0 : context) (a1 : deftype) : List {o : deftype // (fun_clos_deftype a0 a1 o)} :=
  match a0, a1 with
 | C, dt => (((interp_fun_clos_deftypes_io ((C.TYPES))).flatMap fun ⟨o_395, h_5029⟩ => (match o_395 with
 | var_1 => (((fun (dt'_lst : (List deftype)) (h_5032 : (var_1 : (List deftype)) = dt'_lst) => (((interp_fun_subst_all_deftype_iio (dt) ((List.map (fun (dt'_4 : deftype) => (typeuse_deftype dt'_4)) dt'_lst))).flatMap fun ⟨o_396, h_5033⟩ => (match o_396 with
 | var_2 => ((match o_396 with
 | var_0 => (((interp_wf_deftype_i (var_2)).flatMap fun ⟨_, h_5035⟩ => (((interp_allL (fun (iter_9 : deftype) => (interp_wf_deftype_i (iter_9))) var_1).flatMap fun ⟨_, h_5036⟩ => ([⟨var_0, by subst_vars; first | (apply fun_clos_deftype.fun_clos_deftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_clos_deftype.fun_clos_deftype_case_0]⟩]))))))))))) (var_1 : (List deftype)) rfl)))))

def interp_fun_clos_deftype_iio (a0 : context) (a1 : deftype) : List {o : deftype // (fun_clos_deftype a0 a1 o)} :=
  interp_fun_clos_deftype_iio_fun_clos_deftype_case_0 a0 a1

def interp_Deftype_sub_iii_refl (a0 : context) (a1 : deftype) (a2 : deftype) : List {o : Unit // (Deftype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, deftype_1, deftype_2 => (((interp_fun_clos_deftype_iio (C) (deftype_2)).flatMap fun ⟨o_389, h_4894⟩ => (match o_389 with
 | var_1 => (((interp_fun_clos_deftype_iio (C) (deftype_1)).flatMap fun ⟨o_390, h_4895⟩ => (match o_390 with
 | var_0 => ((if h_4896 : (var_0 = var_1) then
(((interp_wf_context_i (C)).flatMap fun ⟨_, h_4897⟩ => (((interp_wf_deftype_i (deftype_1)).flatMap fun ⟨_, h_4898⟩ => (((interp_wf_deftype_i (deftype_2)).flatMap fun ⟨_, h_4899⟩ => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_4900⟩ => (((interp_wf_deftype_i (var_1)).flatMap fun ⟨_, h_4901⟩ => ([⟨(), by subst_vars; first | (apply Deftype_sub.refl <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Deftype_sub.refl]⟩])))))))))))
else []))))))))

def interp_Deftype_sub_iii (a0 : context) (a1 : deftype) (a2 : deftype) : List {o : Unit // (Deftype_sub a0 a1 a2)} :=
  interp_Deftype_sub_iii_refl a0 a1 a2

def interp_Deftype_ok_io (a0 : context) : List {o : deftype // (Deftype_ok a0 o)} :=
  []

def interp_Typeuse_ok_io_deftype (a0 : context) : List {o : typeuse // (Typeuse_ok a0 o)} :=
  match a0 with
 | C => (((interp_Deftype_ok_io (C)).flatMap fun ⟨o_394, h_5011⟩ => (match o_394 with
 | v_deftype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5012⟩ => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_5013⟩ => ([⟨(typeuse_deftype v_deftype), by subst_vars; first | (apply Typeuse_ok.deftype <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Typeuse_ok.deftype]⟩]))))))))

def interp_Typeuse_ok_io (a0 : context) : List {o : typeuse // (Typeuse_ok a0 o)} :=
  interp_Typeuse_ok_io_deftype a0

def interp_Heaptype_ok_io_typeuse (a0 : context) : List {o : heaptype // (Heaptype_ok a0 o)} :=
  match a0 with
 | C => (((interp_Typeuse_ok_io (C)).flatMap fun ⟨o_387, h_4875⟩ => (match o_387 with
 | v_typeuse => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4876⟩ => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_4877⟩ => ([⟨(heaptype_typeuse v_typeuse), by subst_vars; first | (apply Heaptype_ok.typeuse <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_ok.typeuse]⟩]))))))))

def interp_Heaptype_ok_io_bot (a0 : context) : List {o : heaptype // (Heaptype_ok a0 o)} :=
  match a0 with
 | C => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4878⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4879⟩ => ([⟨.BOT, by subst_vars; first | (apply Heaptype_ok.bot <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_ok.bot]⟩])))))

def interp_Heaptype_ok_io (a0 : context) : List {o : heaptype // (Heaptype_ok a0 o)} :=
  interp_Heaptype_ok_io_typeuse a0 ++
  interp_Heaptype_ok_io_bot a0

mutual

partial def interp_Heaptype_sub_iii_refl (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, v_heaptype, y_372 => ((if h_4745 : (y_372 = v_heaptype) then
(((interp_wf_context_i (C)).flatMap fun ⟨_, h_4746⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4747⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.refl <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.refl]⟩])))))
else []))

partial def interp_Heaptype_sub_iii_trans (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, heaptype_1, heaptype_2 => (((interp_Heaptype_ok_io (C)).flatMap fun ⟨o_373, h_4748⟩ => (match o_373 with
 | heaptype' => (((interp_Heaptype_sub_iii (C) (heaptype_1) (heaptype')).flatMap fun ⟨_, h_4749⟩ => (((interp_Heaptype_sub_iii (C) (heaptype') (heaptype_2)).flatMap fun ⟨_, h_4750⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4751⟩ => (((interp_wf_heaptype_i (heaptype_1)).flatMap fun ⟨_, h_4752⟩ => (((interp_wf_heaptype_i (heaptype_2)).flatMap fun ⟨_, h_4753⟩ => (((interp_wf_heaptype_i (heaptype')).flatMap fun ⟨_, h_4754⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.trans <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.trans]⟩]))))))))))))))))

partial def interp_Heaptype_sub_iii_eq_any (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .EQ, .ANY => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4755⟩ => (((interp_wf_heaptype_i (.EQ)).flatMap fun ⟨_, h_4756⟩ => (((interp_wf_heaptype_i (.ANY)).flatMap fun ⟨_, h_4757⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.eq_any <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.eq_any]⟩])))))))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_i31_eq (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .I31, .EQ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4758⟩ => (((interp_wf_heaptype_i (.I31)).flatMap fun ⟨_, h_4759⟩ => (((interp_wf_heaptype_i (.EQ)).flatMap fun ⟨_, h_4760⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.i31_eq <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.i31_eq]⟩])))))))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_struct_eq (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .STRUCT, .EQ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4761⟩ => (((interp_wf_heaptype_i (.STRUCT)).flatMap fun ⟨_, h_4762⟩ => (((interp_wf_heaptype_i (.EQ)).flatMap fun ⟨_, h_4763⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.struct_eq <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.struct_eq]⟩])))))))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_array_eq (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .ARRAY, .EQ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4764⟩ => (((interp_wf_heaptype_i (.ARRAY)).flatMap fun ⟨_, h_4765⟩ => (((interp_wf_heaptype_i (.EQ)).flatMap fun ⟨_, h_4766⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.array_eq <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.array_eq]⟩])))))))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_struct (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, y_374, .STRUCT => ((match interp_inv_heaptype_deftype y_374 with
 | some ⟨v_deftype, h_4767⟩ => (((interp_Expand_io (v_deftype)).flatMap fun ⟨o_375, h_4768⟩ => (match o_375 with
 | (.STRUCT (.mk_list fieldtype_lst)) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4769⟩ => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_4770⟩ => (((interp_wf_heaptype_i (.STRUCT)).flatMap fun ⟨_, h_4771⟩ => (((interp_wf_comptype_i ((.STRUCT (.mk_list fieldtype_lst)))).flatMap fun ⟨_, h_4772⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.struct <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.struct]⟩])))))))))
 | _ => [])))
 | none => []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_array (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, y_376, .ARRAY => ((match interp_inv_heaptype_deftype y_376 with
 | some ⟨v_deftype, h_4773⟩ => (((interp_Expand_io (v_deftype)).flatMap fun ⟨o_377, h_4774⟩ => (match o_377 with
 | (.ARRAY v_fieldtype) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4775⟩ => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_4776⟩ => (((interp_wf_heaptype_i (.ARRAY)).flatMap fun ⟨_, h_4777⟩ => (((interp_wf_comptype_i ((.ARRAY v_fieldtype))).flatMap fun ⟨_, h_4778⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.array]⟩])))))))))
 | _ => [])))
 | none => []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_func (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, y_378, .FUNC => ((match interp_inv_heaptype_deftype y_378 with
 | some ⟨v_deftype, h_4779⟩ => (((interp_Expand_io (v_deftype)).flatMap fun ⟨o_379, h_4780⟩ => (match o_379 with
 | (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4781⟩ => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_4782⟩ => (((interp_wf_heaptype_i (.FUNC)).flatMap fun ⟨_, h_4783⟩ => (((interp_wf_comptype_i ((.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)))).flatMap fun ⟨_, h_4784⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.func]⟩])))))))))
 | _ => [])))
 | none => []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_def (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, y_380, y_381 => ((match interp_inv_heaptype_deftype y_380 with
 | some ⟨deftype_1, h_4785⟩ => ((match interp_inv_heaptype_deftype y_381 with
 | some ⟨deftype_2, h_4786⟩ => (((interp_Deftype_sub_iii (C) (deftype_1) (deftype_2)).flatMap fun ⟨_, h_4787⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4788⟩ => (((interp_wf_deftype_i (deftype_1)).flatMap fun ⟨_, h_4789⟩ => (((interp_wf_deftype_i (deftype_2)).flatMap fun ⟨_, h_4790⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.def <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.def]⟩])))))))))
 | none => []))
 | none => []))

partial def interp_Heaptype_sub_iii_typeidx_l (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (._IDX v_typeidx), v_heaptype => ((if h_4791 : ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) then
(((interp_Heaptype_sub_iii (C) ((heaptype_deftype ((C.TYPES)[(proj_uN_0 v_typeidx)]!))) (v_heaptype)).flatMap fun ⟨_, h_4792⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4793⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4794⟩ => (((interp_wf_heaptype_i ((._IDX v_typeidx))).flatMap fun ⟨_, h_4795⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.typeidx_l <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.typeidx_l]⟩])))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_typeidx_r (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, v_heaptype, (._IDX v_typeidx) => ((if h_4796 : ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) then
(((interp_Heaptype_sub_iii (C) (v_heaptype) ((heaptype_deftype ((C.TYPES)[(proj_uN_0 v_typeidx)]!)))).flatMap fun ⟨_, h_4797⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4798⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4799⟩ => (((interp_wf_heaptype_i ((._IDX v_typeidx))).flatMap fun ⟨_, h_4800⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.typeidx_r <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.typeidx_r]⟩])))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_rec_struct (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REC i), .STRUCT => ((if h_4801 : (i < (List.length (C.RECS))) then
((match h_4802 : (((C.RECS)[i]!) : subtype) with
 | (.SUB final_opt [] (.STRUCT (.mk_list fieldtype_lst))) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4803⟩ => (((interp_wf_heaptype_i ((.REC i))).flatMap fun ⟨_, h_4804⟩ => (((interp_wf_heaptype_i (.STRUCT)).flatMap fun ⟨_, h_4805⟩ => (((interp_wf_subtype_i ((.SUB final_opt [] (.STRUCT (.mk_list fieldtype_lst))))).flatMap fun ⟨_, h_4806⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.rec_struct <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.rec_struct]⟩])))))))))
 | _ => []))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_rec_array (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REC i), .ARRAY => ((if h_4807 : (i < (List.length (C.RECS))) then
((match h_4808 : (((C.RECS)[i]!) : subtype) with
 | (.SUB final_opt [] (.ARRAY v_fieldtype)) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4809⟩ => (((interp_wf_heaptype_i ((.REC i))).flatMap fun ⟨_, h_4810⟩ => (((interp_wf_heaptype_i (.ARRAY)).flatMap fun ⟨_, h_4811⟩ => (((interp_wf_subtype_i ((.SUB final_opt [] (.ARRAY v_fieldtype)))).flatMap fun ⟨_, h_4812⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.rec_array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.rec_array]⟩])))))))))
 | _ => []))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_rec_func (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REC i), .FUNC => ((if h_4813 : (i < (List.length (C.RECS))) then
((match h_4814 : (((C.RECS)[i]!) : subtype) with
 | (.SUB final_opt [] (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4815⟩ => (((interp_wf_heaptype_i ((.REC i))).flatMap fun ⟨_, h_4816⟩ => (((interp_wf_heaptype_i (.FUNC)).flatMap fun ⟨_, h_4817⟩ => (((interp_wf_subtype_i ((.SUB final_opt [] (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))))).flatMap fun ⟨_, h_4818⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.rec_func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.rec_func]⟩])))))))))
 | _ => []))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_none (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .NONE, v_heaptype => ((if h_4834 : (v_heaptype ≠ .BOT) then
(((interp_Heaptype_sub_iii (C) (v_heaptype) (.ANY)).flatMap fun ⟨_, h_4835⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4836⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4837⟩ => (((interp_wf_heaptype_i (.NONE)).flatMap fun ⟨_, h_4838⟩ => (((interp_wf_heaptype_i (.ANY)).flatMap fun ⟨_, h_4839⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4840⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.none <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.none]⟩])))))))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_nofunc (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .NOFUNC, v_heaptype => ((if h_4841 : (v_heaptype ≠ .BOT) then
(((interp_Heaptype_sub_iii (C) (v_heaptype) (.FUNC)).flatMap fun ⟨_, h_4842⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4843⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4844⟩ => (((interp_wf_heaptype_i (.NOFUNC)).flatMap fun ⟨_, h_4845⟩ => (((interp_wf_heaptype_i (.FUNC)).flatMap fun ⟨_, h_4846⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4847⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.nofunc <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.nofunc]⟩])))))))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_noexn (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .NOEXN, v_heaptype => ((if h_4848 : (v_heaptype ≠ .BOT) then
(((interp_Heaptype_sub_iii (C) (v_heaptype) (.EXN)).flatMap fun ⟨_, h_4849⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4850⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4851⟩ => (((interp_wf_heaptype_i (.NOEXN)).flatMap fun ⟨_, h_4852⟩ => (((interp_wf_heaptype_i (.EXN)).flatMap fun ⟨_, h_4853⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4854⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.noexn <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.noexn]⟩])))))))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_noextern (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .NOEXTERN, v_heaptype => ((if h_4855 : (v_heaptype ≠ .BOT) then
(((interp_Heaptype_sub_iii (C) (v_heaptype) (.EXTERN)).flatMap fun ⟨_, h_4856⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4857⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4858⟩ => (((interp_wf_heaptype_i (.NOEXTERN)).flatMap fun ⟨_, h_4859⟩ => (((interp_wf_heaptype_i (.EXTERN)).flatMap fun ⟨_, h_4860⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4861⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.noextern <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.noextern]⟩])))))))))))))
else []))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii_bot (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, .BOT, v_heaptype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4862⟩ => (((interp_wf_heaptype_i (v_heaptype)).flatMap fun ⟨_, h_4863⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4864⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_sub.bot <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_sub.bot]⟩])))))))
 | _, _, _ => []

partial def interp_Heaptype_sub_iii (a0 : context) (a1 : heaptype) (a2 : heaptype) : List {o : Unit // (Heaptype_sub a0 a1 a2)} :=
  interp_Heaptype_sub_iii_refl a0 a1 a2 ++
  interp_Heaptype_sub_iii_trans a0 a1 a2 ++
  interp_Heaptype_sub_iii_eq_any a0 a1 a2 ++
  interp_Heaptype_sub_iii_i31_eq a0 a1 a2 ++
  interp_Heaptype_sub_iii_struct_eq a0 a1 a2 ++
  interp_Heaptype_sub_iii_array_eq a0 a1 a2 ++
  interp_Heaptype_sub_iii_struct a0 a1 a2 ++
  interp_Heaptype_sub_iii_array a0 a1 a2 ++
  interp_Heaptype_sub_iii_func a0 a1 a2 ++
  interp_Heaptype_sub_iii_def a0 a1 a2 ++
  interp_Heaptype_sub_iii_typeidx_l a0 a1 a2 ++
  interp_Heaptype_sub_iii_typeidx_r a0 a1 a2 ++
  interp_Heaptype_sub_iii_rec_struct a0 a1 a2 ++
  interp_Heaptype_sub_iii_rec_array a0 a1 a2 ++
  interp_Heaptype_sub_iii_rec_func a0 a1 a2 ++
  interp_Heaptype_sub_iii_none a0 a1 a2 ++
  interp_Heaptype_sub_iii_nofunc a0 a1 a2 ++
  interp_Heaptype_sub_iii_noexn a0 a1 a2 ++
  interp_Heaptype_sub_iii_noextern a0 a1 a2 ++
  interp_Heaptype_sub_iii_bot a0 a1 a2

end

def interp_Reftype_sub_iii_nonnull (a0 : context) (a1 : reftype) (a2 : reftype) : List {o : Unit // (Reftype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REF none ht_1), (.REF none ht_2) => (((interp_Heaptype_sub_iii (C) (ht_1) (ht_2)).flatMap fun ⟨_, h_4677⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4678⟩ => (((interp_wf_reftype_i ((.REF none ht_1))).flatMap fun ⟨_, h_4679⟩ => (((interp_wf_reftype_i ((.REF none ht_2))).flatMap fun ⟨_, h_4680⟩ => ([⟨(), by subst_vars; first | (apply Reftype_sub.nonnull <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Reftype_sub.nonnull]⟩])))))))))
 | _, _, _ => []

def interp_Reftype_sub_iii_null (a0 : context) (a1 : reftype) (a2 : reftype) : List {o : Unit // (Reftype_sub a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REF (some .NULL) ht_1), (.REF (some .NULL) ht_2) => (((interp_Heaptype_sub_iii (C) (ht_1) (ht_2)).flatMap fun ⟨_, h_4681⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4682⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) ht_1))).flatMap fun ⟨_, h_4683⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) ht_2))).flatMap fun ⟨_, h_4684⟩ => ([⟨(), by subst_vars; first | (apply Reftype_sub.null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Reftype_sub.null]⟩])))))))))
 | _, _, _ => []

def interp_Reftype_sub_iii (a0 : context) (a1 : reftype) (a2 : reftype) : List {o : Unit // (Reftype_sub a0 a1 a2)} :=
  interp_Reftype_sub_iii_nonnull a0 a1 a2 ++
  interp_Reftype_sub_iii_null a0 a1 a2

def interp_Vectype_ok_ii_mk_Vectype_ok (a0 : context) (a1 : vectype) : List {o : Unit // (Vectype_ok a0 a1)} :=
  match a0, a1 with
 | C, v_vectype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5201⟩ => ([⟨(), by subst_vars; first | (apply Vectype_ok.mk_Vectype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Vectype_ok.mk_Vectype_ok]⟩])))

def interp_Vectype_ok_ii (a0 : context) (a1 : vectype) : List {o : Unit // (Vectype_ok a0 a1)} :=
  interp_Vectype_ok_ii_mk_Vectype_ok a0 a1

def interp_Numtype_ok_ii_mk_Numtype_ok (a0 : context) (a1 : numtype) : List {o : Unit // (Numtype_ok a0 a1)} :=
  match a0, a1 with
 | C, v_numtype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5200⟩ => ([⟨(), by subst_vars; first | (apply Numtype_ok.mk_Numtype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Numtype_ok.mk_Numtype_ok]⟩])))

def interp_Numtype_ok_ii (a0 : context) (a1 : numtype) : List {o : Unit // (Numtype_ok a0 a1)} :=
  interp_Numtype_ok_ii_mk_Numtype_ok a0 a1

def interp_Packtype_ok_ii_mk_Packtype_ok (a0 : context) (a1 : packtype) : List {o : Unit // (Packtype_ok a0 a1)} :=
  match a0, a1 with
 | C, v_packtype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5199⟩ => ([⟨(), by subst_vars; first | (apply Packtype_ok.mk_Packtype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Packtype_ok.mk_Packtype_ok]⟩])))

def interp_Packtype_ok_ii (a0 : context) (a1 : packtype) : List {o : Unit // (Packtype_ok a0 a1)} :=
  interp_Packtype_ok_ii_mk_Packtype_ok a0 a1

mutual

partial def interp_Reftype_ok_ii_mk_Reftype_ok (a0 : context) (a1 : reftype) : List {o : Unit // (Reftype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.REF (some .NULL) v_heaptype) => (((interp_Heaptype_ok_ii (C) (v_heaptype)).flatMap fun ⟨_, h_4674⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4675⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) v_heaptype))).flatMap fun ⟨_, h_4676⟩ => ([⟨(), by subst_vars; first | (apply Reftype_ok.mk_Reftype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Reftype_ok.mk_Reftype_ok]⟩])))))))
 | _, _ => []

partial def interp_Reftype_ok_ii (a0 : context) (a1 : reftype) : List {o : Unit // (Reftype_ok a0 a1)} :=
  interp_Reftype_ok_ii_mk_Reftype_ok a0 a1

partial def interp_Heaptype_ok_ii_abs (a0 : context) (a1 : heaptype) : List {o : Unit // (Heaptype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_370 => ((match interp_inv_heaptype_absheaptype y_370 with
 | some ⟨v_absheaptype, h_4737⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4738⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_ok.abs <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_ok.abs]⟩])))
 | none => []))

partial def interp_Heaptype_ok_ii_typeuse (a0 : context) (a1 : heaptype) : List {o : Unit // (Heaptype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_371 => ((match interp_inv_heaptype_typeuse y_371 with
 | some ⟨v_typeuse, h_4739⟩ => (((interp_Typeuse_ok_ii (C) (v_typeuse)).flatMap fun ⟨_, h_4740⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4741⟩ => (((interp_wf_typeuse_i (v_typeuse)).flatMap fun ⟨_, h_4742⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_ok.typeuse <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_ok.typeuse]⟩])))))))
 | none => []))

partial def interp_Heaptype_ok_ii_bot (a0 : context) (a1 : heaptype) : List {o : Unit // (Heaptype_ok a0 a1)} :=
  match a0, a1 with
 | C, .BOT => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4743⟩ => (((interp_wf_heaptype_i (.BOT)).flatMap fun ⟨_, h_4744⟩ => ([⟨(), by subst_vars; first | (apply Heaptype_ok.bot <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Heaptype_ok.bot]⟩])))))
 | _, _ => []

partial def interp_Heaptype_ok_ii (a0 : context) (a1 : heaptype) : List {o : Unit // (Heaptype_ok a0 a1)} :=
  interp_Heaptype_ok_ii_abs a0 a1 ++
  interp_Heaptype_ok_ii_typeuse a0 a1 ++
  interp_Heaptype_ok_ii_bot a0 a1

partial def interp_Typeuse_ok_ii_typeidx (a0 : context) (a1 : typeuse) : List {o : Unit // (Typeuse_ok a0 a1)} :=
  match a0, a1 with
 | C, (._IDX v_typeidx) => ((if h_4880 : ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) then
(((fun (dt : deftype) (h_4881 : (((C.TYPES)[(proj_uN_0 v_typeidx)]!) : deftype) = dt) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4882⟩ => (((interp_wf_deftype_i (dt)).flatMap fun ⟨_, h_4883⟩ => (((interp_wf_typeuse_i ((._IDX v_typeidx))).flatMap fun ⟨_, h_4884⟩ => ([⟨(), by subst_vars; first | (apply Typeuse_ok.typeidx <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Typeuse_ok.typeidx]⟩])))))))) (((C.TYPES)[(proj_uN_0 v_typeidx)]!) : deftype) rfl))
else []))
 | _, _ => []

partial def interp_Typeuse_ok_ii_rec (a0 : context) (a1 : typeuse) : List {o : Unit // (Typeuse_ok a0 a1)} :=
  match a0, a1 with
 | C, (.REC i) => ((if h_4885 : (i < (List.length (C.RECS))) then
(((fun (st : subtype) (h_4886 : (((C.RECS)[i]!) : subtype) = st) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4887⟩ => (((interp_wf_subtype_i (st)).flatMap fun ⟨_, h_4888⟩ => (((interp_wf_typeuse_i ((.REC i))).flatMap fun ⟨_, h_4889⟩ => ([⟨(), by subst_vars; first | (apply Typeuse_ok.rec_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Typeuse_ok.rec_]⟩])))))))) (((C.RECS)[i]!) : subtype) rfl))
else []))
 | _, _ => []

partial def interp_Typeuse_ok_ii_deftype (a0 : context) (a1 : typeuse) : List {o : Unit // (Typeuse_ok a0 a1)} :=
  match a0, a1 with
 | C, y_388 => ((match interp_inv_typeuse_deftype y_388 with
 | some ⟨v_deftype, h_4890⟩ => (((interp_Deftype_ok_ii (C) (v_deftype)).flatMap fun ⟨_, h_4891⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4892⟩ => (((interp_wf_deftype_i (v_deftype)).flatMap fun ⟨_, h_4893⟩ => ([⟨(), by subst_vars; first | (apply Typeuse_ok.deftype <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Typeuse_ok.deftype]⟩])))))))
 | none => []))

partial def interp_Typeuse_ok_ii (a0 : context) (a1 : typeuse) : List {o : Unit // (Typeuse_ok a0 a1)} :=
  interp_Typeuse_ok_ii_typeidx a0 a1 ++
  interp_Typeuse_ok_ii_rec a0 a1 ++
  interp_Typeuse_ok_ii_deftype a0 a1

partial def interp_Deftype_ok_ii_mk_Deftype_ok (a0 : context) (a1 : deftype) : List {o : Unit // (Deftype_ok a0 a1)} :=
  match a0, a1 with
 | C, (._DEF v_rectype i) => ((match h_5015 : (v_rectype : rectype) with
 | (.REC (.mk_list subtype_lst)) => (((interp_Rectype_ok2_iii (({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := subtype_lst } ++ C)) (v_rectype) ((.OK 0))).flatMap fun ⟨_, h_5016⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5018⟩ => (((interp_wf_deftype_i ((._DEF v_rectype i))).flatMap fun ⟨_, h_5020⟩ => (((interp_wf_context_i ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := subtype_lst })).flatMap fun ⟨_, h_5022⟩ => (((interp_wf_rectype_i ((.REC (.mk_list subtype_lst)))).flatMap fun ⟨_, h_5024⟩ => (((fun (v_n : Nat) (h_5026 : ((List.length subtype_lst) : Nat) = v_n) => ((if h_5027 : (i < v_n) then
([⟨(), by subst_vars; first | (apply Deftype_ok.mk_Deftype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Deftype_ok.mk_Deftype_ok]⟩])
else []))) ((List.length subtype_lst) : Nat) rfl))))))))))))))

partial def interp_Deftype_ok_ii (a0 : context) (a1 : deftype) : List {o : Unit // (Deftype_ok a0 a1)} :=
  interp_Deftype_ok_ii_mk_Deftype_ok a0 a1

partial def interp_Rectype_ok2_iii_empty (a0 : context) (a1 : rectype) (a2 : oktypenat) : List {o : Unit // (Rectype_ok2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REC (.mk_list [])), (.OK i) => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5068⟩ => (((interp_wf_rectype_i ((.REC (.mk_list [])))).flatMap fun ⟨_, h_5069⟩ => ([⟨(), by subst_vars; first | (apply Rectype_ok2.empty <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Rectype_ok2.empty]⟩])))))
 | _, _, _ => []

partial def interp_Rectype_ok2_iii_cons (a0 : context) (a1 : rectype) (a2 : oktypenat) : List {o : Unit // (Rectype_ok2 a0 a1 a2)} :=
  match a0, a1, a2 with
 | C, (.REC (.mk_list (subtype_1 :: subtype_lst))), (.OK i) => (((interp_Subtype_ok2_iii (C) (subtype_1) ((.OK i))).flatMap fun ⟨_, h_5070⟩ => (((interp_Rectype_ok2_iii (C) ((.REC (.mk_list subtype_lst))) ((.OK (i + 1)))).flatMap fun ⟨_, h_5071⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5072⟩ => (((interp_wf_rectype_i ((.REC (.mk_list (([subtype_1] : (List subtype)) ++ subtype_lst))))).flatMap fun ⟨_, h_5073⟩ => (((interp_wf_rectype_i ((.REC (.mk_list subtype_lst)))).flatMap fun ⟨_, h_5074⟩ => ([⟨(), by subst_vars; first | (apply Rectype_ok2.cons <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Rectype_ok2.cons]⟩])))))))))))
 | _, _, _ => []

partial def interp_Rectype_ok2_iii (a0 : context) (a1 : rectype) (a2 : oktypenat) : List {o : Unit // (Rectype_ok2 a0 a1 a2)} :=
  interp_Rectype_ok2_iii_empty a0 a1 a2 ++
  interp_Rectype_ok2_iii_cons a0 a1 a2

partial def interp_Subtype_ok2_iii (a0 : context) (a1 : subtype) (a2 : oktypenat) : List {o : Unit // (Subtype_ok2 a0 a1 a2)} :=
  []

partial def interp_Comptype_ok_ii_struct (a0 : context) (a1 : comptype) : List {o : Unit // (Comptype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.STRUCT (.mk_list fieldtype_lst)) => (((interp_allL (fun (v_fieldtype : fieldtype) => (interp_Fieldtype_ok_ii (C) (v_fieldtype))) fieldtype_lst).flatMap fun ⟨_, h_5159⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5160⟩ => (((interp_wf_comptype_i ((.STRUCT (.mk_list fieldtype_lst)))).flatMap fun ⟨_, h_5161⟩ => ([⟨(), by subst_vars; first | (apply Comptype_ok.struct <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Comptype_ok.struct]⟩])))))))
 | _, _ => []

partial def interp_Comptype_ok_ii_array (a0 : context) (a1 : comptype) : List {o : Unit // (Comptype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.ARRAY v_fieldtype) => (((interp_Fieldtype_ok_ii (C) (v_fieldtype)).flatMap fun ⟨_, h_5162⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5163⟩ => (((interp_wf_comptype_i ((.ARRAY v_fieldtype))).flatMap fun ⟨_, h_5164⟩ => ([⟨(), by subst_vars; first | (apply Comptype_ok.array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Comptype_ok.array]⟩])))))))
 | _, _ => []

partial def interp_Comptype_ok_ii_func (a0 : context) (a1 : comptype) : List {o : Unit // (Comptype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) => ((if h_5165 : ((List.length (List.map (fun (X_17416 : valtype) => X_17416) (proj_list_0 valtype (.mk_list t_1_lst)))) < (2 ^ 32)) then
((if h_5166 : ((List.length (List.map (fun (X_17417 : valtype) => X_17417) (proj_list_0 valtype (.mk_list t_2_lst)))) < (2 ^ 32)) then
(((interp_Resulttype_ok_ii (C) ((.mk_list t_1_lst))).flatMap fun ⟨_, h_5167⟩ => (((interp_Resulttype_ok_ii (C) ((.mk_list t_2_lst))).flatMap fun ⟨_, h_5168⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5169⟩ => (((interp_wf_comptype_i ((.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)))).flatMap fun ⟨_, h_5170⟩ => (((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype (.mk_list t_1_lst))).flatMap fun ⟨_, h_5171⟩ => (((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype (.mk_list t_2_lst))).flatMap fun ⟨_, h_5172⟩ => ([⟨(), by subst_vars; first | (apply Comptype_ok.func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Comptype_ok.func]⟩])))))))))))))
else []))
else []))
 | _, _ => []

partial def interp_Comptype_ok_ii (a0 : context) (a1 : comptype) : List {o : Unit // (Comptype_ok a0 a1)} :=
  interp_Comptype_ok_ii_struct a0 a1 ++
  interp_Comptype_ok_ii_array a0 a1 ++
  interp_Comptype_ok_ii_func a0 a1

partial def interp_Resulttype_ok_ii_mk_Resulttype_ok (a0 : context) (a1 : resulttype) : List {o : Unit // (Resulttype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.mk_list t_lst) => ((if h_5176 : ((List.length (List.map (fun (X_17415 : valtype) => X_17415) (proj_list_0 valtype (.mk_list t_lst)))) < (2 ^ 32)) then
(((interp_allL (fun (t : valtype) => (interp_Valtype_ok_ii (C) (t))) t_lst).flatMap fun ⟨_, h_5177⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5178⟩ => (((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype (.mk_list t_lst))).flatMap fun ⟨_, h_5179⟩ => ([⟨(), by subst_vars; first | (apply Resulttype_ok.mk_Resulttype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Resulttype_ok.mk_Resulttype_ok]⟩])))))))
else []))

partial def interp_Resulttype_ok_ii (a0 : context) (a1 : resulttype) : List {o : Unit // (Resulttype_ok a0 a1)} :=
  interp_Resulttype_ok_ii_mk_Resulttype_ok a0 a1

partial def interp_Valtype_ok_ii_num (a0 : context) (a1 : valtype) : List {o : Unit // (Valtype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_406 => ((match interp_inv_valtype_numtype y_406 with
 | some ⟨v_numtype, h_5187⟩ => (((interp_Numtype_ok_ii (C) (v_numtype)).flatMap fun ⟨_, h_5188⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5189⟩ => ([⟨(), by subst_vars; first | (apply Valtype_ok.num <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Valtype_ok.num]⟩])))))
 | none => []))

partial def interp_Valtype_ok_ii_vec (a0 : context) (a1 : valtype) : List {o : Unit // (Valtype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_407 => ((match interp_inv_valtype_vectype y_407 with
 | some ⟨v_vectype, h_5190⟩ => (((interp_Vectype_ok_ii (C) (v_vectype)).flatMap fun ⟨_, h_5191⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5192⟩ => ([⟨(), by subst_vars; first | (apply Valtype_ok.vec <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Valtype_ok.vec]⟩])))))
 | none => []))

partial def interp_Valtype_ok_ii_ref (a0 : context) (a1 : valtype) : List {o : Unit // (Valtype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_408 => ((match interp_inv_valtype_reftype y_408 with
 | some ⟨v_reftype, h_5193⟩ => (((interp_Reftype_ok_ii (C) (v_reftype)).flatMap fun ⟨_, h_5194⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5195⟩ => (((interp_wf_reftype_i (v_reftype)).flatMap fun ⟨_, h_5196⟩ => ([⟨(), by subst_vars; first | (apply Valtype_ok.ref <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Valtype_ok.ref]⟩])))))))
 | none => []))

partial def interp_Valtype_ok_ii_bot (a0 : context) (a1 : valtype) : List {o : Unit // (Valtype_ok a0 a1)} :=
  match a0, a1 with
 | C, .BOT => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5197⟩ => (((interp_wf_valtype_i (.BOT)).flatMap fun ⟨_, h_5198⟩ => ([⟨(), by subst_vars; first | (apply Valtype_ok.bot <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Valtype_ok.bot]⟩])))))
 | _, _ => []

partial def interp_Valtype_ok_ii (a0 : context) (a1 : valtype) : List {o : Unit // (Valtype_ok a0 a1)} :=
  interp_Valtype_ok_ii_num a0 a1 ++
  interp_Valtype_ok_ii_vec a0 a1 ++
  interp_Valtype_ok_ii_ref a0 a1 ++
  interp_Valtype_ok_ii_bot a0 a1

partial def interp_Fieldtype_ok_ii_mk_Fieldtype_ok (a0 : context) (a1 : fieldtype) : List {o : Unit // (Fieldtype_ok a0 a1)} :=
  match a0, a1 with
 | C, (.mk_fieldtype (some .MUT) v_storagetype) => (((interp_Storagetype_ok_ii (C) (v_storagetype)).flatMap fun ⟨_, h_5173⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5174⟩ => (((interp_wf_fieldtype_i ((.mk_fieldtype (some .MUT) v_storagetype))).flatMap fun ⟨_, h_5175⟩ => ([⟨(), by subst_vars; first | (apply Fieldtype_ok.mk_Fieldtype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Fieldtype_ok.mk_Fieldtype_ok]⟩])))))))
 | _, _ => []

partial def interp_Fieldtype_ok_ii (a0 : context) (a1 : fieldtype) : List {o : Unit // (Fieldtype_ok a0 a1)} :=
  interp_Fieldtype_ok_ii_mk_Fieldtype_ok a0 a1

partial def interp_Storagetype_ok_ii_val (a0 : context) (a1 : storagetype) : List {o : Unit // (Storagetype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_404 => ((match interp_inv_storagetype_valtype y_404 with
 | some ⟨v_valtype, h_5180⟩ => (((interp_Valtype_ok_ii (C) (v_valtype)).flatMap fun ⟨_, h_5181⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5182⟩ => (((interp_wf_valtype_i (v_valtype)).flatMap fun ⟨_, h_5183⟩ => ([⟨(), by subst_vars; first | (apply Storagetype_ok.val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Storagetype_ok.val]⟩])))))))
 | none => []))

partial def interp_Storagetype_ok_ii_pack (a0 : context) (a1 : storagetype) : List {o : Unit // (Storagetype_ok a0 a1)} :=
  match a0, a1 with
 | C, y_405 => ((match interp_inv_storagetype_packtype y_405 with
 | some ⟨v_packtype, h_5184⟩ => (((interp_Packtype_ok_ii (C) (v_packtype)).flatMap fun ⟨_, h_5185⟩ => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_5186⟩ => ([⟨(), by subst_vars; first | (apply Storagetype_ok.pack <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Storagetype_ok.pack]⟩])))))
 | none => []))

partial def interp_Storagetype_ok_ii (a0 : context) (a1 : storagetype) : List {o : Unit // (Storagetype_ok a0 a1)} :=
  interp_Storagetype_ok_ii_val a0 a1 ++
  interp_Storagetype_ok_ii_pack a0 a1

end

def interp_Reftype_ok_io_mk_Reftype_ok (a0 : context) : List {o : reftype // (Reftype_ok a0 o)} :=
  match a0 with
 | C => (((interp_Heaptype_ok_io (C)).flatMap fun ⟨o_369, h_4734⟩ => (match o_369 with
 | v_heaptype => (((interp_wf_context_i (C)).flatMap fun ⟨_, h_4735⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) v_heaptype))).flatMap fun ⟨_, h_4736⟩ => ([⟨(.REF (some .NULL) v_heaptype), by subst_vars; first | (apply Reftype_ok.mk_Reftype_ok <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Reftype_ok.mk_Reftype_ok]⟩]))))))))

def interp_Reftype_ok_io (a0 : context) : List {o : reftype // (Reftype_ok a0 o)} :=
  interp_Reftype_ok_io_mk_Reftype_ok a0

def interp_wf_structinst_i_structinst_case_ (a0 : structinst) : List {o : Unit // (wf_structinst a0)} :=
  match a0 with
 | { TYPE := var_0, FIELDS := var_1_lst } => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_4731⟩ => (((interp_allL (fun (var_1 : fieldval) => (interp_wf_fieldval_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4732⟩ => ([⟨(), by subst_vars; first | (apply wf_structinst.structinst_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_structinst.structinst_case_]⟩])))))

def interp_wf_structinst_i (a0 : structinst) : List {o : Unit // (wf_structinst a0)} :=
  interp_wf_structinst_i_structinst_case_ a0

def interp_wf_store_i_store_case_ (a0 : store) : List {o : Unit // (wf_store a0)} :=
  match a0 with
 | { TAGS := var_0_lst, GLOBALS := var_1_lst, MEMS := var_2_lst, TABLES := var_3_lst, FUNCS := var_4_lst, DATAS := var_5_lst, ELEMS := var_6_lst, STRUCTS := var_7_lst, ARRAYS := var_8_lst, EXNS := var_9_lst } => (((interp_allL (fun (var_0 : taginst) => (interp_wf_taginst_i (var_0))) var_0_lst).flatMap fun ⟨_, h_4616⟩ => (((interp_allL (fun (var_1 : globalinst) => (interp_wf_globalinst_i (var_1))) var_1_lst).flatMap fun ⟨_, h_4617⟩ => (((interp_allL (fun (var_2 : meminst) => (interp_wf_meminst_i (var_2))) var_2_lst).flatMap fun ⟨_, h_4618⟩ => (((interp_allL (fun (var_3 : tableinst) => (interp_wf_tableinst_i (var_3))) var_3_lst).flatMap fun ⟨_, h_4619⟩ => (((interp_allL (fun (var_4 : funcinst) => (interp_wf_funcinst_i (var_4))) var_4_lst).flatMap fun ⟨_, h_4620⟩ => (((interp_allL (fun (var_5 : datainst) => (interp_wf_datainst_i (var_5))) var_5_lst).flatMap fun ⟨_, h_4621⟩ => (((interp_allL (fun (var_6 : eleminst) => (interp_wf_eleminst_i (var_6))) var_6_lst).flatMap fun ⟨_, h_4622⟩ => (((interp_allL (fun (var_7 : structinst) => (interp_wf_structinst_i (var_7))) var_7_lst).flatMap fun ⟨_, h_4623⟩ => (((interp_allL (fun (var_8 : arrayinst) => (interp_wf_arrayinst_i (var_8))) var_8_lst).flatMap fun ⟨_, h_4624⟩ => (((interp_allL (fun (var_9 : exninst) => (interp_wf_exninst_i (var_9))) var_9_lst).flatMap fun ⟨_, h_4625⟩ => ([⟨(), by subst_vars; first | (apply wf_store.store_case_ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_store.store_case_]⟩])))))))))))))))))))))

def interp_wf_store_i (a0 : store) : List {o : Unit // (wf_store a0)} :=
  interp_wf_store_i_store_case_ a0

mutual

partial def interp_Ref_ok_iii_null (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, .REF_NULL_ADDR, (.REF (some .NULL) .BOT) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4481⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_4482⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) .BOT))).flatMap fun ⟨_, h_4483⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.null]⟩])))))))
 | _, _, _ => []

partial def interp_Ref_ok_iii_i31 (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_I31_NUM i), (.REF none .I31) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4484⟩ => (((interp_wf_ref_i ((.REF_I31_NUM i))).flatMap fun ⟨_, h_4485⟩ => (((interp_wf_reftype_i ((.REF none .I31))).flatMap fun ⟨_, h_4486⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.i31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.i31]⟩])))))))
 | _, _, _ => []

partial def interp_Ref_ok_iii_struct (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_STRUCT_ADDR a), (.REF none y_358) => ((if h_4487 : (a < (List.length (s.STRUCTS))) then
((match interp_inv_heaptype_deftype y_358 with
 | some ⟨dt, h_4488⟩ => ((if h_4489 : ((((s.STRUCTS)[a]!).TYPE) = dt) then
(((interp_wf_store_i (s)).flatMap fun ⟨_, h_4490⟩ => (((interp_wf_ref_i ((.REF_STRUCT_ADDR a))).flatMap fun ⟨_, h_4491⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4492⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.struct <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.struct]⟩])))))))
else []))
 | none => []))
else []))
 | _, _, _ => []

partial def interp_Ref_ok_iii_array (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_ARRAY_ADDR a), (.REF none y_359) => ((if h_4493 : (a < (List.length (s.ARRAYS))) then
((match interp_inv_heaptype_deftype y_359 with
 | some ⟨dt, h_4494⟩ => ((if h_4495 : ((((s.ARRAYS)[a]!).TYPE) = dt) then
(((interp_wf_store_i (s)).flatMap fun ⟨_, h_4496⟩ => (((interp_wf_ref_i ((.REF_ARRAY_ADDR a))).flatMap fun ⟨_, h_4497⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4498⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.array]⟩])))))))
else []))
 | none => []))
else []))
 | _, _, _ => []

partial def interp_Ref_ok_iii_func (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_FUNC_ADDR a), (.REF none y_360) => ((if h_4499 : (a < (List.length (s.FUNCS))) then
((match interp_inv_heaptype_deftype y_360 with
 | some ⟨dt, h_4500⟩ => ((if h_4501 : ((((s.FUNCS)[a]!).TYPE) = dt) then
(((interp_wf_store_i (s)).flatMap fun ⟨_, h_4502⟩ => (((interp_wf_ref_i ((.REF_FUNC_ADDR a))).flatMap fun ⟨_, h_4503⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4504⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.func]⟩])))))))
else []))
 | none => []))
else []))
 | _, _, _ => []

partial def interp_Ref_ok_iii_exn (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_EXN_ADDR a), (.REF none .EXN) => ((if h_4505 : (a < (List.length (s.EXNS))) then
(((fun (exn : exninst) (h_4506 : (((s.EXNS)[a]!) : exninst) = exn) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4507⟩ => (((interp_wf_exninst_i (exn)).flatMap fun ⟨_, h_4508⟩ => (((interp_wf_ref_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_4509⟩ => (((interp_wf_reftype_i ((.REF none .EXN))).flatMap fun ⟨_, h_4510⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.exn <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.exn]⟩])))))))))) (((s.EXNS)[a]!) : exninst) rfl))
else []))
 | _, _, _ => []

partial def interp_Ref_ok_iii_host (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_HOST_ADDR a), (.REF none .ANY) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4511⟩ => (((interp_wf_ref_i ((.REF_HOST_ADDR a))).flatMap fun ⟨_, h_4512⟩ => (((interp_wf_reftype_i ((.REF none .ANY))).flatMap fun ⟨_, h_4513⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.host <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.host]⟩])))))))
 | _, _, _ => []

partial def interp_Ref_ok_iii_extern (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, (.REF_EXTERN v_ref), (.REF none .EXTERN) => ((if h_4514 : (v_ref ≠ .REF_NULL_ADDR) then
(((interp_Ref_ok_iii (s) (v_ref) ((.REF none .ANY))).flatMap fun ⟨_, h_4515⟩ => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4516⟩ => (((interp_wf_ref_i ((.REF_EXTERN v_ref))).flatMap fun ⟨_, h_4517⟩ => (((interp_wf_reftype_i ((.REF none .EXTERN))).flatMap fun ⟨_, h_4518⟩ => (((interp_wf_reftype_i ((.REF none .ANY))).flatMap fun ⟨_, h_4519⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_4520⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.extern <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.extern]⟩])))))))))))))
else []))
 | _, _, _ => []

partial def interp_Ref_ok_iii_sub (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  match a0, a1, a2 with
 | s, v_ref, rt => (((interp_Ref_ok_iio (s) (v_ref)).flatMap fun ⟨o_361, h_4521⟩ => (match o_361 with
 | rt' => (((interp_Reftype_ok_ii ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] }) (rt)).flatMap fun ⟨_, h_4522⟩ => (((interp_Reftype_sub_iii ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] }) (rt') (rt)).flatMap fun ⟨_, h_4523⟩ => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4524⟩ => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_4525⟩ => (((interp_wf_reftype_i (rt)).flatMap fun ⟨_, h_4526⟩ => (((interp_wf_reftype_i (rt')).flatMap fun ⟨_, h_4527⟩ => (((interp_wf_context_i ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] })).flatMap fun ⟨_, h_4528⟩ => ([⟨(), by subst_vars; first | (apply Ref_ok.sub <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.sub]⟩]))))))))))))))))))

partial def interp_Ref_ok_iii (a0 : store) (a1 : ref) (a2 : reftype) : List {o : Unit // (Ref_ok a0 a1 a2)} :=
  interp_Ref_ok_iii_null a0 a1 a2 ++
  interp_Ref_ok_iii_i31 a0 a1 a2 ++
  interp_Ref_ok_iii_struct a0 a1 a2 ++
  interp_Ref_ok_iii_array a0 a1 a2 ++
  interp_Ref_ok_iii_func a0 a1 a2 ++
  interp_Ref_ok_iii_exn a0 a1 a2 ++
  interp_Ref_ok_iii_host a0 a1 a2 ++
  interp_Ref_ok_iii_extern a0 a1 a2 ++
  interp_Ref_ok_iii_sub a0 a1 a2

partial def interp_Ref_ok_iio_null (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, .REF_NULL_ADDR => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4629⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_4630⟩ => (((interp_wf_reftype_i ((.REF (some .NULL) .BOT))).flatMap fun ⟨_, h_4631⟩ => ([⟨(.REF (some .NULL) .BOT), by subst_vars; first | (apply Ref_ok.null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.null]⟩])))))))
 | _, _ => []

partial def interp_Ref_ok_iio_i31 (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_I31_NUM i) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4632⟩ => (((interp_wf_ref_i ((.REF_I31_NUM i))).flatMap fun ⟨_, h_4633⟩ => (((interp_wf_reftype_i ((.REF none .I31))).flatMap fun ⟨_, h_4634⟩ => ([⟨(.REF none .I31), by subst_vars; first | (apply Ref_ok.i31 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.i31]⟩])))))))
 | _, _ => []

partial def interp_Ref_ok_iio_struct (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_STRUCT_ADDR a) => ((if h_4635 : (a < (List.length (s.STRUCTS))) then
(((fun (dt : deftype) (h_4636 : ((((s.STRUCTS)[a]!).TYPE) : deftype) = dt) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4637⟩ => (((interp_wf_ref_i ((.REF_STRUCT_ADDR a))).flatMap fun ⟨_, h_4638⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4639⟩ => ([⟨(.REF none (heaptype_deftype dt)), by subst_vars; first | (apply Ref_ok.struct <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.struct]⟩])))))))) ((((s.STRUCTS)[a]!).TYPE) : deftype) rfl))
else []))
 | _, _ => []

partial def interp_Ref_ok_iio_array (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_ARRAY_ADDR a) => ((if h_4640 : (a < (List.length (s.ARRAYS))) then
(((fun (dt : deftype) (h_4641 : ((((s.ARRAYS)[a]!).TYPE) : deftype) = dt) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4642⟩ => (((interp_wf_ref_i ((.REF_ARRAY_ADDR a))).flatMap fun ⟨_, h_4643⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4644⟩ => ([⟨(.REF none (heaptype_deftype dt)), by subst_vars; first | (apply Ref_ok.array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.array]⟩])))))))) ((((s.ARRAYS)[a]!).TYPE) : deftype) rfl))
else []))
 | _, _ => []

partial def interp_Ref_ok_iio_func (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_FUNC_ADDR a) => ((if h_4645 : (a < (List.length (s.FUNCS))) then
(((fun (dt : deftype) (h_4646 : ((((s.FUNCS)[a]!).TYPE) : deftype) = dt) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4647⟩ => (((interp_wf_ref_i ((.REF_FUNC_ADDR a))).flatMap fun ⟨_, h_4648⟩ => (((interp_wf_reftype_i ((.REF none (heaptype_deftype dt)))).flatMap fun ⟨_, h_4649⟩ => ([⟨(.REF none (heaptype_deftype dt)), by subst_vars; first | (apply Ref_ok.func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.func]⟩])))))))) ((((s.FUNCS)[a]!).TYPE) : deftype) rfl))
else []))
 | _, _ => []

partial def interp_Ref_ok_iio_exn (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_EXN_ADDR a) => ((if h_4650 : (a < (List.length (s.EXNS))) then
(((fun (exn : exninst) (h_4651 : (((s.EXNS)[a]!) : exninst) = exn) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4652⟩ => (((interp_wf_exninst_i (exn)).flatMap fun ⟨_, h_4653⟩ => (((interp_wf_ref_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_4654⟩ => (((interp_wf_reftype_i ((.REF none .EXN))).flatMap fun ⟨_, h_4655⟩ => ([⟨(.REF none .EXN), by subst_vars; first | (apply Ref_ok.exn <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.exn]⟩])))))))))) (((s.EXNS)[a]!) : exninst) rfl))
else []))
 | _, _ => []

partial def interp_Ref_ok_iio_host (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_HOST_ADDR a) => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4656⟩ => (((interp_wf_ref_i ((.REF_HOST_ADDR a))).flatMap fun ⟨_, h_4657⟩ => (((interp_wf_reftype_i ((.REF none .ANY))).flatMap fun ⟨_, h_4658⟩ => ([⟨(.REF none .ANY), by subst_vars; first | (apply Ref_ok.host <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.host]⟩])))))))
 | _, _ => []

partial def interp_Ref_ok_iio_extern (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, (.REF_EXTERN v_ref) => ((if h_4659 : (v_ref ≠ .REF_NULL_ADDR) then
(((interp_Ref_ok_iii (s) (v_ref) ((.REF none .ANY))).flatMap fun ⟨_, h_4660⟩ => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4661⟩ => (((interp_wf_ref_i ((.REF_EXTERN v_ref))).flatMap fun ⟨_, h_4662⟩ => (((interp_wf_reftype_i ((.REF none .EXTERN))).flatMap fun ⟨_, h_4663⟩ => (((interp_wf_reftype_i ((.REF none .ANY))).flatMap fun ⟨_, h_4664⟩ => (((interp_wf_ref_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_4665⟩ => ([⟨(.REF none .EXTERN), by subst_vars; first | (apply Ref_ok.extern <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.extern]⟩])))))))))))))
else []))
 | _, _ => []

partial def interp_Ref_ok_iio_sub (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  match a0, a1 with
 | s, v_ref => (((interp_Ref_ok_iio (s) (v_ref)).flatMap fun ⟨o_366, h_4666⟩ => (match o_366 with
 | rt' => (((interp_Reftype_ok_io ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] })).flatMap fun ⟨o_367, h_4667⟩ => (match o_367 with
 | rt => (((interp_Reftype_sub_iii ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] }) (rt') (rt)).flatMap fun ⟨_, h_4668⟩ => (((interp_wf_store_i (s)).flatMap fun ⟨_, h_4669⟩ => (((interp_wf_ref_i (v_ref)).flatMap fun ⟨_, h_4670⟩ => (((interp_wf_reftype_i (rt)).flatMap fun ⟨_, h_4671⟩ => (((interp_wf_reftype_i (rt')).flatMap fun ⟨_, h_4672⟩ => (((interp_wf_context_i ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := [] })).flatMap fun ⟨_, h_4673⟩ => ([⟨rt, by subst_vars; first | (apply Ref_ok.sub <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Ref_ok.sub]⟩])))))))))))))))))))

partial def interp_Ref_ok_iio (a0 : store) (a1 : ref) : List {o : reftype // (Ref_ok a0 a1 o)} :=
  interp_Ref_ok_iio_null a0 a1 ++
  interp_Ref_ok_iio_i31 a0 a1 ++
  interp_Ref_ok_iio_struct a0 a1 ++
  interp_Ref_ok_iio_array a0 a1 ++
  interp_Ref_ok_iio_func a0 a1 ++
  interp_Ref_ok_iio_exn a0 a1 ++
  interp_Ref_ok_iio_host a0 a1 ++
  interp_Ref_ok_iio_extern a0 a1 ++
  interp_Ref_ok_iio_sub a0 a1

end

mutual

partial def interp_fun_subst_typevar_iiio_fun_subst_typevar_case_0 (a0 : typevar) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : (Option typeuse) // (fun_subst_typevar a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | tv, [], [] => ([⟨(some (typeuse_typevar tv)), by subst_vars; first | (apply fun_subst_typevar.fun_subst_typevar_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_typevar.fun_subst_typevar_case_0]⟩])
 | _, _, _ => []

partial def interp_fun_subst_typevar_iiio_fun_subst_typevar_case_1 (a0 : typevar) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : (Option typeuse) // (fun_subst_typevar a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | tv, (tv_1 :: tv'_lst), (tu_1 :: tu'_lst) => (((interp_fun_subst_typevar_iiio (tv) (tv'_lst) (tu'_lst)).flatMap fun ⟨o_392, h_4992⟩ => (match o_392 with
 | var_0 => ([⟨(Option.map (fun (iter_val_2 : typeuse) => (if (tv == tv_1) then tu_1 else iter_val_2)) var_0), by subst_vars; first | (apply fun_subst_typevar.fun_subst_typevar_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_typevar.fun_subst_typevar_case_1]⟩]))))
 | _, _, _ => []

partial def interp_fun_subst_typevar_iiio (a0 : typevar) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : (Option typeuse) // (fun_subst_typevar a0 a1 a2 o)} :=
  interp_fun_subst_typevar_iiio_fun_subst_typevar_case_0 a0 a1 a2 ++
  interp_fun_subst_typevar_iiio_fun_subst_typevar_case_1 a0 a1 a2

end

def interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_0 (a0 : heaptype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : heaptype // (fun_subst_heaptype a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.REC v_n), tv_lst, tu_lst => (((interp_fun_subst_typevar_iiio ((.REC v_n)) (tv_lst) (tu_lst)).flatMap fun ⟨o_384, h_4870⟩ => (match o_384 with
 | var_0 => ([⟨(heaptype_typeuse (Option.get! var_0)), by subst_vars; first | (apply fun_subst_heaptype.fun_subst_heaptype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_heaptype.fun_subst_heaptype_case_0]⟩]))))
 | _, _, _ => []

def interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_1 (a0 : heaptype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : heaptype // (fun_subst_heaptype a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (._IDX v_typeidx), tv_lst, tu_lst => (((interp_fun_subst_typevar_iiio ((._IDX v_typeidx)) (tv_lst) (tu_lst)).flatMap fun ⟨o_385, h_4871⟩ => (match o_385 with
 | var_0 => ([⟨(heaptype_typeuse (Option.get! var_0)), by subst_vars; first | (apply fun_subst_heaptype.fun_subst_heaptype_case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_heaptype.fun_subst_heaptype_case_1]⟩]))))
 | _, _, _ => []

def interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_2 (a0 : heaptype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : heaptype // (fun_subst_heaptype a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (._DEF v_rectype v_n), tv_lst, tu_lst => (((interp_fun_subst_deftype_iiio ((._DEF v_rectype v_n)) (tv_lst) (tu_lst)).flatMap fun ⟨o_386, h_4872⟩ => (match o_386 with
 | var_0 => ([⟨(heaptype_deftype var_0), by subst_vars; first | (apply fun_subst_heaptype.fun_subst_heaptype_case_2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_heaptype.fun_subst_heaptype_case_2]⟩]))))
 | _, _, _ => []

def interp_fun_subst_heaptype_iiio (a0 : heaptype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : heaptype // (fun_subst_heaptype a0 a1 a2 o)} :=
  interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_0 a0 a1 a2 ++
  interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_1 a0 a1 a2 ++
  interp_fun_subst_heaptype_iiio_fun_subst_heaptype_case_2 a0 a1 a2

def interp_fun_subst_reftype_iiio_fun_subst_reftype_case_0 (a0 : reftype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : reftype // (fun_subst_reftype a0 a1 a2 o)} :=
  match a0, a1, a2 with
 | (.REF null_opt ht), tv_lst, tu_lst => (((interp_fun_subst_heaptype_iiio (ht) (tv_lst) (tu_lst)).flatMap fun ⟨o_368, h_4733⟩ => (match o_368 with
 | var_0 => ([⟨(.REF null_opt var_0), by subst_vars; first | (apply fun_subst_reftype.fun_subst_reftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_reftype.fun_subst_reftype_case_0]⟩]))))

def interp_fun_subst_reftype_iiio (a0 : reftype) (a1 : (List typevar)) (a2 : (List typeuse)) : List {o : reftype // (fun_subst_reftype a0 a1 a2 o)} :=
  interp_fun_subst_reftype_iiio_fun_subst_reftype_case_0 a0 a1 a2

def interp_fun_subst_all_reftype_iio_fun_subst_all_reftype_case_0 (a0 : reftype) (a1 : (List typeuse)) : List {o : reftype // (fun_subst_all_reftype a0 a1 o)} :=
  match a0, a1 with
 | rt, tu_lst => (((fun (v_n : Nat) (h_4627 : ((List.length tu_lst) : Nat) = v_n) => (((interp_fun_subst_reftype_iiio (rt) (((List.range v_n).map (fun (i : Nat) => ((._IDX (.mk_uN i)) : typevar)))) (tu_lst)).flatMap fun ⟨o_365, h_4628⟩ => (match o_365 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_subst_all_reftype.fun_subst_all_reftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_subst_all_reftype.fun_subst_all_reftype_case_0]⟩]))))) ((List.length tu_lst) : Nat) rfl))

def interp_fun_subst_all_reftype_iio (a0 : reftype) (a1 : (List typeuse)) : List {o : reftype // (fun_subst_all_reftype a0 a1 o)} :=
  interp_fun_subst_all_reftype_iio_fun_subst_all_reftype_case_0 a0 a1

def interp_fun_inst_reftype_iio_fun_inst_reftype_case_0 (a0 : moduleinst) (a1 : reftype) : List {o : reftype // (fun_inst_reftype a0 a1 o)} :=
  match a0, a1 with
 | v_moduleinst, rt => (((interp_fun_subst_all_reftype_iio (rt) ((List.map (fun (iter_val_4 : deftype) => (typeuse_deftype iter_val_4)) (v_moduleinst.TYPES)))).flatMap fun ⟨o_357, h_4480⟩ => (match o_357 with
 | var_0 => ([⟨var_0, by subst_vars; first | (apply fun_inst_reftype.fun_inst_reftype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_inst_reftype.fun_inst_reftype_case_0]⟩]))))

def interp_fun_inst_reftype_iio (a0 : moduleinst) (a1 : reftype) : List {o : reftype // (fun_inst_reftype a0 a1 o)} :=
  interp_fun_inst_reftype_iio_fun_inst_reftype_case_0 a0 a1

def interp_wf_state_i_state_case_0 (a0 : state) : List {o : Unit // (wf_state a0)} :=
  match a0 with
 | (.mk_state v_store v_frame) => (((interp_wf_store_i (v_store)).flatMap fun ⟨_, h_4470⟩ => (((interp_wf_frame_i (v_frame)).flatMap fun ⟨_, h_4471⟩ => ([⟨(), by subst_vars; first | (apply wf_state.state_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_state.state_case_0]⟩])))))

def interp_wf_state_i (a0 : state) : List {o : Unit // (wf_state a0)} :=
  interp_wf_state_i_state_case_0 a0

def interp_wf_config_i_config_case_0 (a0 : config) : List {o : Unit // (wf_config a0)} :=
  match a0 with
 | (.mk_config v_state instr_lst) => (((interp_wf_state_i (v_state)).flatMap fun ⟨_, h_2645⟩ => (((interp_allL (fun (v_instr : instr) => (interp_wf_instr_i (v_instr))) instr_lst).flatMap fun ⟨_, h_2646⟩ => ([⟨(), by subst_vars; first | (apply wf_config.config_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_config.config_case_0]⟩])))))

def interp_wf_config_i (a0 : config) : List {o : Unit // (wf_config a0)} :=
  interp_wf_config_i_config_case_0 a0

def interp_wf_instrtype_i_instrtype_case_0 (a0 : instrtype) : List {o : Unit // (wf_instrtype a0)} :=
  match a0 with
 | (.mk_instrtype v_resulttype localidx_lst resulttype_0) => ((if h_4475 : ((List.length (List.map (fun (X_17411 : valtype) => X_17411) (proj_list_0 valtype v_resulttype))) < (2 ^ 32)) then
((if h_4476 : ((List.length (List.map (fun (X_17412 : valtype) => X_17412) (proj_list_0 valtype resulttype_0))) < (2 ^ 32)) then
(((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype v_resulttype)).flatMap fun ⟨_, h_4477⟩ => (((interp_allL (fun (v_localidx : localidx) => (interp_wf_uN_ii (32) (v_localidx))) localidx_lst).flatMap fun ⟨_, h_4478⟩ => (((interp_allL (fun (iter : valtype) => (interp_wf_valtype_i (iter))) (proj_list_0 valtype resulttype_0)).flatMap fun ⟨_, h_4479⟩ => ([⟨(), by subst_vars; first | (apply wf_instrtype.instrtype_case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [wf_instrtype.instrtype_case_0]⟩])))))))
else []))
else []))

def interp_wf_instrtype_i (a0 : instrtype) : List {o : Unit // (wf_instrtype a0)} :=
  interp_wf_instrtype_i_instrtype_case_0 a0

def interp_fun_blocktype__iio_fun_blocktype__case_0 (a0 : state) (a1 : blocktype) : List {o : instrtype // (fun_blocktype_ a0 a1 o)} :=
  match a0, a1 with
 | z, (._IDX x) => (((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_355, h_4472⟩ => (match o_355 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_356, h_4473⟩ => (match o_356 with
 | (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) => (((interp_wf_comptype_i ((.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)))).flatMap fun ⟨_, h_4474⟩ => ([⟨(.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)), by subst_vars; first | (apply fun_blocktype_.fun_blocktype__case_0 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_blocktype_.fun_blocktype__case_0]⟩])))
 | _ => []))))))
 | _, _ => []

def interp_fun_blocktype__iio_fun_blocktype__case_1 (a0 : state) (a1 : blocktype) : List {o : instrtype // (fun_blocktype_ a0 a1 o)} :=
  match a0, a1 with
 | z, (._RESULT t_opt) => ([⟨(.mk_instrtype (.mk_list []) [] (.mk_list (Option.toList t_opt))), by subst_vars; first | (apply fun_blocktype_.fun_blocktype__case_1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [fun_blocktype_.fun_blocktype__case_1]⟩])
 | _, _ => []

def interp_fun_blocktype__iio (a0 : state) (a1 : blocktype) : List {o : instrtype // (fun_blocktype_ a0 a1 o)} :=
  interp_fun_blocktype__iio_fun_blocktype__case_0 a0 a1 ++
  interp_fun_blocktype__iio_fun_blocktype__case_1 a0 a1

def interp_Step_read_io_block (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z y_188) => (((interp_splits y_188).flatMap fun ⟨(a_189, b_190), h_2647⟩ => ((match interp_invMap interp_inv_instr_val a_189 with
 | some ⟨val_lst, h_2648⟩ => (match h_2649 : List.length val_lst with
 | v_m => (if h_2650 : (v_m = (List.length val_lst)) then
((match b_190 with
 | [(.BLOCK bt instr_lst)] => (((interp_fun_blocktype__iio (z) (bt)).flatMap fun ⟨o_191, h_2652⟩ => (match o_191 with
 | var_0 => ((match h_2653 : (var_0 : instrtype) with
 | (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) => ((if h_2654 : (v_m = (List.length t_1_lst)) then
(((interp_wf_instrtype_i (var_0)).flatMap fun ⟨_, h_2655⟩ => (((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BLOCK bt instr_lst)] : (List instr)))))).flatMap fun ⟨_, h_2656⟩ => (((interp_wf_instrtype_i ((.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)))).flatMap fun ⟨_, h_2658⟩ => (((fun (v_n : Nat) (h_2660 : ((List.length t_2_lst) : Nat) = v_n) => (((interp_wf_instr_i ((.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst)))).flatMap fun ⟨_, h_2661⟩ => ((if h_2662 : ((List.length val_lst) = v_m) then
([⟨([(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))] : (List instr)), by subst_vars; first | (apply Step_read.block <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.block]⟩])
else []))))) ((List.length t_2_lst) : Nat) rfl))))))))
else []))
 | _ => [])))))
 | _ => []))
else []))
 | none => []))))

def interp_Step_read_io_loop (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z y_192) => (((interp_splits y_192).flatMap fun ⟨(a_193, b_194), h_2663⟩ => ((match interp_invMap interp_inv_instr_val a_193 with
 | some ⟨val_lst, h_2664⟩ => (match h_2665 : List.length val_lst with
 | v_m => (if h_2666 : (v_m = (List.length val_lst)) then
((match b_194 with
 | [(.LOOP bt instr_lst)] => (((interp_fun_blocktype__iio (z) (bt)).flatMap fun ⟨o_195, h_2668⟩ => (match o_195 with
 | var_0 => ((match h_2669 : (var_0 : instrtype) with
 | (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) => ((if h_2670 : (v_m = (List.length t_1_lst)) then
(((interp_wf_instrtype_i (var_0)).flatMap fun ⟨_, h_2671⟩ => (((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.LOOP bt instr_lst)] : (List instr)))))).flatMap fun ⟨_, h_2672⟩ => (((interp_wf_instr_i ((.LABEL_ v_m ([(.LOOP bt instr_lst)] : (List instr)) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst)))).flatMap fun ⟨_, h_2673⟩ => (((interp_wf_instrtype_i ((.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)))).flatMap fun ⟨_, h_2674⟩ => (((fun (v_n : Nat) (h_2675 : ((List.length t_2_lst) : Nat) = v_n) => ((if h_2676 : ((List.length val_lst) = v_m) then
([⟨([(.LABEL_ v_m ([(.LOOP bt instr_lst)] : (List instr)) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))] : (List instr)), by subst_vars; first | (apply Step_read.loop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.loop]⟩])
else []))) ((List.length t_2_lst) : Nat) rfl))))))))))
else []))
 | _ => [])))))
 | _ => []))
else []))
 | none => []))))

def interp_Step_read_io_br_on_cast_succeed (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config (.mk_state s f) [y_196, (.BR_ON_CAST l rt_1 rt_2)]) => ((match interp_inv_instr_ref y_196 with
 | some ⟨v_ref, h_2677⟩ => (((interp_fun_inst_reftype_iio ((f.MODULE)) (rt_2)).flatMap fun ⟨o_197, h_2678⟩ => (match o_197 with
 | var_0 => (((interp_Ref_ok_iii (s) (v_ref) (var_0)).flatMap fun ⟨_, h_2679⟩ => (((interp_wf_reftype_i (var_0)).flatMap fun ⟨_, h_2680⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s f) ([(instr_ref v_ref), (.BR_ON_CAST l rt_1 rt_2)] : (List instr))))).flatMap fun ⟨_, h_2681⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_2682⟩ => ([⟨([(instr_ref v_ref), (.BR l)] : (List instr)), by subst_vars; first | (apply Step_read.br_on_cast_succeed <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.br_on_cast_succeed]⟩]))))))))))))
 | none => []))
 | _ => []

def interp_Step_read_io_br_on_cast_fail_succeed (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config (.mk_state s f) [y_199, (.BR_ON_CAST_FAIL l rt_1 rt_2)]) => ((match interp_inv_instr_ref y_199 with
 | some ⟨v_ref, h_2685⟩ => (((interp_fun_inst_reftype_iio ((f.MODULE)) (rt_2)).flatMap fun ⟨o_200, h_2686⟩ => (match o_200 with
 | var_0 => (((interp_Ref_ok_iii (s) (v_ref) (var_0)).flatMap fun ⟨_, h_2687⟩ => (((interp_wf_reftype_i (var_0)).flatMap fun ⟨_, h_2688⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s f) ([(instr_ref v_ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)] : (List instr))))).flatMap fun ⟨_, h_2689⟩ => ([⟨([(instr_ref v_ref)] : (List instr)), by subst_vars; first | (apply Step_read.br_on_cast_fail_succeed <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.br_on_cast_fail_succeed]⟩]))))))))))
 | none => []))
 | _ => []

def interp_Step_read_io_call (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CALL x)]) => ((if h_2692 : ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) then
(((fun (a : addr) (h_2694 : ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) : addr) = a) => ((if h_2695 : (a < (List.length (fun_funcinst z))) then
(((interp_wf_moduleinst_i ((fun_moduleinst z))).flatMap fun ⟨_, h_2696⟩ => (((interp_wf_config_i ((.mk_config z ([(.CALL x)] : (List instr))))).flatMap fun ⟨_, h_2697⟩ => (((interp_wf_instr_i ((.REF_FUNC_ADDR a))).flatMap fun ⟨_, h_2698⟩ => (((interp_wf_instr_i ((.CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE))))).flatMap fun ⟨_, h_2699⟩ => ([⟨([(.REF_FUNC_ADDR a), (.CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE)))] : (List instr)), by subst_vars; first | (apply Step_read.call <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.call]⟩])))))))))
else []))) ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) : addr) rfl))
else []))
 | _ => []

def interp_Step_read_io_call_ref_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CALL_REF yy)]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CALL_REF yy)] : (List instr))))).flatMap fun ⟨_, h_2700⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2701⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.call_ref_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.call_ref_null]⟩])))))
 | _ => []

def interp_Step_read_io_return_call (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.RETURN_CALL x)]) => ((if h_2760 : ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) then
(((fun (a : addr) (h_2762 : ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) : addr) = a) => ((if h_2763 : (a < (List.length (fun_funcinst z))) then
(((interp_wf_moduleinst_i ((fun_moduleinst z))).flatMap fun ⟨_, h_2764⟩ => (((interp_wf_config_i ((.mk_config z ([(.RETURN_CALL x)] : (List instr))))).flatMap fun ⟨_, h_2765⟩ => (((interp_wf_instr_i ((.REF_FUNC_ADDR a))).flatMap fun ⟨_, h_2766⟩ => (((interp_wf_instr_i ((.RETURN_CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE))))).flatMap fun ⟨_, h_2767⟩ => ([⟨([(.REF_FUNC_ADDR a), (.RETURN_CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE)))] : (List instr)), by subst_vars; first | (apply Step_read.return_call <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.return_call]⟩])))))))))
else []))) ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) : addr) rfl))
else []))
 | _ => []

def interp_Step_read_io_return_call_ref_label (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.LABEL_ k instr'_lst y_206)]) => (((interp_splits y_206).flatMap fun ⟨(a_207, b_208), h_2768⟩ => (((interp_splits a_207).flatMap fun ⟨(a_209, b_210), h_2769⟩ => ((match interp_invMap interp_inv_instr_val a_209 with
 | some ⟨val_lst, h_2770⟩ => ((match b_210 with
 | [(.RETURN_CALL_REF yy)] => ((match b_208 with
 | instr_lst => (((interp_wf_config_i ((.mk_config z ([(.LABEL_ k instr'_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] : (List instr))) ++ instr_lst))] : (List instr))))).flatMap fun ⟨_, h_2773⟩ => (((interp_wf_instr_i ((.RETURN_CALL_REF yy))).flatMap fun ⟨_, h_2774⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] : (List instr))), by subst_vars; first | (apply Step_read.return_call_ref_label <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.return_call_ref_label]⟩])))))))
 | _ => []))
 | none => []))))))
 | _ => []

def interp_Step_read_io_return_call_ref_handler (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ k catch_lst y_211)]) => (((interp_splits y_211).flatMap fun ⟨(a_212, b_213), h_2775⟩ => (((interp_splits a_212).flatMap fun ⟨(a_214, b_215), h_2776⟩ => ((match interp_invMap interp_inv_instr_val a_214 with
 | some ⟨val_lst, h_2777⟩ => ((match b_215 with
 | [(.RETURN_CALL_REF yy)] => ((match b_213 with
 | instr_lst => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ k catch_lst (((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] : (List instr))) ++ instr_lst))] : (List instr))))).flatMap fun ⟨_, h_2780⟩ => (((interp_wf_instr_i ((.RETURN_CALL_REF yy))).flatMap fun ⟨_, h_2781⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] : (List instr))), by subst_vars; first | (apply Step_read.return_call_ref_handler <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.return_call_ref_handler]⟩])))))))
 | _ => []))
 | none => []))))))
 | _ => []

def interp_Step_read_io_return_call_ref_frame_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.FRAME_ k f y_216)]) => (((interp_splits y_216).flatMap fun ⟨(a_217, b_218), h_2782⟩ => (((interp_splits a_217).flatMap fun ⟨(a_219, b_220), h_2783⟩ => (((interp_splits a_219).flatMap fun ⟨(a_221, b_222), h_2784⟩ => ((if h_2785 : (b_222 = ([.REF_NULL_ADDR] : (List instr))) then
((match interp_invMap interp_inv_instr_val a_221 with
 | some ⟨val_lst, h_2786⟩ => ((match b_220 with
 | [(.RETURN_CALL_REF yy)] => ((match b_218 with
 | instr_lst => (((interp_wf_config_i ((.mk_config z ([(.FRAME_ k f ((((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.REF_NULL_ADDR] : (List instr))) ++ ([(.RETURN_CALL_REF yy)] : (List instr))) ++ instr_lst))] : (List instr))))).flatMap fun ⟨_, h_2789⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2790⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.return_call_ref_frame_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.return_call_ref_frame_null]⟩])))))))
 | _ => []))
 | none => []))
else []))))))))
 | _ => []

def interp_Step_read_io_return_call_ref_frame_addr (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.FRAME_ k f y_223)]) => (((interp_splits y_223).flatMap fun ⟨(a_224, b_225), h_2791⟩ => (((interp_splits a_224).flatMap fun ⟨(a_226, b_227), h_2792⟩ => (((interp_splits a_226).flatMap fun ⟨(a_228, b_229), h_2793⟩ => (((interp_splits a_228).flatMap fun ⟨(a_230, b_231), h_2794⟩ => ((match interp_invMap interp_inv_instr_val a_230 with
 | some ⟨val'_lst, h_2795⟩ => ((match interp_invMap interp_inv_instr_val b_231 with
 | some ⟨val_lst, h_2796⟩ => (match h_2797 : List.length val_lst with
 | v_n => (if h_2798 : (v_n = (List.length val_lst)) then
((match b_229 with
 | [(.REF_FUNC_ADDR a)] => ((if h_2800 : (a < (List.length (fun_funcinst z))) then
((match b_227 with
 | [(.RETURN_CALL_REF yy)] => ((match b_225 with
 | instr_lst => (((interp_Expand_io ((((fun_funcinst z)[a]!).TYPE))).flatMap fun ⟨o_232, h_2803⟩ => (match o_232 with
 | (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) => ((if h_2804 : (v_n = (List.length t_1_lst)) then
(((interp_allL (fun (iter : funcinst) => (interp_wf_funcinst_i (iter))) (fun_funcinst z)).flatMap fun ⟨_, h_2805⟩ => (((interp_wf_config_i ((.mk_config z ([(.FRAME_ k f (((((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)) ++ ([(.REF_FUNC_ADDR a)] : (List instr))) ++ ([(.RETURN_CALL_REF yy)] : (List instr))) ++ instr_lst))] : (List instr))))).flatMap fun ⟨_, h_2806⟩ => (((interp_wf_instr_i ((.REF_FUNC_ADDR a))).flatMap fun ⟨_, h_2807⟩ => (((interp_wf_instr_i ((.CALL_REF yy))).flatMap fun ⟨_, h_2808⟩ => (((interp_wf_comptype_i ((.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)))).flatMap fun ⟨_, h_2809⟩ => (((fun (v_m : Nat) (h_2810 : ((List.length t_2_lst) : Nat) = v_m) => ((if h_2811 : ((List.length val_lst) = v_n) then
([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.REF_FUNC_ADDR a), (.CALL_REF yy)] : (List instr))), by subst_vars; first | (apply Step_read.return_call_ref_frame_addr <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.return_call_ref_frame_addr]⟩])
else []))) ((List.length t_2_lst) : Nat) rfl))))))))))))
else []))
 | _ => [])))))
 | _ => []))
else []))
 | _ => []))
else []))
 | none => []))
 | none => []))))))))))
 | _ => []

def interp_Step_read_io_throw_ref_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, .THROW_REF]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, .THROW_REF] : (List instr))))).flatMap fun ⟨_, h_2812⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2813⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_null]⟩])))))
 | _ => []

def interp_Step_read_io_throw_ref_instrs (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z y_233) => (((interp_splits y_233).flatMap fun ⟨(a_234, b_235), h_2814⟩ => ((match interp_invMap interp_inv_instr_val a_234 with
 | some ⟨val_lst, h_2815⟩ => (((interp_splits b_235).flatMap fun ⟨(a_236, b_237), h_2816⟩ => ((match a_236 with
 | [(.REF_EXN_ADDR a)] => (((interp_splits b_237).flatMap fun ⟨(a_238, b_239), h_2818⟩ => ((if h_2819 : (a_238 = ([.THROW_REF] : (List instr))) then
((match b_239 with
 | instr_lst => ((if h_2821 : ((val_lst ≠ []) ∨ (instr_lst ≠ [])) then
(((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (([(.REF_EXN_ADDR a)] : (List instr)) ++ (([.THROW_REF] : (List instr)) ++ instr_lst)))))).flatMap fun ⟨_, h_2822⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2823⟩ => (((interp_wf_instr_i (.THROW_REF)).flatMap fun ⟨_, h_2824⟩ => ([⟨([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_instrs <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_instrs]⟩])))))))
else []))))
else []))))
 | _ => []))))
 | none => []))))

def interp_Step_read_io_throw_ref_label (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.LABEL_ v_n instr'_lst [(.REF_EXN_ADDR a), .THROW_REF])]) => (((interp_wf_config_i ((.mk_config z ([(.LABEL_ v_n instr'_lst ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2825⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2826⟩ => (((interp_wf_instr_i (.THROW_REF)).flatMap fun ⟨_, h_2827⟩ => ([⟨([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_label <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_label]⟩])))))))
 | _ => []

def interp_Step_read_io_throw_ref_frame (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.FRAME_ v_n f [(.REF_EXN_ADDR a), .THROW_REF])]) => (((interp_wf_config_i ((.mk_config z ([(.FRAME_ v_n f ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2828⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2829⟩ => (((interp_wf_instr_i (.THROW_REF)).flatMap fun ⟨_, h_2830⟩ => ([⟨([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_frame <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_frame]⟩])))))))
 | _ => []

def interp_Step_read_io_throw_ref_handler_empty (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n [] [(.REF_EXN_ADDR a), .THROW_REF])]) => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n [] ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2831⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2832⟩ => (((interp_wf_instr_i (.THROW_REF)).flatMap fun ⟨_, h_2833⟩ => ([⟨([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_handler_empty <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_handler_empty]⟩])))))))
 | _ => []

def interp_Step_read_io_throw_ref_handler_catch (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n ((.CATCH x l) :: catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) => ((if h_2834 : (a < (List.length (fun_exninst z))) then
((if h_2835 : ((proj_uN_0 x) < (List.length (fun_tagaddr z))) then
((if h_2836 : ((((fun_exninst z)[a]!).TAG) = ((fun_tagaddr z)[(proj_uN_0 x)]!)) then
(((fun (val_lst : (List val)) (h_2837 : ((((fun_exninst z)[a]!).FIELDS) : (List val)) = val_lst) => (((interp_allL (fun (v_val : val) => (interp_wf_val_i (v_val))) val_lst).flatMap fun ⟨_, h_2838⟩ => (((interp_allL (fun (iter : exninst) => (interp_wf_exninst_i (iter))) (fun_exninst z)).flatMap fun ⟨_, h_2839⟩ => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n (([(.CATCH x l)] : (List «catch»)) ++ catch'_lst) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2840⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_2841⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] : (List instr))), by subst_vars; first | (apply Step_read.throw_ref_handler_catch <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_handler_catch]⟩])))))))))) ((((fun_exninst z)[a]!).FIELDS) : (List val)) rfl))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_throw_ref_handler_catch_ref (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n ((.CATCH_REF x l) :: catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) => ((if h_2842 : (a < (List.length (fun_exninst z))) then
((if h_2843 : ((proj_uN_0 x) < (List.length (fun_tagaddr z))) then
((if h_2844 : ((((fun_exninst z)[a]!).TAG) = ((fun_tagaddr z)[(proj_uN_0 x)]!)) then
(((fun (val_lst : (List val)) (h_2845 : ((((fun_exninst z)[a]!).FIELDS) : (List val)) = val_lst) => (((interp_allL (fun (v_val : val) => (interp_wf_val_i (v_val))) val_lst).flatMap fun ⟨_, h_2846⟩ => (((interp_allL (fun (iter : exninst) => (interp_wf_exninst_i (iter))) (fun_exninst z)).flatMap fun ⟨_, h_2847⟩ => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n (([(.CATCH_REF x l)] : (List «catch»)) ++ catch'_lst) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2848⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2849⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_2850⟩ => ([⟨((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.REF_EXN_ADDR a), (.BR l)] : (List instr))), by subst_vars; first | (apply Step_read.throw_ref_handler_catch_ref <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_handler_catch_ref]⟩])))))))))))) ((((fun_exninst z)[a]!).FIELDS) : (List val)) rfl))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_throw_ref_handler_catch_all (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n ((.CATCH_ALL l) :: catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n (([(.CATCH_ALL l)] : (List «catch»)) ++ catch'_lst) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2851⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_2852⟩ => ([⟨([(.BR l)] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_handler_catch_all <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_handler_catch_all]⟩])))))
 | _ => []

def interp_Step_read_io_throw_ref_handler_catch_all_ref (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n ((.CATCH_ALL_REF l) :: catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n (([(.CATCH_ALL_REF l)] : (List «catch»)) ++ catch'_lst) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr)))] : (List instr))))).flatMap fun ⟨_, h_2853⟩ => (((interp_wf_instr_i ((.REF_EXN_ADDR a))).flatMap fun ⟨_, h_2854⟩ => (((interp_wf_instr_i ((.BR l))).flatMap fun ⟨_, h_2855⟩ => ([⟨([(.REF_EXN_ADDR a), (.BR l)] : (List instr)), by subst_vars; first | (apply Step_read.throw_ref_handler_catch_all_ref <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.throw_ref_handler_catch_all_ref]⟩])))))))
 | _ => []

def interp_Step_read_io_try_table (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z y_240) => (((interp_splits y_240).flatMap fun ⟨(a_241, b_242), h_2857⟩ => ((match interp_invMap interp_inv_instr_val a_241 with
 | some ⟨val_lst, h_2858⟩ => (match h_2859 : List.length val_lst with
 | v_m => (if h_2860 : (v_m = (List.length val_lst)) then
((match b_242 with
 | [(.TRY_TABLE bt (.mk_list catch_lst) instr_lst)] => (((interp_fun_blocktype__iio (z) (bt)).flatMap fun ⟨o_243, h_2862⟩ => (match o_243 with
 | var_0 => ((match h_2863 : (var_0 : instrtype) with
 | (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) => ((if h_2864 : (v_m = (List.length t_1_lst)) then
(((interp_wf_instrtype_i (var_0)).flatMap fun ⟨_, h_2865⟩ => (((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.TRY_TABLE bt (.mk_list catch_lst) instr_lst)] : (List instr)))))).flatMap fun ⟨_, h_2866⟩ => (((interp_wf_instrtype_i ((.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)))).flatMap fun ⟨_, h_2868⟩ => (((fun (v_n : Nat) (h_2870 : ((List.length t_2_lst) : Nat) = v_n) => (((interp_wf_instr_i ((.HANDLER_ v_n catch_lst ([(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))] : (List instr))))).flatMap fun ⟨_, h_2871⟩ => ((if h_2872 : ((List.length val_lst) = v_m) then
([⟨([(.HANDLER_ v_n catch_lst ([(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))] : (List instr)))] : (List instr)), by subst_vars; first | (apply Step_read.try_table <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.try_table]⟩])
else []))))) ((List.length t_2_lst) : Nat) rfl))))))))
else []))
 | _ => [])))))
 | _ => []))
else []))
 | none => []))))

def interp_Step_read_io_local_get (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.LOCAL_GET x)]) => ((match h_2873 : ((fun_local z x) : (Option val)) with
 | (some v_val) => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_2874⟩ => (((interp_allL (fun (iter : val) => (interp_wf_val_i (iter))) (Option.toList (fun_local z x))).flatMap fun ⟨_, h_2875⟩ => (((interp_wf_config_i ((.mk_config z ([(.LOCAL_GET x)] : (List instr))))).flatMap fun ⟨_, h_2876⟩ => ((if h_2877 : ((proj_uN_0 x) < (List.length ((fof z).LOCALS))) then
([⟨([(instr_val v_val)] : (List instr)), by subst_vars; first | (apply Step_read.local_get <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.local_get]⟩])
else []))))))))
 | _ => []))
 | _ => []

def interp_Step_read_io_global_get (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.GLOBAL_GET x)]) => (((fun (v_val : val) (h_2878 : (((fun_global z x).VALUE) : val) = v_val) => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_2879⟩ => (((interp_wf_globalinst_i ((fun_global z x))).flatMap fun ⟨_, h_2880⟩ => (((interp_wf_config_i ((.mk_config z ([(.GLOBAL_GET x)] : (List instr))))).flatMap fun ⟨_, h_2881⟩ => ((if h_2882 : (((((fof z).MODULE).GLOBALS)[(proj_uN_0 x)]!) < (List.length ((sof z).GLOBALS))) then
((if h_2883 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).GLOBALS))) then
([⟨([(instr_val v_val)] : (List instr)), by subst_vars; first | (apply Step_read.global_get <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.global_get]⟩])
else []))
else []))))))))) (((fun_global z x).VALUE) : val) rfl))
 | _ => []

def interp_Step_read_io_table_get_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_244 i), (.TABLE_GET x)]) => ((if h_2884 : ((proj_num__0 i) ≠ none) then
((if h_2885 : ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) then
((match interp_inv_numtype_addrtype y_244 with
 | some ⟨«at», h_2886⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_2887⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.TABLE_GET x)] : (List instr))))).flatMap fun ⟨_, h_2888⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2889⟩ => ((if h_2890 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2891 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.table_get_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_get_oob]⟩])
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_get_val (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_245 i), (.TABLE_GET x)]) => ((if h_2892 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) then
((if h_2893 : ((proj_num__0 i) ≠ none) then
((match interp_inv_numtype_addrtype y_245 with
 | some ⟨«at», h_2894⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_2895⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.TABLE_GET x)] : (List instr))))).flatMap fun ⟨_, h_2896⟩ => ((if h_2897 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2898 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([(instr_ref (((fun_table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))] : (List instr)), by subst_vars; first | (apply Step_read.table_get_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_get_val]⟩])
else []))
else []))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_size (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.TABLE_SIZE x)]) => (((fun (v_n : n) (h_2899 : ((List.length ((fun_table z x).REFS)) : n) = v_n) => ((match h_2900 : (((fun_table z x).TYPE) : tabletype) with
 | (.mk_tabletype «at» lim rt) => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_2901⟩ => (((interp_wf_config_i ((.mk_config z ([(.TABLE_SIZE x)] : (List instr))))).flatMap fun ⟨_, h_2902⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))))).flatMap fun ⟨_, h_2903⟩ => (((interp_wf_tabletype_i ((.mk_tabletype «at» lim rt))).flatMap fun ⟨_, h_2904⟩ => ((if h_2905 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2906 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n)))] : (List instr)), by subst_vars; first | (apply Step_read.table_size <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_size]⟩])
else []))
else []))))))))))))) ((List.length ((fun_table z x).REFS)) : n) rfl))
 | _ => []

def interp_Step_read_io_table_fill_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_246 i), y_247, (.CONST y_248 (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) => ((if h_2907 : (y_246 = (numtype_addrtype «at»)) then
((if h_2908 : (y_248 = (numtype_addrtype «at»)) then
((if h_2909 : ((proj_num__0 i) ≠ none) then
((if h_2910 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) then
((match interp_inv_instr_val y_247 with
 | some ⟨v_val, h_2911⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_2912⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)] : (List instr))))).flatMap fun ⟨_, h_2913⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2914⟩ => ((if h_2915 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2916 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.table_fill_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_fill_oob]⟩])
else []))
else []))))))))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_fill_zero (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_249 i), y_250, (.CONST y_251 (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) => ((if h_2917 : (y_249 = (numtype_addrtype «at»)) then
((if h_2918 : (y_251 = (numtype_addrtype «at»)) then
((if h_2919 : ((proj_num__0 i) ≠ none) then
((if h_2920 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) then
((if h_2921 : (v_n = 0) then
((match interp_inv_instr_val y_250 with
 | some ⟨v_val, h_2922⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)] : (List instr))))).flatMap fun ⟨_, h_2923⟩ => ((if h_2924 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2925 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨[], by subst_vars; first | (apply Step_read.table_fill_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_fill_zero]⟩])
else []))
else []))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_fill_succ (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_252 i), y_253, (.CONST y_254 (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) => ((if h_2926 : (y_252 = (numtype_addrtype «at»)) then
((if h_2927 : (y_254 = (numtype_addrtype «at»)) then
((if h_2928 : ((proj_num__0 i) ≠ none) then
((if h_2929 : (v_n ≠ 0) then
((if h_2930 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) then
((match interp_inv_instr_val y_253 with
 | some ⟨v_val, h_2931⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)] : (List instr))))).flatMap fun ⟨_, h_2932⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») i))).flatMap fun ⟨_, h_2933⟩ => (((interp_wf_instr_i ((.TABLE_SET x))).flatMap fun ⟨_, h_2934⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))))).flatMap fun ⟨_, h_2935⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_2936⟩ => (((interp_wf_instr_i ((.TABLE_FILL x))).flatMap fun ⟨_, h_2937⟩ => ((if h_2938 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_2939 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2940 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.TABLE_SET x), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.TABLE_FILL x)] : (List instr)), by subst_vars; first | (apply Step_read.table_fill_succ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_fill_succ]⟩])
else []))
else []))
else []))))))))))))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_copy_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_255 i_1), (.CONST y_256 i_2), (.CONST y_257 (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x_1 x_2)]) => ((if h_2941 : (y_257 = (numtype_addrtype at')) then
((if h_2942 : ((proj_num__0 i_1) ≠ none) then
((if h_2943 : ((proj_num__0 i_2) ≠ none) then
((if h_2944 : ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_table z x_1).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_table z x_2).REFS)))) then
((match interp_inv_numtype_addrtype y_255 with
 | some ⟨at_1, h_2945⟩ => ((match interp_inv_numtype_addrtype y_256 with
 | some ⟨at_2, h_2946⟩ => (((interp_wf_tableinst_i ((fun_table z x_1))).flatMap fun ⟨_, h_2947⟩ => (((interp_wf_tableinst_i ((fun_table z x_2))).flatMap fun ⟨_, h_2948⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_2949⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2950⟩ => ((if h_2951 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x_1)]!) < (List.length ((sof z).TABLES))) then
((if h_2952 : ((proj_uN_0 x_1) < (List.length (((fof z).MODULE).TABLES))) then
((if h_2953 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x_2)]!) < (List.length ((sof z).TABLES))) then
((if h_2954 : ((proj_uN_0 x_2) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.table_copy_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_copy_oob]⟩])
else []))
else []))
else []))
else []))))))))))
 | none => []))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_init_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_267 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) => ((if h_2973 : ((proj_num__0 i) ≠ none) then
((if h_2974 : ((proj_num__0 j) ≠ none) then
((if h_2975 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS)))) then
((match interp_inv_numtype_addrtype y_267 with
 | some ⟨«at», h_2976⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_2977⟩ => (((interp_wf_eleminst_i ((fun_elem z y))).flatMap fun ⟨_, h_2978⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_2979⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_2980⟩ => ((if h_2981 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2982 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
((if h_2983 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_2984 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.table_init_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_init_oob]⟩])
else []))
else []))
else []))
else []))))))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_init_zero (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_268 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) => ((if h_2985 : ((proj_num__0 i) ≠ none) then
((if h_2986 : ((proj_num__0 j) ≠ none) then
((if h_2987 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) then
((if h_2988 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS))) then
((if h_2989 : (v_n = 0) then
((match interp_inv_numtype_addrtype y_268 with
 | some ⟨«at», h_2990⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_2991⟩ => ((if h_2992 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_2993 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
((if h_2994 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_2995 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨[], by subst_vars; first | (apply Step_read.table_init_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_init_zero]⟩])
else []))
else []))
else []))
else []))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_table_init_succ (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_269 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) => ((if h_2996 : ((proj_uN_0 (Option.get! (proj_num__0 j))) < (List.length ((fun_elem z y).REFS))) then
((if h_2997 : ((proj_num__0 j) ≠ none) then
((if h_2998 : ((proj_num__0 i) ≠ none) then
((if h_2999 : (v_n ≠ 0) then
((if h_3000 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) then
((if h_3001 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS))) then
((match interp_inv_numtype_addrtype y_269 with
 | some ⟨«at», h_3002⟩ => (((interp_wf_eleminst_i ((fun_elem z y))).flatMap fun ⟨_, h_3003⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_3004⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») i))).flatMap fun ⟨_, h_3005⟩ => (((interp_wf_instr_i ((.TABLE_SET x))).flatMap fun ⟨_, h_3006⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))))).flatMap fun ⟨_, h_3007⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))))).flatMap fun ⟨_, h_3008⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3009⟩ => (((interp_wf_instr_i ((.TABLE_INIT x y))).flatMap fun ⟨_, h_3010⟩ => ((if h_3011 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_3012 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
((if h_3013 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_3014 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_3015 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨([(.CONST (numtype_addrtype «at») i), (instr_ref (((fun_elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!)), (.TABLE_SET x), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.TABLE_INIT x y)] : (List instr)), by subst_vars; first | (apply Step_read.table_init_succ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.table_init_succ]⟩])
else []))
else []))
else []))
else []))
else []))))))))))))))))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_load_num_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_270 i), (.LOAD nt none x ao)]) => ((if h_3016 : ((proj_num__0 i) ≠ none) then
((if h_3017 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_270 with
 | some ⟨«at», h_3018⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3019⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.LOAD nt none x ao)] : (List instr))))).flatMap fun ⟨_, h_3020⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3021⟩ => ((if h_3022 : ((((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3023 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3024 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3025 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.load_num_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.load_num_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_load_pack_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_272 i), (.LOAD y_273 (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) x ao)]) => ((if h_3057 : (y_273 = (numtype_addrtype v_Inn)) then
((if h_3058 : ((proj_num__0 i) ≠ none) then
((if h_3059 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_272 with
 | some ⟨«at», h_3060⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3061⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.LOAD (numtype_addrtype v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) x ao)] : (List instr))))).flatMap fun ⟨_, h_3062⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3063⟩ => ((if h_3064 : ((((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3065 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3066 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3067 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.load_pack_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.load_pack_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_vload_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_276 i), (.VLOAD .V128 none x ao)]) => ((if h_3100 : ((proj_num__0 i) ≠ none) then
((if h_3101 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_276 with
 | some ⟨«at», h_3102⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3103⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 none x ao)] : (List instr))))).flatMap fun ⟨_, h_3104⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3105⟩ => ((if h_3106 : ((((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3107 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3108 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3109 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.vload_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.vload_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_vload_pack_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_278 i), (.VLOAD .V128 (some (.SHAPEX_ (.mk_sz v_M) v_K v_sx)) x ao)]) => ((if h_3141 : ((proj_num__0 i) ≠ none) then
((if h_3142 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (v_M * v_K))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_278 with
 | some ⟨«at», h_3143⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3144⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SHAPEX_ (.mk_sz v_M) v_K v_sx)) x ao)] : (List instr))))).flatMap fun ⟨_, h_3145⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3146⟩ => ((if h_3147 : ((((Rat.ofInt (Int.ofNat (v_M * v_K))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (v_M * v_K))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3148 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3149 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3150 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.vload_pack_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.vload_pack_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_vload_splat_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_280 i), (.VLOAD .V128 (some (.SPLAT (.mk_sz v_N))) x ao)]) => ((if h_3208 : ((proj_num__0 i) ≠ none) then
((if h_3209 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_280 with
 | some ⟨«at», h_3210⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3211⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SPLAT (.mk_sz v_N))) x ao)] : (List instr))))).flatMap fun ⟨_, h_3212⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3213⟩ => ((if h_3214 : ((((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3215 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3216 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3217 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.vload_splat_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.vload_splat_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_vload_zero_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_282 i), (.VLOAD .V128 (some (.ZERO (.mk_sz v_N))) x ao)]) => ((if h_3302 : ((proj_num__0 i) ≠ none) then
((if h_3303 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_282 with
 | some ⟨«at», h_3304⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3305⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.ZERO (.mk_sz v_N))) x ao)] : (List instr))))).flatMap fun ⟨_, h_3306⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3307⟩ => ((if h_3308 : ((((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3309 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3310 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3311 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.vload_zero_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.vload_zero_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_vload_lane_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_284 i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) x ao j)]) => ((if h_3366 : ((proj_num__0 i) ≠ none) then
((if h_3367 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_284 with
 | some ⟨«at», h_3368⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3369⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) x ao j)] : (List instr))))).flatMap fun ⟨_, h_3370⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3371⟩ => ((if h_3372 : ((((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3373 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3374 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3375 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.vload_lane_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.vload_lane_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_fill_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_286 i), y_287, (.CONST y_288 (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) => ((if h_3496 : (y_286 = (numtype_addrtype «at»)) then
((if h_3497 : (y_288 = (numtype_addrtype «at»)) then
((if h_3498 : ((proj_num__0 i) ≠ none) then
((if h_3499 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_instr_val y_287 with
 | some ⟨v_val, h_3500⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3501⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)] : (List instr))))).flatMap fun ⟨_, h_3502⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3503⟩ => ((if h_3504 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3505 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.memory_fill_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_fill_oob]⟩])
else []))
else []))))))))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_fill_zero (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_289 i), y_290, (.CONST y_291 (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) => ((if h_3506 : (y_289 = (numtype_addrtype «at»)) then
((if h_3507 : (y_291 = (numtype_addrtype «at»)) then
((if h_3508 : ((proj_num__0 i) ≠ none) then
((if h_3509 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) then
((if h_3510 : (v_n = 0) then
((match interp_inv_instr_val y_290 with
 | some ⟨v_val, h_3511⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)] : (List instr))))).flatMap fun ⟨_, h_3512⟩ => ((if h_3513 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3514 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨[], by subst_vars; first | (apply Step_read.memory_fill_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_fill_zero]⟩])
else []))
else []))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_fill_succ (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_292 i), y_293, (.CONST y_294 (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) => ((if h_3515 : (y_292 = (numtype_addrtype «at»)) then
((if h_3516 : (y_294 = (numtype_addrtype «at»)) then
((if h_3517 : ((proj_num__0 i) ≠ none) then
((if h_3518 : (v_n ≠ 0) then
((if h_3519 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_instr_val y_293 with
 | some ⟨v_val, h_3520⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)] : (List instr))))).flatMap fun ⟨_, h_3521⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») i))).flatMap fun ⟨_, h_3522⟩ => (((interp_wf_instr_i ((.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )))).flatMap fun ⟨_, h_3523⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (iadd_ (size (numtype_addrtype «at»)) (Option.get! (proj_num__0 i)) (.mk_uN 1)))))).flatMap fun ⟨_, h_3524⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3525⟩ => (((interp_wf_instr_i ((.MEMORY_FILL x))).flatMap fun ⟨_, h_3526⟩ => ((if h_3527 : ((2 ^ (size (numtype_addrtype «at»))) ≠ 0) then
((if h_3528 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_3529 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3530 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (iadd_ (size (numtype_addrtype «at»)) (Option.get! (proj_num__0 i)) (.mk_uN 1)))), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.MEMORY_FILL x)] : (List instr)), by subst_vars; first | (apply Step_read.memory_fill_succ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_fill_succ]⟩])
else []))
else []))
else []))
else []))))))))))))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_copy_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_295 i_1), (.CONST y_296 i_2), (.CONST y_297 (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) => ((if h_3531 : (y_297 = (numtype_addrtype at')) then
((if h_3532 : ((proj_num__0 i_1) ≠ none) then
((if h_3533 : ((proj_num__0 i_2) ≠ none) then
((if h_3534 : ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_mem z x_1).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_mem z x_2).BYTES)))) then
((match interp_inv_numtype_addrtype y_295 with
 | some ⟨at_1, h_3535⟩ => ((match interp_inv_numtype_addrtype y_296 with
 | some ⟨at_2, h_3536⟩ => (((interp_wf_meminst_i ((fun_mem z x_1))).flatMap fun ⟨_, h_3537⟩ => (((interp_wf_meminst_i ((fun_mem z x_2))).flatMap fun ⟨_, h_3538⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_3539⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3540⟩ => ((if h_3541 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_1)]!) < (List.length ((sof z).MEMS))) then
((if h_3542 : ((proj_uN_0 x_1) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3543 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_2)]!) < (List.length ((sof z).MEMS))) then
((if h_3544 : ((proj_uN_0 x_2) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.memory_copy_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_copy_oob]⟩])
else []))
else []))
else []))
else []))))))))))
 | none => []))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_copy_zero (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_298 i_1), (.CONST y_299 i_2), (.CONST y_300 (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) => ((if h_3545 : (y_300 = (numtype_addrtype at')) then
((if h_3546 : ((proj_num__0 i_1) ≠ none) then
((if h_3547 : ((proj_num__0 i_2) ≠ none) then
((if h_3548 : (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) then
((if h_3549 : (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES))) then
((if h_3550 : (v_n = 0) then
((match interp_inv_numtype_addrtype y_298 with
 | some ⟨at_1, h_3551⟩ => ((match interp_inv_numtype_addrtype y_299 with
 | some ⟨at_2, h_3552⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_3553⟩ => ((if h_3554 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_1)]!) < (List.length ((sof z).MEMS))) then
((if h_3555 : ((proj_uN_0 x_1) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3556 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_2)]!) < (List.length ((sof z).MEMS))) then
((if h_3557 : ((proj_uN_0 x_2) < (List.length (((fof z).MODULE).MEMS))) then
([⟨[], by subst_vars; first | (apply Step_read.memory_copy_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_copy_zero]⟩])
else []))
else []))
else []))
else []))))
 | none => []))
 | none => []))
else []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_copy_le (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_301 i_1), (.CONST y_302 i_2), (.CONST y_303 (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) => ((if h_3558 : (y_303 = (numtype_addrtype at')) then
((if h_3559 : ((proj_num__0 i_1) ≠ none) then
((if h_3560 : ((proj_num__0 i_2) ≠ none) then
((if h_3561 : (v_n ≠ 0) then
((if h_3562 : (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) then
((if h_3563 : (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES))) then
((if h_3564 : ((proj_uN_0 (Option.get! (proj_num__0 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 i_2)))) then
((match interp_inv_numtype_addrtype y_301 with
 | some ⟨at_1, h_3565⟩ => ((match interp_inv_numtype_addrtype y_302 with
 | some ⟨at_2, h_3566⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_3567⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_1) i_1))).flatMap fun ⟨_, h_3568⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_2) i_2))).flatMap fun ⟨_, h_3569⟩ => (((interp_wf_instr_i ((.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )))).flatMap fun ⟨_, h_3570⟩ => (((interp_wf_instr_i ((.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )))).flatMap fun ⟨_, h_3571⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (iadd_ (size (numtype_addrtype at_1)) (Option.get! (proj_num__0 i_1)) (.mk_uN 1)))))).flatMap fun ⟨_, h_3572⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (iadd_ (size (numtype_addrtype at_2)) (Option.get! (proj_num__0 i_2)) (.mk_uN 1)))))).flatMap fun ⟨_, h_3573⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3574⟩ => (((interp_wf_instr_i ((.MEMORY_COPY x_1 x_2))).flatMap fun ⟨_, h_3575⟩ => ((if h_3576 : ((2 ^ (size (numtype_addrtype at_1))) ≠ 0) then
((if h_3577 : ((2 ^ (size (numtype_addrtype at_2))) ≠ 0) then
((if h_3578 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_3579 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_1)]!) < (List.length ((sof z).MEMS))) then
((if h_3580 : ((proj_uN_0 x_1) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3581 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_2)]!) < (List.length ((sof z).MEMS))) then
((if h_3582 : ((proj_uN_0 x_2) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (iadd_ (size (numtype_addrtype at_1)) (Option.get! (proj_num__0 i_1)) (.mk_uN 1)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (iadd_ (size (numtype_addrtype at_2)) (Option.get! (proj_num__0 i_2)) (.mk_uN 1)))), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.MEMORY_COPY x_1 x_2)] : (List instr)), by subst_vars; first | (apply Step_read.memory_copy_le <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_copy_le]⟩])
else []))
else []))
else []))
else []))
else []))
else []))
else []))))))))))))))))))))
 | none => []))
 | none => []))
else []))
else []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_copy_gt (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_304 i_1), (.CONST y_305 i_2), (.CONST y_306 (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) => ((if h_3583 : (y_306 = (numtype_addrtype at')) then
((if h_3584 : ((proj_num__0 i_1) ≠ none) then
((if h_3585 : ((proj_num__0 i_2) ≠ none) then
((if h_3586 : ((proj_uN_0 (Option.get! (proj_num__0 i_1))) > (proj_uN_0 (Option.get! (proj_num__0 i_2)))) then
((if h_3587 : (v_n ≠ 0) then
((if h_3588 : (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) then
((if h_3589 : (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES))) then
((match interp_inv_numtype_addrtype y_304 with
 | some ⟨at_1, h_3590⟩ => ((match interp_inv_numtype_addrtype y_305 with
 | some ⟨at_2, h_3591⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_3592⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN (Int.toNat ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n)) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3593⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN (Int.toNat ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n)) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3594⟩ => (((interp_wf_instr_i ((.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )))).flatMap fun ⟨_, h_3595⟩ => (((interp_wf_instr_i ((.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )))).flatMap fun ⟨_, h_3596⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_1) i_1))).flatMap fun ⟨_, h_3597⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at_2) i_2))).flatMap fun ⟨_, h_3598⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3599⟩ => (((interp_wf_instr_i ((.MEMORY_COPY x_1 x_2))).flatMap fun ⟨_, h_3600⟩ => ((if h_3601 : (0 ≤ ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n)) - (Int.ofNat 1))) then
((if h_3602 : (0 ≤ ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n)) - (Int.ofNat 1))) then
((if h_3603 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_3604 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_1)]!) < (List.length ((sof z).MEMS))) then
((if h_3605 : ((proj_uN_0 x_1) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3606 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x_2)]!) < (List.length ((sof z).MEMS))) then
((if h_3607 : ((proj_uN_0 x_2) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([(.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN (Int.toNat ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n)) - (Int.ofNat 1)))))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN (Int.toNat ((Int.ofNat ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n)) - (Int.ofNat 1)))))), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.MEMORY_COPY x_1 x_2)] : (List instr)), by subst_vars; first | (apply Step_read.memory_copy_gt <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_copy_gt]⟩])
else []))
else []))
else []))
else []))
else []))
else []))
else []))))))))))))))))))))
 | none => []))
 | none => []))
else []))
else []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_init_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_307 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) => ((if h_3608 : ((proj_num__0 i) ≠ none) then
((if h_3609 : ((proj_num__0 j) ≠ none) then
((if h_3610 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_data z y).BYTES)))) then
((match interp_inv_numtype_addrtype y_307 with
 | some ⟨«at», h_3611⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_3612⟩ => (((interp_wf_datainst_i ((fun_data z y))).flatMap fun ⟨_, h_3613⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_3614⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3615⟩ => ((if h_3616 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3617 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3618 : (((((fof z).MODULE).DATAS)[(proj_uN_0 y)]!) < (List.length ((sof z).DATAS))) then
((if h_3619 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).DATAS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.memory_init_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_init_oob]⟩])
else []))
else []))
else []))
else []))))))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_init_zero (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_308 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) => ((if h_3620 : ((proj_num__0 i) ≠ none) then
((if h_3621 : ((proj_num__0 j) ≠ none) then
((if h_3622 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) then
((if h_3623 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_data z y).BYTES))) then
((if h_3624 : (v_n = 0) then
((match interp_inv_numtype_addrtype y_308 with
 | some ⟨«at», h_3625⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_3626⟩ => ((if h_3627 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3628 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
((if h_3629 : (((((fof z).MODULE).DATAS)[(proj_uN_0 y)]!) < (List.length ((sof z).DATAS))) then
((if h_3630 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).DATAS))) then
([⟨[], by subst_vars; first | (apply Step_read.memory_init_zero <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_init_zero]⟩])
else []))
else []))
else []))
else []))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_memory_init_succ (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_309 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) => ((if h_3631 : ((proj_uN_0 (Option.get! (proj_num__0 j))) < (List.length ((fun_data z y).BYTES))) then
((if h_3632 : ((proj_num__0 j) ≠ none) then
((if h_3633 : ((proj_num__0 i) ≠ none) then
((if h_3634 : (v_n ≠ 0) then
((if h_3635 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) then
((if h_3636 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_data z y).BYTES))) then
((match interp_inv_numtype_addrtype y_309 with
 | some ⟨«at», h_3637⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)] : (List instr))))).flatMap fun ⟨_, h_3638⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») i))).flatMap fun ⟨_, h_3639⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN (proj_byte_0 (((fun_data z y).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!))))))).flatMap fun ⟨_, h_3640⟩ => (((interp_wf_instr_i ((.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )))).flatMap fun ⟨_, h_3641⟩ => (((interp_wf_instr_i ((.CONST (numtype_addrtype «at») (.mk_num__0 «at» (iadd_ (size (numtype_addrtype «at»)) (Option.get! (proj_num__0 i)) (.mk_uN 1)))))).flatMap fun ⟨_, h_3642⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (iadd_ 32 (Option.get! (proj_num__0 j)) (.mk_uN 1)))))).flatMap fun ⟨_, h_3643⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))))).flatMap fun ⟨_, h_3644⟩ => (((interp_wf_instr_i ((.MEMORY_INIT x y))).flatMap fun ⟨_, h_3645⟩ => ((if h_3646 : (((((fof z).MODULE).DATAS)[(proj_uN_0 y)]!) < (List.length ((sof z).DATAS))) then
((if h_3647 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).DATAS))) then
((if h_3648 : ((2 ^ (size (numtype_addrtype «at»))) ≠ 0) then
((if h_3649 : ((2 ^ 32) ≠ 0) then
((if h_3650 : (0 ≤ ((Int.ofNat v_n) - (Int.ofNat 1))) then
((if h_3651 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_3652 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨([(.CONST (numtype_addrtype «at») i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (proj_byte_0 (((fun_data z y).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!))))), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (iadd_ (size (numtype_addrtype «at»)) (Option.get! (proj_num__0 i)) (.mk_uN 1)))), (.CONST .I32 (.mk_num__0 .I32 (iadd_ 32 (Option.get! (proj_num__0 j)) (.mk_uN 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (Int.toNat ((Int.ofNat v_n) - (Int.ofNat 1)))))), (.MEMORY_INIT x y)] : (List instr)), by subst_vars; first | (apply Step_read.memory_init_succ <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.memory_init_succ]⟩])
else []))
else []))
else []))
else []))
else []))
else []))
else []))))))))))))))))))
 | none => []))
else []))
else []))
else []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_ref_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_NULL ht)]) => (((interp_wf_config_i ((.mk_config z ([(.REF_NULL ht)] : (List instr))))).flatMap fun ⟨_, h_3653⟩ => (((interp_wf_instr_i (.REF_NULL_ADDR)).flatMap fun ⟨_, h_3654⟩ => ([⟨([.REF_NULL_ADDR] : (List instr)), by subst_vars; first | (apply Step_read.ref_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.ref_null]⟩])))))
 | _ => []

def interp_Step_read_io_ref_func (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_FUNC x)]) => ((if h_3655 : ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) then
(((interp_wf_config_i ((.mk_config z ([(.REF_FUNC x)] : (List instr))))).flatMap fun ⟨_, h_3656⟩ => (((interp_wf_instr_i ((.REF_FUNC_ADDR (((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!)))).flatMap fun ⟨_, h_3657⟩ => ([⟨([(.REF_FUNC_ADDR (((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!))] : (List instr)), by subst_vars; first | (apply Step_read.ref_func <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.ref_func]⟩])))))
else []))
 | _ => []

def interp_Step_read_io_ref_test_true (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config (.mk_state s f) [y_310, (.REF_TEST rt)]) => ((match interp_inv_instr_ref y_310 with
 | some ⟨v_ref, h_3658⟩ => (((interp_fun_inst_reftype_iio ((f.MODULE)) (rt)).flatMap fun ⟨o_311, h_3659⟩ => (match o_311 with
 | var_0 => (((interp_Ref_ok_iii (s) (v_ref) (var_0)).flatMap fun ⟨_, h_3660⟩ => (((interp_wf_reftype_i (var_0)).flatMap fun ⟨_, h_3661⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s f) ([(instr_ref v_ref), (.REF_TEST rt)] : (List instr))))).flatMap fun ⟨_, h_3662⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1))))).flatMap fun ⟨_, h_3663⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))] : (List instr)), by subst_vars; first | (apply Step_read.ref_test_true <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.ref_test_true]⟩]))))))))))))
 | none => []))
 | _ => []

def interp_Step_read_io_ref_cast_succeed (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config (.mk_state s f) [y_313, (.REF_CAST rt)]) => ((match interp_inv_instr_ref y_313 with
 | some ⟨v_ref, h_3666⟩ => (((interp_fun_inst_reftype_iio ((f.MODULE)) (rt)).flatMap fun ⟨o_314, h_3667⟩ => (match o_314 with
 | var_0 => (((interp_Ref_ok_iii (s) (v_ref) (var_0)).flatMap fun ⟨_, h_3668⟩ => (((interp_wf_reftype_i (var_0)).flatMap fun ⟨_, h_3669⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s f) ([(instr_ref v_ref), (.REF_CAST rt)] : (List instr))))).flatMap fun ⟨_, h_3670⟩ => ([⟨([(instr_ref v_ref)] : (List instr)), by subst_vars; first | (apply Step_read.ref_cast_succeed <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.ref_cast_succeed]⟩]))))))))))
 | none => []))
 | _ => []

def interp_Step_read_io_struct_get_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.STRUCT_GET sx_opt x i)]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.STRUCT_GET sx_opt x i)] : (List instr))))).flatMap fun ⟨_, h_3741⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3742⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.struct_get_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.struct_get_null]⟩])))))
 | _ => []

def interp_Step_read_io_array_new_default (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DEFAULT x)]) => (((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_322, h_3776⟩ => (match o_322 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_323, h_3778⟩ => (match o_323 with
 | (.ARRAY (.mk_fieldtype mut_opt zt)) => (((interp_fun_default__io ((unpack zt))).flatMap fun ⟨o_324, h_3779⟩ => (match o_324 with
 | var_1 => ((if h_3780 : (var_1 ≠ none) then
((match h_3781 : ((Option.get! var_1) : (Option val)) with
 | (some v_val) => (((interp_wf_val_i (v_val)).flatMap fun ⟨_, h_3782⟩ => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_3783⟩ => (((interp_allL (fun (iter : val) => (interp_wf_val_i (iter))) (Option.toList (Option.get! var_1))).flatMap fun ⟨_, h_3784⟩ => (((interp_wf_valtype_i ((unpack zt))).flatMap fun ⟨_, h_3785⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DEFAULT x)] : (List instr))))).flatMap fun ⟨_, h_3786⟩ => (((interp_wf_instr_i ((.ARRAY_NEW_FIXED x (.mk_uN v_n)))).flatMap fun ⟨_, h_3787⟩ => (((interp_wf_comptype_i ((.ARRAY (.mk_fieldtype mut_opt zt)))).flatMap fun ⟨_, h_3788⟩ => ([⟨((List.replicate v_n (instr_val v_val)) ++ ([(.ARRAY_NEW_FIXED x (.mk_uN v_n))] : (List instr))), by subst_vars; first | (apply Step_read.array_new_default <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_new_default]⟩])))))))))))))))
 | _ => []))
else [])))))
 | _ => []))))))
 | _ => []

def interp_Step_read_io_array_new_elem_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)]) => ((if h_3789 : ((proj_num__0 i) ≠ none) then
((if h_3790 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) then
(((interp_wf_eleminst_i ((fun_elem z y))).flatMap fun ⟨_, h_3791⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)] : (List instr))))).flatMap fun ⟨_, h_3792⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3793⟩ => ((if h_3794 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_3795 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_new_elem_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_new_elem_oob]⟩])
else []))
else []))))))))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_new_elem_alloc (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)]) => ((if h_3796 : ((proj_num__0 i) ≠ none) then
(((fun (ref_lst : (List ref)) (h_3797 : ((List.take v_n (List.drop (proj_uN_0 (Option.get! (proj_num__0 i))) ((fun_elem z y).REFS))) : (List ref)) = ref_lst) => ((if h_3798 : (v_n = (List.length ref_lst)) then
(((interp_allL (fun (v_ref : ref) => (interp_wf_ref_i (v_ref))) ref_lst).flatMap fun ⟨_, h_3799⟩ => (((interp_wf_eleminst_i ((fun_elem z y))).flatMap fun ⟨_, h_3800⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)] : (List instr))))).flatMap fun ⟨_, h_3801⟩ => (((interp_wf_instr_i ((.ARRAY_NEW_FIXED x (.mk_uN v_n)))).flatMap fun ⟨_, h_3802⟩ => ((if h_3803 : ((List.length ref_lst) = v_n) then
((if h_3804 : ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n ≤ (List.length ((fun_elem z y).REFS))) then
((if h_3805 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_3806 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨((List.map (fun (v_ref : ref) => (instr_ref v_ref)) ref_lst) ++ ([(.ARRAY_NEW_FIXED x (.mk_uN v_n))] : (List instr))), by subst_vars; first | (apply Step_read.array_new_elem_alloc <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_new_elem_alloc]⟩])
else []))
else []))
else []))
else []))))))))))
else []))) ((List.take v_n (List.drop (proj_uN_0 (Option.get! (proj_num__0 i))) ((fun_elem z y).REFS))) : (List ref)) rfl))
else []))
 | _ => []

def interp_Step_read_io_array_new_data_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DATA x y)]) => ((if h_3807 : ((proj_num__0 i) ≠ none) then
(((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_325, h_3808⟩ => (match o_325 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_326, h_3809⟩ => (match o_326 with
 | (.ARRAY (.mk_fieldtype mut_opt zt)) => ((if h_3810 : ((zsize zt) ≠ none) then
((if h_3811 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_data z y).BYTES))) then
(((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_3812⟩ => (((interp_wf_datainst_i ((fun_data z y))).flatMap fun ⟨_, h_3813⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DATA x y)] : (List instr))))).flatMap fun ⟨_, h_3814⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3815⟩ => (((interp_wf_comptype_i ((.ARRAY (.mk_fieldtype mut_opt zt)))).flatMap fun ⟨_, h_3816⟩ => ((if h_3817 : ((((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_3818 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_3819 : (((((fof z).MODULE).DATAS)[(proj_uN_0 y)]!) < (List.length ((sof z).DATAS))) then
((if h_3820 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).DATAS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_new_data_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_new_data_oob]⟩])
else []))
else []))
else []))
else []))))))))))))
else []))
else []))
 | _ => []))))))
else []))
 | _ => []

def interp_Step_read_io_array_get_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i), (.ARRAY_GET sx_opt x)] : (List instr))))).flatMap fun ⟨_, h_3963⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3964⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_get_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_get_null]⟩])))))
 | _ => []

def interp_Step_read_io_array_get_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) => ((if h_3965 : ((proj_num__0 i) ≠ none) then
((if h_3966 : (a < (List.length (fun_arrayinst z))) then
((if h_3967 : ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
(((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_3968⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)] : (List instr))))).flatMap fun ⟨_, h_3969⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3970⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_get_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_get_oob]⟩])))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_get_array (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) => ((if h_3971 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
((if h_3972 : (a < (List.length (fun_arrayinst z))) then
((if h_3973 : ((proj_num__0 i) ≠ none) then
(((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_329, h_3974⟩ => (match o_329 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_330, h_3976⟩ => (match o_330 with
 | (.ARRAY (.mk_fieldtype mut_opt zt)) => ((if h_3977 : ((unpackfield_ zt sx_opt ((((fun_arrayinst z)[a]!).FIELDS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!)) ≠ none) then
(((interp_wf_val_i ((Option.get! (unpackfield_ zt sx_opt ((((fun_arrayinst z)[a]!).FIELDS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))))).flatMap fun ⟨_, h_3978⟩ => (((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_3979⟩ => (((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_3980⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)] : (List instr))))).flatMap fun ⟨_, h_3981⟩ => (((interp_wf_comptype_i ((.ARRAY (.mk_fieldtype mut_opt zt)))).flatMap fun ⟨_, h_3982⟩ => ([⟨([(instr_val (Option.get! (unpackfield_ zt sx_opt ((((fun_arrayinst z)[a]!).FIELDS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))))] : (List instr)), by subst_vars; first | (apply Step_read.array_get_array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_get_array]⟩])))))))))))
else []))
 | _ => []))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_len_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, .ARRAY_LEN]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, .ARRAY_LEN] : (List instr))))).flatMap fun ⟨_, h_3983⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3984⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_len_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_len_null]⟩])))))
 | _ => []

def interp_Step_read_io_array_len_array (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), .ARRAY_LEN]) => ((if h_3985 : (a < (List.length (fun_arrayinst z))) then
(((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), .ARRAY_LEN] : (List instr))))).flatMap fun ⟨_, h_3986⟩ => (((interp_wf_instr_i ((.CONST .I32 (.mk_num__0 .I32 (.mk_uN (List.length (((fun_arrayinst z)[a]!).FIELDS))))))).flatMap fun ⟨_, h_3987⟩ => ([⟨([(.CONST .I32 (.mk_num__0 .I32 (.mk_uN (List.length (((fun_arrayinst z)[a]!).FIELDS)))))] : (List instr)), by subst_vars; first | (apply Step_read.array_len_array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_len_array]⟩])))))
else []))
 | _ => []

def interp_Step_read_io_array_fill_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i), y_331, (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) => ((match interp_inv_instr_val y_331 with
 | some ⟨v_val, h_3988⟩ => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)] : (List instr))))).flatMap fun ⟨_, h_3989⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3990⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_fill_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_fill_null]⟩])))))
 | none => []))
 | _ => []

def interp_Step_read_io_array_fill_oob (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), y_332, (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) => ((if h_3991 : ((proj_num__0 i) ≠ none) then
((if h_3992 : (a < (List.length (fun_arrayinst z))) then
((if h_3993 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
((match interp_inv_instr_val y_332 with
 | some ⟨v_val, h_3994⟩ => (((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_3995⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)] : (List instr))))).flatMap fun ⟨_, h_3996⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_3997⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_fill_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_fill_oob]⟩])))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_copy_null1 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i_1), y_335, (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) => ((match interp_inv_instr_ref y_335 with
 | some ⟨v_ref, h_4004⟩ => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i_1), (instr_ref v_ref), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_4005⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4006⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_copy_null1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_copy_null1]⟩])))))
 | none => []))
 | _ => []

def interp_Step_read_io_array_copy_null2 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [y_336, (.CONST .I32 i_1), .REF_NULL_ADDR, (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) => ((match interp_inv_instr_ref y_336 with
 | some ⟨v_ref, h_4007⟩ => (((interp_wf_config_i ((.mk_config z ([(instr_ref v_ref), (.CONST .I32 i_1), .REF_NULL_ADDR, (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_4008⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4009⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_copy_null2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_copy_null2]⟩])))))
 | none => []))
 | _ => []

def interp_Step_read_io_array_copy_oob1 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) => ((if h_4010 : ((proj_num__0 i_1) ≠ none) then
((if h_4011 : (a_1 < (List.length (fun_arrayinst z))) then
((if h_4012 : (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) then
(((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_4013⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_4014⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4015⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_copy_oob1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_copy_oob1]⟩])))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_copy_oob2 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) => ((if h_4016 : ((proj_num__0 i_2) ≠ none) then
((if h_4017 : (a_2 < (List.length (fun_arrayinst z))) then
((if h_4018 : (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) then
(((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_4019⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)] : (List instr))))).flatMap fun ⟨_, h_4020⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4021⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_copy_oob2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_copy_oob2]⟩])))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_init_elem_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)] : (List instr))))).flatMap fun ⟨_, h_4033⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4034⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_elem_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_elem_null]⟩])))))
 | _ => []

def interp_Step_read_io_array_init_elem_oob1 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) => ((if h_4035 : ((proj_num__0 i) ≠ none) then
((if h_4036 : (a < (List.length (fun_arrayinst z))) then
((if h_4037 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
(((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_4038⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)] : (List instr))))).flatMap fun ⟨_, h_4039⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4040⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_elem_oob1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_elem_oob1]⟩])))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_init_elem_oob2 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) => ((if h_4041 : ((proj_num__0 j) ≠ none) then
((if h_4042 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS))) then
(((interp_wf_eleminst_i ((fun_elem z y))).flatMap fun ⟨_, h_4043⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)] : (List instr))))).flatMap fun ⟨_, h_4044⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4045⟩ => ((if h_4046 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 y)]!) < (List.length ((sof z).ELEMS))) then
((if h_4047 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_elem_oob2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_elem_oob2]⟩])
else []))
else []))))))))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_init_data_null (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)] : (List instr))))).flatMap fun ⟨_, h_4054⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4055⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_data_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_data_null]⟩])))))
 | _ => []

def interp_Step_read_io_array_init_data_oob1 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) => ((if h_4056 : ((proj_num__0 i) ≠ none) then
((if h_4057 : (a < (List.length (fun_arrayinst z))) then
((if h_4058 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
(((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_4059⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)] : (List instr))))).flatMap fun ⟨_, h_4060⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4061⟩ => ([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_data_oob1 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_data_oob1]⟩])))))))
else []))
else []))
else []))
 | _ => []

def interp_Step_read_io_array_init_data_oob2 (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) => ((if h_4062 : ((proj_num__0 j) ≠ none) then
(((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_339, h_4063⟩ => (match o_339 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_340, h_4064⟩ => (match o_340 with
 | (.ARRAY (.mk_fieldtype mut_opt zt)) => ((if h_4065 : ((zsize zt) ≠ none) then
((if h_4066 : (((proj_uN_0 (Option.get! (proj_num__0 j))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_data z y).BYTES))) then
(((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_4067⟩ => (((interp_wf_datainst_i ((fun_data z y))).flatMap fun ⟨_, h_4068⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)] : (List instr))))).flatMap fun ⟨_, h_4069⟩ => (((interp_wf_instr_i (.TRAP)).flatMap fun ⟨_, h_4070⟩ => (((interp_wf_comptype_i ((.ARRAY (.mk_fieldtype mut_opt zt)))).flatMap fun ⟨_, h_4071⟩ => ((if h_4072 : ((((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_4073 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_4074 : (((((fof z).MODULE).DATAS)[(proj_uN_0 y)]!) < (List.length ((sof z).DATAS))) then
((if h_4075 : ((proj_uN_0 y) < (List.length (((fof z).MODULE).DATAS))) then
([⟨([.TRAP] : (List instr)), by subst_vars; first | (apply Step_read.array_init_data_oob2 <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step_read.array_init_data_oob2]⟩])
else []))
else []))
else []))
else []))))))))))))
else []))
else []))
 | _ => []))))))
else []))
 | _ => []

def interp_Step_read_io (a0 : config) : List {o : (List instr) // (Step_read a0 o)} :=
  interp_Step_read_io_block a0 ++
  interp_Step_read_io_loop a0 ++
  interp_Step_read_io_br_on_cast_succeed a0 ++
  interp_Step_read_io_br_on_cast_fail_succeed a0 ++
  interp_Step_read_io_call a0 ++
  interp_Step_read_io_call_ref_null a0 ++
  interp_Step_read_io_return_call a0 ++
  interp_Step_read_io_return_call_ref_label a0 ++
  interp_Step_read_io_return_call_ref_handler a0 ++
  interp_Step_read_io_return_call_ref_frame_null a0 ++
  interp_Step_read_io_return_call_ref_frame_addr a0 ++
  interp_Step_read_io_throw_ref_null a0 ++
  interp_Step_read_io_throw_ref_instrs a0 ++
  interp_Step_read_io_throw_ref_label a0 ++
  interp_Step_read_io_throw_ref_frame a0 ++
  interp_Step_read_io_throw_ref_handler_empty a0 ++
  interp_Step_read_io_throw_ref_handler_catch a0 ++
  interp_Step_read_io_throw_ref_handler_catch_ref a0 ++
  interp_Step_read_io_throw_ref_handler_catch_all a0 ++
  interp_Step_read_io_throw_ref_handler_catch_all_ref a0 ++
  interp_Step_read_io_try_table a0 ++
  interp_Step_read_io_local_get a0 ++
  interp_Step_read_io_global_get a0 ++
  interp_Step_read_io_table_get_oob a0 ++
  interp_Step_read_io_table_get_val a0 ++
  interp_Step_read_io_table_size a0 ++
  interp_Step_read_io_table_fill_oob a0 ++
  interp_Step_read_io_table_fill_zero a0 ++
  interp_Step_read_io_table_fill_succ a0 ++
  interp_Step_read_io_table_copy_oob a0 ++
  interp_Step_read_io_table_init_oob a0 ++
  interp_Step_read_io_table_init_zero a0 ++
  interp_Step_read_io_table_init_succ a0 ++
  interp_Step_read_io_load_num_oob a0 ++
  interp_Step_read_io_load_pack_oob a0 ++
  interp_Step_read_io_vload_oob a0 ++
  interp_Step_read_io_vload_pack_oob a0 ++
  interp_Step_read_io_vload_splat_oob a0 ++
  interp_Step_read_io_vload_zero_oob a0 ++
  interp_Step_read_io_vload_lane_oob a0 ++
  interp_Step_read_io_memory_fill_oob a0 ++
  interp_Step_read_io_memory_fill_zero a0 ++
  interp_Step_read_io_memory_fill_succ a0 ++
  interp_Step_read_io_memory_copy_oob a0 ++
  interp_Step_read_io_memory_copy_zero a0 ++
  interp_Step_read_io_memory_copy_le a0 ++
  interp_Step_read_io_memory_copy_gt a0 ++
  interp_Step_read_io_memory_init_oob a0 ++
  interp_Step_read_io_memory_init_zero a0 ++
  interp_Step_read_io_memory_init_succ a0 ++
  interp_Step_read_io_ref_null a0 ++
  interp_Step_read_io_ref_func a0 ++
  interp_Step_read_io_ref_test_true a0 ++
  interp_Step_read_io_ref_cast_succeed a0 ++
  interp_Step_read_io_struct_get_null a0 ++
  interp_Step_read_io_array_new_default a0 ++
  interp_Step_read_io_array_new_elem_oob a0 ++
  interp_Step_read_io_array_new_elem_alloc a0 ++
  interp_Step_read_io_array_new_data_oob a0 ++
  interp_Step_read_io_array_get_null a0 ++
  interp_Step_read_io_array_get_oob a0 ++
  interp_Step_read_io_array_get_array a0 ++
  interp_Step_read_io_array_len_null a0 ++
  interp_Step_read_io_array_len_array a0 ++
  interp_Step_read_io_array_fill_null a0 ++
  interp_Step_read_io_array_fill_oob a0 ++
  interp_Step_read_io_array_copy_null1 a0 ++
  interp_Step_read_io_array_copy_null2 a0 ++
  interp_Step_read_io_array_copy_oob1 a0 ++
  interp_Step_read_io_array_copy_oob2 a0 ++
  interp_Step_read_io_array_init_elem_null a0 ++
  interp_Step_read_io_array_init_elem_oob1 a0 ++
  interp_Step_read_io_array_init_elem_oob2 a0 ++
  interp_Step_read_io_array_init_data_null a0 ++
  interp_Step_read_io_array_init_data_oob1 a0 ++
  interp_Step_read_io_array_init_data_oob2 a0

mutual

partial def interp_Step_io_pure (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z instr_lst) => (((interp_Step_pure_io (instr_lst)).flatMap fun ⟨o_105, h_549⟩ => (match o_105 with
 | instr'_lst => (((interp_wf_config_i ((.mk_config z instr_lst))).flatMap fun ⟨_, h_550⟩ => (((interp_wf_config_i ((.mk_config z instr'_lst))).flatMap fun ⟨_, h_551⟩ => ([⟨(.mk_config z instr'_lst), by subst_vars; first | (apply Step.pure <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.pure]⟩]))))))))

partial def interp_Step_io_read (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z instr_lst) => (((interp_Step_read_io ((.mk_config z instr_lst))).flatMap fun ⟨o_106, h_552⟩ => (match o_106 with
 | instr'_lst => (((interp_wf_config_i ((.mk_config z instr_lst))).flatMap fun ⟨_, h_553⟩ => (((interp_wf_config_i ((.mk_config z instr'_lst))).flatMap fun ⟨_, h_554⟩ => ([⟨(.mk_config z instr'_lst), by subst_vars; first | (apply Step.read <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.read]⟩]))))))))

partial def interp_Step_io_ctxt_instrs (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z y_107) => (((interp_splits y_107).flatMap fun ⟨(a_108, b_109), h_555⟩ => ((match interp_invMap interp_inv_instr_val a_108 with
 | some ⟨val_lst, h_556⟩ => (((interp_splits b_109).flatMap fun ⟨(a_110, b_111), h_557⟩ => ((match a_110 with
 | instr_lst => ((match b_111 with
 | instr_1_lst => ((if h_560 : ((val_lst ≠ []) ∨ (instr_1_lst ≠ [])) then
(((interp_Step_io ((.mk_config z instr_lst))).flatMap fun ⟨o_112, h_561⟩ => (match o_112 with
 | (.mk_config z' instr'_lst) => (((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (instr_lst ++ instr_1_lst))))).flatMap fun ⟨_, h_562⟩ => (((interp_wf_config_i ((.mk_config z' ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (instr'_lst ++ instr_1_lst))))).flatMap fun ⟨_, h_563⟩ => (((interp_wf_config_i ((.mk_config z instr_lst))).flatMap fun ⟨_, h_564⟩ => (((interp_wf_config_i ((.mk_config z' instr'_lst))).flatMap fun ⟨_, h_565⟩ => ([⟨(.mk_config z' ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (instr'_lst ++ instr_1_lst))), by subst_vars; first | (apply Step.ctxt_instrs <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.ctxt_instrs]⟩]))))))))))))
else []))))))))
 | none => []))))

partial def interp_Step_io_ctxt_label (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.LABEL_ v_n instr_0_lst instr_lst)]) => (((interp_Step_io ((.mk_config z instr_lst))).flatMap fun ⟨o_113, h_566⟩ => (match o_113 with
 | (.mk_config z' instr'_lst) => (((interp_wf_config_i ((.mk_config z ([(.LABEL_ v_n instr_0_lst instr_lst)] : (List instr))))).flatMap fun ⟨_, h_567⟩ => (((interp_wf_config_i ((.mk_config z' ([(.LABEL_ v_n instr_0_lst instr'_lst)] : (List instr))))).flatMap fun ⟨_, h_568⟩ => (((interp_wf_config_i ((.mk_config z instr_lst))).flatMap fun ⟨_, h_569⟩ => (((interp_wf_config_i ((.mk_config z' instr'_lst))).flatMap fun ⟨_, h_570⟩ => ([⟨(.mk_config z' ([(.LABEL_ v_n instr_0_lst instr'_lst)] : (List instr))), by subst_vars; first | (apply Step.ctxt_label <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.ctxt_label]⟩]))))))))))))
 | _ => []

partial def interp_Step_io_ctxt_handler (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.HANDLER_ v_n catch_lst instr_lst)]) => (((interp_Step_io ((.mk_config z instr_lst))).flatMap fun ⟨o_114, h_571⟩ => (match o_114 with
 | (.mk_config z' instr'_lst) => (((interp_wf_config_i ((.mk_config z ([(.HANDLER_ v_n catch_lst instr_lst)] : (List instr))))).flatMap fun ⟨_, h_572⟩ => (((interp_wf_config_i ((.mk_config z' ([(.HANDLER_ v_n catch_lst instr'_lst)] : (List instr))))).flatMap fun ⟨_, h_573⟩ => (((interp_wf_config_i ((.mk_config z instr_lst))).flatMap fun ⟨_, h_574⟩ => (((interp_wf_config_i ((.mk_config z' instr'_lst))).flatMap fun ⟨_, h_575⟩ => ([⟨(.mk_config z' ([(.HANDLER_ v_n catch_lst instr'_lst)] : (List instr))), by subst_vars; first | (apply Step.ctxt_handler <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.ctxt_handler]⟩]))))))))))))
 | _ => []

partial def interp_Step_io_ctxt_frame (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config (.mk_state s f) [(.FRAME_ v_n f' instr_lst)]) => (((interp_Step_io ((.mk_config (.mk_state s f') instr_lst))).flatMap fun ⟨o_115, h_576⟩ => (match o_115 with
 | (.mk_config (.mk_state s' f'') instr'_lst) => (((interp_wf_config_i ((.mk_config (.mk_state s f) ([(.FRAME_ v_n f' instr_lst)] : (List instr))))).flatMap fun ⟨_, h_577⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s' f) ([(.FRAME_ v_n f'' instr'_lst)] : (List instr))))).flatMap fun ⟨_, h_578⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s f') instr_lst))).flatMap fun ⟨_, h_579⟩ => (((interp_wf_config_i ((.mk_config (.mk_state s' f'') instr'_lst))).flatMap fun ⟨_, h_580⟩ => ([⟨(.mk_config (.mk_state s' f) ([(.FRAME_ v_n f'' instr'_lst)] : (List instr))), by subst_vars; first | (apply Step.ctxt_frame <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.ctxt_frame]⟩]))))))))))))
 | _ => []

partial def interp_Step_io_throw (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z y_116) => (((interp_splits y_116).flatMap fun ⟨(a_117, b_118), h_581⟩ => ((match interp_invMap interp_inv_instr_val a_117 with
 | some ⟨val_lst, h_582⟩ => (match h_583 : List.length val_lst with
 | v_n => (if h_584 : (v_n = (List.length val_lst)) then
((match b_118 with
 | [(.THROW x)] => ((if h_586 : ((as_deftype ((fun_tag z x).TYPE)) ≠ none) then
((if h_587 : ((proj_uN_0 x) < (List.length (fun_tagaddr z))) then
(((interp_Expand_io ((Option.get! (as_deftype ((fun_tag z x).TYPE))))).flatMap fun ⟨o_119, h_588⟩ => (match o_119 with
 | (.FUNC (.mk_list t_lst) (.mk_list [])) => ((if h_589 : (v_n = (List.length t_lst)) then
(((fun (a : Nat) (h_590 : ((List.length (fun_exninst z)) : Nat) = a) => (((fun (exn : exninst) (h_591 : ({ TAG := ((fun_tagaddr z)[(proj_uN_0 x)]!), FIELDS := val_lst } : exninst) = exn) => (((interp_wf_deftype_i ((Option.get! (as_deftype ((fun_tag z x).TYPE))))).flatMap fun ⟨_, h_592⟩ => (((interp_wf_taginst_i ((fun_tag z x))).flatMap fun ⟨_, h_593⟩ => (((interp_allL (fun (iter : exninst) => (interp_wf_exninst_i (iter))) (fun_exninst z)).flatMap fun ⟨_, h_594⟩ => (((interp_wf_config_i ((.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.THROW x)] : (List instr)))))).flatMap fun ⟨_, h_595⟩ => (((interp_wf_config_i ((.mk_config (add_exninst z ([exn] : (List exninst))) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr))))).flatMap fun ⟨_, h_596⟩ => (((interp_wf_comptype_i ((.FUNC (.mk_list t_lst) (.mk_list [])))).flatMap fun ⟨_, h_597⟩ => (((interp_wf_exninst_i ({ TAG := ((fun_tagaddr z)[(proj_uN_0 x)]!), FIELDS := val_lst })).flatMap fun ⟨_, h_598⟩ => ((if h_599 : ((List.length val_lst) = v_n) then
((if h_600 : (((((fof z).MODULE).TAGS)[(proj_uN_0 x)]!) < (List.length ((sof z).TAGS))) then
((if h_601 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TAGS))) then
([⟨(.mk_config (add_exninst z ([exn] : (List exninst))) ([(.REF_EXN_ADDR a), .THROW_REF] : (List instr))), by subst_vars; first | (apply Step.throw <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.throw]⟩])
else []))
else []))
else []))))))))))))))))) ({ TAG := ((fun_tagaddr z)[(proj_uN_0 x)]!), FIELDS := val_lst } : exninst) rfl))) ((List.length (fun_exninst z)) : Nat) rfl))
else []))
 | _ => [])))
else []))
else []))
 | _ => []))
else []))
 | none => []))))

partial def interp_Step_io_local_set (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [y_120, (.LOCAL_SET x)]) => ((match interp_inv_instr_val y_120 with
 | some ⟨v_val, h_602⟩ => (((interp_wf_config_i ((.mk_config z ([(instr_val v_val), (.LOCAL_SET x)] : (List instr))))).flatMap fun ⟨_, h_603⟩ => (((interp_wf_config_i ((.mk_config (with_local z x v_val) []))).flatMap fun ⟨_, h_604⟩ => ((if h_605 : ((proj_uN_0 x) < (List.length ((fof z).LOCALS))) then
([⟨(.mk_config (with_local z x v_val) []), by subst_vars; first | (apply Step.local_set <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.local_set]⟩])
else []))))))
 | none => []))
 | _ => []

partial def interp_Step_io_global_set (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [y_121, (.GLOBAL_SET x)]) => ((match interp_inv_instr_val y_121 with
 | some ⟨v_val, h_606⟩ => (((interp_wf_config_i ((.mk_config z ([(instr_val v_val), (.GLOBAL_SET x)] : (List instr))))).flatMap fun ⟨_, h_607⟩ => (((interp_wf_config_i ((.mk_config (with_global z x v_val) []))).flatMap fun ⟨_, h_608⟩ => ((if h_609 : (((((fof z).MODULE).GLOBALS)[(proj_uN_0 x)]!) < (List.length ((sof z).GLOBALS))) then
((if h_610 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).GLOBALS))) then
([⟨(.mk_config (with_global z x v_val) []), by subst_vars; first | (apply Step.global_set <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.global_set]⟩])
else []))
else []))))))
 | none => []))
 | _ => []

partial def interp_Step_io_table_set_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_122 i), y_123, (.TABLE_SET x)]) => ((if h_611 : ((proj_num__0 i) ≠ none) then
((if h_612 : ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) then
((match interp_inv_numtype_addrtype y_122 with
 | some ⟨«at», h_613⟩ => ((match interp_inv_instr_ref y_123 with
 | some ⟨v_ref, h_614⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_615⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_ref v_ref), (.TABLE_SET x)] : (List instr))))).flatMap fun ⟨_, h_616⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_617⟩ => ((if h_618 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_619 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.table_set_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.table_set_oob]⟩])
else []))
else []))))))))
 | none => []))
 | none => []))
else []))
else []))
 | _ => []

partial def interp_Step_io_table_set_val (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_124 i), y_125, (.TABLE_SET x)]) => ((if h_620 : ((proj_num__0 i) ≠ none) then
((if h_621 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) then
((match interp_inv_numtype_addrtype y_124 with
 | some ⟨«at», h_622⟩ => ((match interp_inv_instr_ref y_125 with
 | some ⟨v_ref, h_623⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_624⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (instr_ref v_ref), (.TABLE_SET x)] : (List instr))))).flatMap fun ⟨_, h_625⟩ => (((interp_wf_config_i ((.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) []))).flatMap fun ⟨_, h_626⟩ => ((if h_627 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_628 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((((sof z).TABLES)[((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!)]!).REFS))) then
((if h_629 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨(.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) []), by subst_vars; first | (apply Step.table_set_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.table_set_val]⟩])
else []))
else []))
else []))))))))
 | none => []))
 | none => []))
else []))
else []))
 | _ => []

partial def interp_Step_io_table_grow_succeed (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [y_126, (.CONST y_127 (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)]) => ((if h_630 : (y_127 = (numtype_addrtype «at»)) then
((match interp_inv_instr_ref y_126 with
 | some ⟨v_ref, h_631⟩ => (((interp_fun_growtable_iiio ((fun_table z x)) (v_n) (v_ref)).flatMap fun ⟨o_128, h_632⟩ => (match o_128 with
 | var_0 => ((if h_633 : (var_0 ≠ none) then
(((fun (ti : tableinst) (h_634 : ((Option.get! var_0) : tableinst) = ti) => (((interp_wf_tableinst_i ((Option.get! var_0))).flatMap fun ⟨_, h_635⟩ => (((interp_wf_tableinst_i ((fun_table z x))).flatMap fun ⟨_, h_636⟩ => (((interp_wf_config_i ((.mk_config z ([(instr_ref v_ref), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)] : (List instr))))).flatMap fun ⟨_, h_637⟩ => (((interp_wf_config_i ((.mk_config (with_tableinst z x ti) ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (List.length ((fun_table z x).REFS)))))] : (List instr))))).flatMap fun ⟨_, h_638⟩ => ((if h_639 : (((((fof z).MODULE).TABLES)[(proj_uN_0 x)]!) < (List.length ((sof z).TABLES))) then
((if h_640 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).TABLES))) then
([⟨(.mk_config (with_tableinst z x ti) ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (List.length ((fun_table z x).REFS)))))] : (List instr))), by subst_vars; first | (apply Step.table_grow_succeed <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.table_grow_succeed]⟩])
else []))
else []))))))))))) ((Option.get! var_0) : tableinst) rfl))
else [])))))
 | none => []))
else []))
 | _ => []

partial def interp_Step_io_table_grow_fail (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [y_129, (.CONST y_130 (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)]) => ((if h_641 : (y_130 = (numtype_addrtype «at»)) then
((match interp_inv_instr_ref y_129 with
 | some ⟨v_ref, h_642⟩ => (((interp_fun_inv_signed__iio ((size (numtype_addrtype «at»))) ((0 - (Int.ofNat 1)))).flatMap fun ⟨o_131, h_643⟩ => (match o_131 with
 | var_0 => (((interp_wf_config_i ((.mk_config z ([(instr_ref v_ref), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)] : (List instr))))).flatMap fun ⟨_, h_644⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))] : (List instr))))).flatMap fun ⟨_, h_645⟩ => ([⟨(.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))] : (List instr))), by subst_vars; first | (apply Step.table_grow_fail <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.table_grow_fail]⟩]))))))))
 | none => []))
else []))
 | _ => []

partial def interp_Step_io_elem_drop (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.ELEM_DROP x)]) => (((interp_wf_config_i ((.mk_config z ([(.ELEM_DROP x)] : (List instr))))).flatMap fun ⟨_, h_646⟩ => (((interp_wf_config_i ((.mk_config (with_elem z x []) []))).flatMap fun ⟨_, h_647⟩ => ((if h_648 : (((((fof z).MODULE).ELEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).ELEMS))) then
((if h_649 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).ELEMS))) then
([⟨(.mk_config (with_elem z x []) []), by subst_vars; first | (apply Step.elem_drop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.elem_drop]⟩])
else []))
else []))))))
 | _ => []

partial def interp_Step_io_store_num_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_132 i), (.CONST nt c), (.STORE y_133 none x ao)]) => ((if h_650 : (y_133 = nt) then
((if h_651 : ((proj_num__0 i) ≠ none) then
((if h_652 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_132 with
 | some ⟨«at», h_653⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_654⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST nt c), (.STORE nt none x ao)] : (List instr))))).flatMap fun ⟨_, h_655⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_656⟩ => ((if h_657 : ((((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_658 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_659 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_660 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.store_num_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.store_num_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

partial def interp_Step_io_store_num_val (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_134 i), (.CONST nt c), (.STORE y_135 none x ao)]) => ((if h_661 : (y_135 = nt) then
((if h_662 : ((proj_num__0 i) ≠ none) then
((match interp_inv_numtype_addrtype y_134 with
 | some ⟨«at», h_663⟩ => (((fun (b_lst : (List byte)) (h_664 : ((nbytes_ nt c) : (List byte)) = b_lst) => (((interp_allL (fun (iter : byte) => (interp_wf_byte_i (iter))) (nbytes_ nt c)).flatMap fun ⟨_, h_665⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST nt c), (.STORE nt none x ao)] : (List instr))))).flatMap fun ⟨_, h_666⟩ => (((interp_wf_config_i ((.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []))).flatMap fun ⟨_, h_667⟩ => ((if h_668 : ((((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_669 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_670 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_671 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8))))) ≤ (List.length ((((sof z).MEMS)[((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!)]!).BYTES))) then
((if h_672 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []), by subst_vars; first | (apply Step.store_num_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.store_num_val]⟩])
else []))
else []))
else []))
else []))
else []))))))))) ((nbytes_ nt c) : (List byte)) rfl))
 | none => []))
else []))
else []))
 | _ => []

partial def interp_Step_io_store_pack_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_136 i), (.CONST y_137 c), (.STORE y_138 (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)]) => ((if h_673 : (y_137 = (numtype_addrtype v_Inn)) then
((if h_674 : (y_138 = (numtype_addrtype v_Inn)) then
((if h_675 : ((proj_num__0 i) ≠ none) then
((if h_676 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_136 with
 | some ⟨«at», h_677⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_678⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST (numtype_addrtype v_Inn) c), (.STORE (numtype_addrtype v_Inn) (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)] : (List instr))))).flatMap fun ⟨_, h_679⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_680⟩ => ((if h_681 : ((((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_682 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_683 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_684 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.store_pack_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.store_pack_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

partial def interp_Step_io_store_pack_val (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_139 i), (.CONST y_140 c), (.STORE y_141 (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)]) => ((if h_685 : (y_140 = (numtype_addrtype v_Inn)) then
((if h_686 : (y_141 = (numtype_addrtype v_Inn)) then
((if h_687 : ((proj_num__0 i) ≠ none) then
((if h_688 : ((proj_num__0 c) ≠ none) then
((match interp_inv_numtype_addrtype y_139 with
 | some ⟨«at», h_689⟩ => (((fun (b_lst : (List byte)) (h_690 : ((ibytes_ v_n (wrap__ (size (numtype_addrtype v_Inn)) v_n (Option.get! (proj_num__0 c)))) : (List byte)) = b_lst) => (((interp_allL (fun (iter : byte) => (interp_wf_byte_i (iter))) (ibytes_ v_n (wrap__ (size (numtype_addrtype v_Inn)) v_n (Option.get! (proj_num__0 c))))).flatMap fun ⟨_, h_691⟩ => (((interp_wf_uN_ii (v_n) ((wrap__ (size (numtype_addrtype v_Inn)) v_n (Option.get! (proj_num__0 c))))).flatMap fun ⟨_, h_692⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.CONST (numtype_addrtype v_Inn) c), (.STORE (numtype_addrtype v_Inn) (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)] : (List instr))))).flatMap fun ⟨_, h_693⟩ => (((interp_wf_config_i ((.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []))).flatMap fun ⟨_, h_694⟩ => ((if h_695 : ((((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_696 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_697 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_698 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8))))) ≤ (List.length ((((sof z).MEMS)[((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!)]!).BYTES))) then
((if h_699 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []), by subst_vars; first | (apply Step.store_pack_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.store_pack_val]⟩])
else []))
else []))
else []))
else []))
else []))))))))))) ((ibytes_ v_n (wrap__ (size (numtype_addrtype v_Inn)) v_n (Option.get! (proj_num__0 c)))) : (List byte)) rfl))
 | none => []))
else []))
else []))
else []))
else []))
 | _ => []

partial def interp_Step_io_vstore_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_142 i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) => ((if h_700 : ((proj_num__0 i) ≠ none) then
((if h_701 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))))) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_142 with
 | some ⟨«at», h_702⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_703⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE .V128 x ao)] : (List instr))))).flatMap fun ⟨_, h_704⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_705⟩ => ((if h_706 : ((((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_707 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_708 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_709 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.vstore_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.vstore_oob]⟩])
else []))
else []))
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

partial def interp_Step_io_vstore_val (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_143 i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) => ((if h_710 : ((proj_num__0 i) ≠ none) then
((match interp_inv_numtype_addrtype y_143 with
 | some ⟨«at», h_711⟩ => (((fun (b_lst : (List byte)) (h_712 : ((vbytes_ .V128 c) : (List byte)) = b_lst) => (((interp_allL (fun (iter : byte) => (interp_wf_byte_i (iter))) (vbytes_ .V128 c)).flatMap fun ⟨_, h_713⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE .V128 x ao)] : (List instr))))).flatMap fun ⟨_, h_714⟩ => (((interp_wf_config_i ((.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []))).flatMap fun ⟨_, h_715⟩ => ((if h_716 : ((((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8)))) then
((if h_717 : ((Rat.ofInt (Int.ofNat 8)) ≠ 0) then
((if h_718 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_719 : (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8))))) ≤ (List.length ((((sof z).MEMS)[((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!)]!).BYTES))) then
((if h_720 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8))))) b_lst) []), by subst_vars; first | (apply Step.vstore_val <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.vstore_val]⟩])
else []))
else []))
else []))
else []))
else []))))))))) ((vbytes_ .V128 c) : (List byte)) rfl))
 | none => []))
else []))
 | _ => []

partial def interp_Step_io_vstore_lane_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_144 i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) x ao j)]) => ((if h_721 : ((proj_num__0 i) ≠ none) then
((if h_722 : ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + v_N) > (List.length ((fun_mem z x).BYTES))) then
((match interp_inv_numtype_addrtype y_144 with
 | some ⟨«at», h_723⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_724⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) x ao j)] : (List instr))))).flatMap fun ⟨_, h_725⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_726⟩ => ((if h_727 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_728 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.vstore_lane_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.vstore_lane_oob]⟩])
else []))
else []))))))))
 | none => []))
else []))
else []))
 | _ => []

partial def interp_Step_io_memory_grow_succeed (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_146 (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)]) => ((if h_800 : (y_146 = (numtype_addrtype «at»)) then
(((interp_fun_growmem_iio ((fun_mem z x)) (v_n)).flatMap fun ⟨o_147, h_801⟩ => (match o_147 with
 | var_0 => ((if h_802 : (var_0 ≠ none) then
(((fun (mi : meminst) (h_803 : ((Option.get! var_0) : meminst) = mi) => (((interp_wf_meminst_i ((Option.get! var_0))).flatMap fun ⟨_, h_804⟩ => (((interp_wf_meminst_i ((fun_mem z x))).flatMap fun ⟨_, h_805⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)] : (List instr))))).flatMap fun ⟨_, h_806⟩ => (((interp_wf_config_i ((.mk_config (with_meminst z x mi) ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (List.length ((fun_mem z x).BYTES)))) / (Rat.ofInt (Int.ofNat (64 * (Ki ))))))))))] : (List instr))))).flatMap fun ⟨_, h_807⟩ => ((if h_808 : (((((fof z).MODULE).MEMS)[(proj_uN_0 x)]!) < (List.length ((sof z).MEMS))) then
((if h_809 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).MEMS))) then
((if h_810 : ((((Rat.ofInt (Int.ofNat (List.length ((fun_mem z x).BYTES)))) / (Rat.ofInt (Int.ofNat (64 * (Ki )))))).den = 1 ∧ 0 ≤ ((Rat.ofInt (Int.ofNat (List.length ((fun_mem z x).BYTES)))) / (Rat.ofInt (Int.ofNat (64 * (Ki )))))) then
((if h_811 : ((Rat.ofInt (Int.ofNat (64 * (Ki )))) ≠ 0) then
([⟨(.mk_config (with_meminst z x mi) ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (List.length ((fun_mem z x).BYTES)))) / (Rat.ofInt (Int.ofNat (64 * (Ki ))))))))))] : (List instr))), by subst_vars; first | (apply Step.memory_grow_succeed <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.memory_grow_succeed]⟩])
else []))
else []))
else []))
else []))))))))))) ((Option.get! var_0) : meminst) rfl))
else [])))))
else []))
 | _ => []

partial def interp_Step_io_memory_grow_fail (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.CONST y_148 (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)]) => ((if h_812 : (y_148 = (numtype_addrtype «at»)) then
(((interp_fun_inv_signed__iio ((size (numtype_addrtype «at»))) ((0 - (Int.ofNat 1)))).flatMap fun ⟨o_149, h_813⟩ => (match o_149 with
 | var_0 => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)] : (List instr))))).flatMap fun ⟨_, h_814⟩ => (((interp_wf_config_i ((.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))] : (List instr))))).flatMap fun ⟨_, h_815⟩ => ([⟨(.mk_config z ([(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))] : (List instr))), by subst_vars; first | (apply Step.memory_grow_fail <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.memory_grow_fail]⟩]))))))))
else []))
 | _ => []

partial def interp_Step_io_data_drop (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.DATA_DROP x)]) => (((interp_wf_config_i ((.mk_config z ([(.DATA_DROP x)] : (List instr))))).flatMap fun ⟨_, h_816⟩ => (((interp_wf_config_i ((.mk_config (with_data z x []) []))).flatMap fun ⟨_, h_817⟩ => ((if h_818 : (((((fof z).MODULE).DATAS)[(proj_uN_0 x)]!) < (List.length ((sof z).DATAS))) then
((if h_819 : ((proj_uN_0 x) < (List.length (((fof z).MODULE).DATAS))) then
([⟨(.mk_config (with_data z x []) []), by subst_vars; first | (apply Step.data_drop <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.data_drop]⟩])
else []))
else []))))))
 | _ => []

partial def interp_Step_io_struct_set_null (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, y_156, (.STRUCT_SET x i)]) => ((match interp_inv_instr_val y_156 with
 | some ⟨v_val, h_876⟩ => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (instr_val v_val), (.STRUCT_SET x i)] : (List instr))))).flatMap fun ⟨_, h_877⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_878⟩ => ([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.struct_set_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.struct_set_null]⟩])))))
 | none => []))
 | _ => []

partial def interp_Step_io_array_set_null (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [.REF_NULL_ADDR, (.CONST .I32 i), y_167, (.ARRAY_SET x)]) => ((match interp_inv_instr_val y_167 with
 | some ⟨v_val, h_948⟩ => (((interp_wf_config_i ((.mk_config z ([.REF_NULL_ADDR, (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)] : (List instr))))).flatMap fun ⟨_, h_949⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_950⟩ => ([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.array_set_null <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.array_set_null]⟩])))))
 | none => []))
 | _ => []

partial def interp_Step_io_array_set_oob (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), y_168, (.ARRAY_SET x)]) => ((if h_951 : ((proj_num__0 i) ≠ none) then
((if h_952 : (a < (List.length (fun_arrayinst z))) then
((if h_953 : ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length (((fun_arrayinst z)[a]!).FIELDS))) then
((match interp_inv_instr_val y_168 with
 | some ⟨v_val, h_954⟩ => (((interp_allL (fun (iter : arrayinst) => (interp_wf_arrayinst_i (iter))) (fun_arrayinst z)).flatMap fun ⟨_, h_955⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)] : (List instr))))).flatMap fun ⟨_, h_956⟩ => (((interp_wf_config_i ((.mk_config z ([.TRAP] : (List instr))))).flatMap fun ⟨_, h_957⟩ => ([⟨(.mk_config z ([.TRAP] : (List instr))), by subst_vars; first | (apply Step.array_set_oob <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.array_set_oob]⟩])))))))
 | none => []))
else []))
else []))
else []))
 | _ => []

partial def interp_Step_io_array_set_array (a0 : config) : List {o : config // (Step a0 o)} :=
  match a0 with
 | (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), y_169, (.ARRAY_SET x)]) => ((if h_958 : ((proj_num__0 i) ≠ none) then
((match interp_inv_instr_val y_169 with
 | some ⟨v_val, h_959⟩ => (((interp_fun_type_iio (z) (x)).flatMap fun ⟨o_170, h_960⟩ => (match o_170 with
 | var_0 => (((interp_Expand_io (var_0)).flatMap fun ⟨o_171, h_962⟩ => (match o_171 with
 | (.ARRAY (.mk_fieldtype mut_opt zt)) => ((if h_963 : ((packfield_ zt v_val) ≠ none) then
(((interp_wf_deftype_i (var_0)).flatMap fun ⟨_, h_964⟩ => (((interp_wf_config_i ((.mk_config z ([(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)] : (List instr))))).flatMap fun ⟨_, h_965⟩ => (((interp_wf_config_i ((.mk_config (with_array z a (proj_uN_0 (Option.get! (proj_num__0 i))) (Option.get! (packfield_ zt v_val))) []))).flatMap fun ⟨_, h_966⟩ => (((interp_wf_comptype_i ((.ARRAY (.mk_fieldtype mut_opt zt)))).flatMap fun ⟨_, h_967⟩ => ((if h_968 : (a < (List.length ((sof z).ARRAYS))) then
((if h_969 : ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((((sof z).ARRAYS)[a]!).FIELDS))) then
([⟨(.mk_config (with_array z a (proj_uN_0 (Option.get! (proj_num__0 i))) (Option.get! (packfield_ zt v_val))) []), by subst_vars; first | (apply Step.array_set_array <;> first | assumption | rfl | (apply Eq.symm; assumption) | exact default | (and_intros <;> first | assumption | rfl | (apply Eq.symm; assumption))) | solve_by_elim [Step.array_set_array]⟩])
else []))
else []))))))))))
else []))
 | _ => []))))))
 | none => []))
else []))
 | _ => []

partial def interp_Step_io (a0 : config) : List {o : config // (Step a0 o)} :=
  interp_Step_io_pure a0 ++
  interp_Step_io_read a0 ++
  interp_Step_io_ctxt_instrs a0 ++
  interp_Step_io_ctxt_label a0 ++
  interp_Step_io_ctxt_handler a0 ++
  interp_Step_io_ctxt_frame a0 ++
  interp_Step_io_throw a0 ++
  interp_Step_io_local_set a0 ++
  interp_Step_io_global_set a0 ++
  interp_Step_io_table_set_oob a0 ++
  interp_Step_io_table_set_val a0 ++
  interp_Step_io_table_grow_succeed a0 ++
  interp_Step_io_table_grow_fail a0 ++
  interp_Step_io_elem_drop a0 ++
  interp_Step_io_store_num_oob a0 ++
  interp_Step_io_store_num_val a0 ++
  interp_Step_io_store_pack_oob a0 ++
  interp_Step_io_store_pack_val a0 ++
  interp_Step_io_vstore_oob a0 ++
  interp_Step_io_vstore_val a0 ++
  interp_Step_io_vstore_lane_oob a0 ++
  interp_Step_io_memory_grow_succeed a0 ++
  interp_Step_io_memory_grow_fail a0 ++
  interp_Step_io_data_drop a0 ++
  interp_Step_io_struct_set_null a0 ++
  interp_Step_io_array_set_null a0 ++
  interp_Step_io_array_set_oob a0 ++
  interp_Step_io_array_set_array a0

end

/- 1018 rules compiled, 95 left out:
Step_pure (io) vtestop: no premise is ready: ((proj_num__0 c) ≠ none); ((proj_uN_0 (Option.get! (proj_num__0 c))) = var_0); (wf_instr (.CONST .I32 c))
Step_pure (io) vsplat: no premise is ready: ((lpacknum_ v_Lnn c_1) ≠ none)
Step (io) vstore_lane_val: no premise is ready: (v_N = (jsize v_Jnn)); ((Rat.ofInt (Int.ofNat v_M)) = ((Rat.ofInt (Int.ofNat 128)) / (Rat.ofInt (Int.ofNat v_N)))); ((proj_lane__0 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!)) ≠ none); ((proj_uN_0 j) < (List.length (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c))); (b_lst = (ibytes_ v_N (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!))))))); Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_N (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!)))))); (wf_config (.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8))))) b_lst) [])); (wf_uN v_N (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!))))))
Step (io) struct_new: no premise is ready: y_155 = (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst); Forall₂ (fun (v_val : val) (zt : storagetype) => ((packfield_ zt v_val) ≠ none)) val_lst zt_lst; (si = { TYPE := var_0, FIELDS := (List.zipWith (fun (v_val : val) (zt : storagetype) => (Option.get! (packfield_ zt v_val))) val_lst zt_lst) }); (wf_config (.mk_config (add_structinst z ([si] : (List structinst))) ([(.REF_STRUCT_ADDR a)] : (List instr)))); (wf_comptype (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst)))); (wf_structinst { TYPE := var_0, FIELDS := (List.zipWith (fun (v_val : val) (zt : storagetype) => (Option.get! (packfield_ zt v_val))) val_lst zt_lst) }); (v_n = (List.length mut_opt_lst)); (v_n = (List.length zt_lst))
Step (io) struct_set_struct: no premise is ready: y_160 = (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst); ((packfield_ (zt_lst[(proj_uN_0 i)]!) v_val) ≠ none); ((proj_uN_0 i) < (List.length zt_lst)); (wf_config (.mk_config (with_struct z a (proj_uN_0 i) (Option.get! (packfield_ (zt_lst[(proj_uN_0 i)]!) v_val))) [])); (wf_comptype (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst))))
Step (io) array_new_fixed: no premise is ready: Forall (fun (v_val : val) => ((packfield_ zt v_val) ≠ none)) val_lst
fun_unop_ (iiio) fun_unop__case_22: negated premise
fun_binop_ (iiiio) fun_binop__case_38: negated premise
fun_cvtop__ (iiiio) fun_cvtop___case_36: negated premise
fun_vunop_ (iiio) fun_vunop__case_26: negated premise
fun_vbinop_ (iiiio) fun_vbinop__case_60: negated premise
fun_vternop_ (iiiiio) fun_vternop__case_8: negated premise
fun_vrelop_ (iiiio) fun_vrelop__case_36: negated premise
fun_vshiftop_ (iiiio) fun_vshiftop__case_8: negated premise
fun_vswizzlop_ (iiiio) fun_vswizzlop__case_2: negated premise
fun_vextunop__ (iiiio) fun_vextunop___case_16: negated premise
fun_vextbinop__ (iiiiio) fun_vextbinop___case_48: negated premise
fun_vextternop__ (iiiiiio) fun_vextternop___case_0: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I32)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_1: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I64)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_2: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I8)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_3: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I16)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_4: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I32)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_5: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I64)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_6: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I8)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_7: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I16)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_8: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I32)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_9: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I64)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_10: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I8)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_11: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I16)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_12: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I32)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_13: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I64)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_14: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I8)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_15: no premise is ready: (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2); (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1); (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0); ((jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn .I16)))); (c' = (Option.get! var_0)); (c'' = (Option.get! var_1)); (c ∈ (Option.get! var_2)); (wf_ishape (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))); (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)); (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)))
fun_vextternop__ (iiiiiio) fun_vextternop___case_16: negated premise
fun_vcvtop__ (iiiio) fun_vcvtop___case_0: no premise is ready: Forall₂ (fun (var_2 : (Option (List lane_))) (c_1_142 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) vcvtop c_1_142 var_2)) var_2_lst c_1_lst; (c_lst_lst = (setproduct_ lane_ (List.map (fun (var_2 : (Option (List lane_))) => (Option.get! var_2)) var_2_lst))); (v ∈ (List.map (fun (c_lst_30 : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim v_M)) c_lst_30)) c_lst_lst))
fun_vcvtop__ (iiiio) fun_vcvtop___case_1: no premise is ready: Forall₂ (fun (var_1 : (Option (List lane_))) (c_1_144 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop c_1_144 var_1)) var_1_lst c_1_lst; (c_lst_lst = (setproduct_ lane_ (List.map (fun (var_1 : (Option (List lane_))) => (Option.get! var_1)) var_1_lst))); (v ∈ (List.map (fun (c_lst_32 : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst_32)) c_lst_lst))
fun_vcvtop__ (iiiio) fun_vcvtop___case_2: no premise is ready: Forall₂ (fun (var_1 : (Option (List lane_))) (c_1_146 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop c_1_146 var_1)) var_1_lst c_1_lst; (c_lst_lst = (setproduct_ lane_ ((List.map (fun (var_1 : (Option (List lane_))) => (Option.get! var_1)) var_1_lst) ++ (List.replicate M_1 ([var_2] : (List lane_)))))); (v ∈ (List.map (fun (c_lst_34 : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst_34)) c_lst_lst))
fun_vcvtop__ (iiiio) fun_vcvtop___case_3: negated premise
Step_read (io) br_on_cast_fail: negated premise
Step_read (io) br_on_cast_fail_fail: negated premise
Step_read (io) call_ref_func: no premise is ready: Forall₂ (fun (var_0 : (Option (Option val))) (t : valtype) => (fun_default_ t var_0)) var_0_lst t_lst; ((fi.CODE) = (.FUNC x (List.map (fun (t : valtype) => ((.LOCAL t) : «local»)) t_lst) instr_lst)); Forall (fun (var_0 : (Option (Option val))) => (var_0 ≠ none)) var_0_lst; (f = { LOCALS := ((List.map (fun (v_val : val) => (some v_val)) val_lst) ++ (List.map (fun (var_0 : (Option (Option val))) => (Option.get! var_0)) var_0_lst)), MODULE := (fi.MODULE) }); (wf_instr (.FRAME_ v_m f ([(.LABEL_ v_m [] instr_lst)] : (List instr)))); (wf_funccode (.FUNC x (List.map (fun (t : valtype) => ((.LOCAL t) : «local»)) t_lst) instr_lst)); (wf_frame { LOCALS := ((List.map (fun (v_val : val) => (some v_val)) val_lst) ++ (List.map (fun (var_0 : (Option (Option val))) => (Option.get! var_0)) var_0_lst)), MODULE := (fi.MODULE) })
Step_read (io) throw_ref_handler_next: negated premise
Step_read (io) table_copy_zero: negated premise
Step_read (io) table_copy_le: negated premise
Step_read (io) table_copy_gt: negated premise
Step_read (io) load_num_val: no premise is ready: ((nbytes_ nt c) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (size nt))) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); Forall (fun (iter : byte) => (wf_byte iter)) (nbytes_ nt c); (wf_instr (.CONST nt c))
Step_read (io) load_pack_val: no premise is ready: ((ibytes_ v_n c) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_n)) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_n c); (wf_instr (.CONST (numtype_addrtype v_Inn) (.mk_num__0 v_Inn (extend__ v_n (size (numtype_addrtype v_Inn)) v_sx c))))
Step_read (io) vload_val: no premise is ready: ((vbytes_ .V128 c) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); Forall (fun (iter : byte) => (wf_byte iter)) (vbytes_ .V128 c); (wf_instr (.VCONST .V128 c))
Step_read (io) vload_pack_val: no premise is ready: (∀ (k : Nat), k < v_K → ((proj_num__0 i) ≠ none)); (∀ (k : Nat), k < v_K → let j : iN := (j_lst)[k]!; ((ibytes_ v_M j) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_M)) / (Rat.ofInt (Int.ofNat 8))))) (List.drop (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (k * v_M))) / (Rat.ofInt (Int.ofNat 8)))))) ((fun_mem z x).BYTES))))); (c = (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K)) (List.map (fun (j : iN) => ((.mk_lane__0 v_Jnn (extend__ v_M (jsizenn v_Jnn) v_sx j)) : lane_)) j_lst))); ((jsizenn v_Jnn) = (v_M * 2)); (∀ (k : Nat), k < v_K → let j : iN := (j_lst)[k]!; Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_M j)); (wf_uN 128 (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K)) (List.map (fun (j : iN) => ((.mk_lane__0 v_Jnn (extend__ v_M (jsizenn v_Jnn) v_sx j)) : lane_)) j_lst))); (wf_instr (.VCONST .V128 c)); (wf_shape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K))); Forall (fun (j : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K))) (.mk_lane__0 v_Jnn (extend__ v_M (jsizenn v_Jnn) v_sx j)))) j_lst; (v_K = (List.length j_lst))
Step_read (io) vload_splat_val: no premise is ready: ((ibytes_ v_N j) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); (v_N = (jsize v_Jnn)); ((Rat.ofInt (Int.ofNat v_M)) = ((Rat.ofInt (Int.ofNat 128)) / (Rat.ofInt (Int.ofNat v_N)))); (c = (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.replicate v_M (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 j)))))); Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_N j); (wf_uN 128 (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.replicate v_M (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 j)))))); (wf_instr (.VCONST .V128 c)); (wf_shape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))); (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 j))))
Step_read (io) vload_zero_val: no premise is ready: ((ibytes_ v_N j) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); (c = (extend__ v_N 128 .U j)); (wf_uN v_N j); Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_N j); (wf_uN 128 (extend__ v_N 128 .U j)); (wf_instr (.VCONST .V128 c))
Step_read (io) vload_lane_val: no premise is ready: ((ibytes_ v_N k) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat v_N)) / (Rat.ofInt (Int.ofNat 8))))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z x).BYTES)))); (v_N = (jsize v_Jnn)); ((Rat.ofInt (Int.ofNat v_M)) = ((Rat.ofInt (Int.ofNat (vsize .V128))) / (Rat.ofInt (Int.ofNat v_N)))); (c = (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.modify (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1) (proj_uN_0 j) (fun (_ : lane_) => (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 k))))))); Forall (fun (iter : byte) => (wf_byte iter)) (ibytes_ v_N k); (wf_uN 128 (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.modify (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1) (proj_uN_0 j) (fun (_ : lane_) => (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 k))))))); Forall (fun (iter : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) iter)) (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1); (wf_instr (.VCONST .V128 c)); (wf_shape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))); (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__0 v_Jnn (.mk_uN (proj_uN_0 k))))
Step_read (io) memory_size: no premise is ready: ((v_n * (64 * (Ki ))) = (List.length ((fun_mem z x).BYTES))); (wf_instr (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))))
Step_read (io) ref_test_false: negated premise
Step_read (io) ref_cast_fail: negated premise
Step_read (io) struct_new_default: no premise is ready: y_318 = (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst); Forall₂ (fun (var_1 : (Option (Option val))) (zt : storagetype) => (fun_default_ (unpack zt) var_1)) var_1_lst zt_lst; ((List.length val_lst) = (List.length zt_lst)); Forall (fun (var_1 : (Option (Option val))) => (var_1 ≠ none)) var_1_lst; Forall₂ (fun (var_1 : (Option (Option val))) (v_val : val) => ((Option.get! var_1) = (some v_val))) var_1_lst val_lst; Forall (fun (v_val : val) => (wf_val v_val)) val_lst; Forall (fun (var_1 : (Option (Option val))) => Forall (fun (iter : val) => (wf_val iter)) (Option.toList (Option.get! var_1))) var_1_lst; Forall (fun (zt : storagetype) => (wf_valtype (unpack zt))) zt_lst; (wf_comptype (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst))))
Step_read (io) struct_get_struct: no premise is ready: y_321 = (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst); ((unpackfield_ (zt_lst[(proj_uN_0 i)]!) sx_opt ((((fun_structinst z)[a]!).FIELDS)[(proj_uN_0 i)]!)) ≠ none); ((proj_uN_0 i) < (List.length zt_lst)); (wf_val (Option.get! (unpackfield_ (zt_lst[(proj_uN_0 i)]!) sx_opt ((((fun_structinst z)[a]!).FIELDS)[(proj_uN_0 i)]!)))); (wf_comptype (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => ((.mk_fieldtype mut_opt zt) : fieldtype)) mut_opt_lst zt_lst))))
Step_read (io) array_new_data_num: no premise is ready: Forall (fun (c : lit_) => ((const (Option.get! (cunpack zt)) (Option.get! (cunpacknum_ zt c))) ≠ none)) c_lst; ((cunpack zt) ≠ none); Forall (fun (c : lit_) => ((cunpacknum_ zt c) ≠ none)) c_lst; ((concatn_ byte (List.map (fun (c : lit_) => (zbytes_ zt c)) c_lst) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (Option.get! (zsize zt)))) / (Rat.ofInt (Int.ofNat 8)))))) = (List.take (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (v_n * (Option.get! (zsize zt))))) / (Rat.ofInt (Int.ofNat 8))))) (List.drop (proj_uN_0 (Option.get! (proj_num__0 i))) ((fun_data z y).BYTES)))); Forall (fun (c : lit_) => (wf_lit_ zt c)) c_lst; Forall (fun (c : lit_) => (wf_instr (Option.get! (const (Option.get! (cunpack zt)) (Option.get! (cunpacknum_ zt c)))))) c_lst; Forall (fun (c : lit_) => (wf_lit_ (storagetype_consttype (Option.get! (cunpack zt))) (Option.get! (cunpacknum_ zt c)))) c_lst; Forall (fun (iter : byte) => (wf_byte iter)) (concatn_ byte (List.map (fun (c : lit_) => (zbytes_ zt c)) c_lst) (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (Option.get! (zsize zt)))) / (Rat.ofInt (Int.ofNat 8)))))); Forall (fun (c : lit_) => Forall (fun (iter : byte) => (wf_byte iter)) (zbytes_ zt c)) c_lst; (v_n = (List.length c_lst))
Step_read (io) array_fill_zero: negated premise
Step_read (io) array_fill_succ: negated premise
Step_read (io) array_copy_zero: negated premise
Step_read (io) array_copy_le: negated premise
Step_read (io) array_copy_gt: negated premise
Step_read (io) array_init_elem_zero: negated premise
Step_read (io) array_init_elem_succ: negated premise
Step_read (io) array_init_data_zero: negated premise
Step_read (io) array_init_data_num: negated premise
fun_growtable (iiio) fun_growtable_case_0: no premise is ready: (tableinst' = { TYPE := (.mk_tabletype «at» (.mk_limits i' j_opt) rt), REFS := (r'_lst ++ (List.replicate v_n r)) }); ((proj_uN_0 i') = ((List.length r'_lst) + v_n)); Forall (fun (j_3 : u64) => ((proj_uN_0 i') <= (proj_uN_0 j_3))) (Option.toList j_opt); ((Int.ofNat (proj_uN_0 i')) <= ((Int.ofNat (2 ^ (size (numtype_addrtype «at»)))) - (Int.ofNat 1))); (wf_tableinst { TYPE := (.mk_tabletype «at» (.mk_limits i' j_opt) rt), REFS := (r'_lst ++ (List.replicate v_n r)) })
fun_growtable (iiio) fun_growtable_case_1: negated premise
fun_growmem (iio) fun_growmem_case_0: no premise is ready: (meminst' = { TYPE := (.PAGE «at» (.mk_limits i' j_opt)), BYTES := (b_lst ++ (List.replicate (v_n * (64 * (Ki ))) (.mk_byte 0))) }); ((Rat.ofInt (Int.ofNat (proj_uN_0 i'))) = (((Rat.ofInt (Int.ofNat (List.length b_lst))) / (Rat.ofInt (Int.ofNat (64 * (Ki ))))) + (Rat.ofInt (Int.ofNat v_n)))); Forall (fun (j_8 : u64) => ((proj_uN_0 i') <= (proj_uN_0 j_8))) (Option.toList j_opt); ((proj_uN_0 i') <= (2 ^ (Int.toNat ((Int.ofNat (size (numtype_addrtype «at»))) - (Int.ofNat 16))))); (wf_meminst { TYPE := (.PAGE «at» (.mk_limits i' j_opt)), BYTES := (b_lst ++ (List.replicate (v_n * (64 * (Ki ))) (.mk_byte 0))) })
fun_growmem (iio) fun_growmem_case_1: negated premise
wf_ishape (i) ishape_case_0: no premise is ready: ((fun_lanetype v_shape) = (lanetype_Jnn v_Jnn))
fun_ivbitmaskop_ (iio) fun_ivbitmaskop__case_0: no premise is ready: ((ibits_ 32 c) = ((List.map (fun (c_1_114 : lane_) => ((.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I32)) .S (Option.get! (proj_lane__0 c_1_114)) (.mk_uN 0)))) : bit)) c_1_lst) ++ (List.replicate (Int.toNat ((Int.ofNat 32) - (Int.ofNat v_M))) (.mk_bit 0))))
fun_ivbitmaskop_ (iio) fun_ivbitmaskop__case_1: no premise is ready: ((ibits_ 32 c) = ((List.map (fun (c_1_117 : lane_) => ((.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I64)) .S (Option.get! (proj_lane__0 c_1_117)) (.mk_uN 0)))) : bit)) c_1_lst) ++ (List.replicate (Int.toNat ((Int.ofNat 32) - (Int.ofNat v_M))) (.mk_bit 0))))
fun_ivbitmaskop_ (iio) fun_ivbitmaskop__case_2: no premise is ready: ((ibits_ 32 c) = ((List.map (fun (c_1_120 : lane_) => ((.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I8)) .S (Option.get! (proj_lane__0 c_1_120)) (.mk_uN 0)))) : bit)) c_1_lst) ++ (List.replicate (Int.toNat ((Int.ofNat 32) - (Int.ofNat v_M))) (.mk_bit 0))))
fun_ivbitmaskop_ (iio) fun_ivbitmaskop__case_3: no premise is ready: ((ibits_ 32 c) = ((List.map (fun (c_1_123 : lane_) => ((.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I16)) .S (Option.get! (proj_lane__0 c_1_123)) (.mk_uN 0)))) : bit)) c_1_lst) ++ (List.replicate (Int.toNat ((Int.ofNat 32) - (Int.ofNat v_M))) (.mk_bit 0))))
fun_zeroop (iiio) fun_zeroop_case_40: negated premise
fun_halfop (iiio) fun_halfop_case_40: negated premise
fun_default_ (io) fun_default__case_7: negated premise
fun_unrollrt (io) fun_unrollrt_case_0: no premise is ready: Forall₂ (fun (var_1 : subtype) (subtype_5 : subtype) => (fun_subst_subtype subtype_5 ((List.range v_n).map (fun (i_138938 : Nat) => ((.REC i_138938) : typevar))) ((List.range v_n).map (fun (i_138939 : Nat) => ((._DEF v_rectype i_138939) : typeuse))) var_1)) var_1_lst subtype_lst; Forall₂ (fun (var_0 : subtype) (v_subtype : subtype) => (fun_subst_subtype v_subtype ((List.range v_n).map (fun (i : Nat) => ((.REC i) : typevar))) ((List.range v_n).map (fun (i : Nat) => ((._DEF v_rectype i) : typeuse))) var_0)) var_0_lst subtype_lst; (wf_rectype (.REC (.mk_list var_1_lst)))
Heaptype_sub (iii) rec_sub: no premise is ready: y_382 = (heaptype_typeuse (typeuse_lst[j]!)); (j < (List.length typeuse_lst))
fun_subst_heaptype (iiio) fun_subst_heaptype_case_3: negated premise
Heaptype_ok (io) abs: output not determined
Deftype_sub (iii) super: no premise is ready: (i < (List.length typeuse_lst)); (Heaptype_sub C (heaptype_typeuse (typeuse_lst[i]!)) (heaptype_deftype deftype_2))
fun_utf8 (io) fun_utf8_case_0: no premise is ready: Forall₂ (fun (var_2 : (List byte)) (ch_3 : char) => (fun_utf8 ([ch_3] : (List char)) var_2)) var_2_lst ch_lst; Forall₂ (fun (var_1 : (List byte)) (ch_2 : char) => (fun_utf8 ([ch_2] : (List char)) var_1)) var_1_lst ch_lst; Forall₂ (fun (var_0 : (List byte)) (ch : char) => (fun_utf8 ([ch] : (List char)) var_0)) var_0_lst ch_lst; Forall (fun (iter_1 : byte) => (wf_byte iter_1)) (concat_ byte var_1_lst); Forall (fun (var_2 : (List byte)) => Forall (fun (iter_2 : byte) => (wf_byte iter_2)) var_2) var_2_lst
fun_utf8 (io) fun_utf8_case_2: no premise is ready: (fun_cont b_2 var_0); ((proj_char_0 ch) = (((2 ^ 6) * (Int.toNat ((Int.ofNat (proj_byte_0 b_1)) - (Int.ofNat 192)))) + var_0)); (wf_byte b_1); (wf_byte b_2)
fun_utf8 (io) fun_utf8_case_3: no premise is ready: (fun_cont b_3 var_1); (fun_cont b_2 var_0); ((proj_char_0 ch) = ((((2 ^ 12) * (Int.toNat ((Int.ofNat (proj_byte_0 b_1)) - (Int.ofNat 224)))) + ((2 ^ 6) * var_0)) + var_1)); (wf_byte b_1); (wf_byte b_2); (wf_byte b_3)
fun_utf8 (io) fun_utf8_case_4: no premise is ready: (fun_cont b_4 var_2); (fun_cont b_3 var_1); (fun_cont b_2 var_0); ((proj_char_0 ch) = (((((2 ^ 18) * (Int.toNat ((Int.ofNat (proj_byte_0 b_1)) - (Int.ofNat 240)))) + ((2 ^ 12) * var_0)) + ((2 ^ 6) * var_1)) + var_2)); (wf_byte b_1); (wf_byte b_2); (wf_byte b_3); (wf_byte b_4)
fun_subst_typevar (iiio) fun_subst_typevar_case_2: negated premise
Typeuse_ok (io) typeidx: no premise is ready: ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))); (((C.TYPES)[(proj_uN_0 v_typeidx)]!) = dt); (wf_deftype dt); (wf_typeuse (._IDX v_typeidx))
Typeuse_ok (io) rec: no premise is ready: (i < (List.length (C.RECS))); (((C.RECS)[i]!) = st); (wf_subtype st); (wf_typeuse (.REC i))
fun_subst_rectype (iiio) fun_subst_rectype_case_0: no premise is ready: Forall₂ (fun (var_1 : subtype) (st_2 : subtype) => (fun_subst_subtype st_2 tv'_lst tu'_lst var_1)) var_1_lst st_lst; Forall₂ (fun (var_0 : subtype) (st : subtype) => (fun_subst_subtype st tv'_lst tu'_lst var_0)) var_0_lst st_lst; (wf_rectype (.REC (.mk_list var_1_lst)))
Deftype_ok (io) mk_Deftype_ok: no premise is ready: (Rectype_ok2 ({ TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := subtype_lst } ++ C) v_rectype (.OK 0)); (v_rectype = (.REC (.mk_list subtype_lst))); (i < v_n); (wf_deftype (._DEF v_rectype i)); (wf_context { TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [], RECS := subtype_lst }); (wf_rectype (.REC (.mk_list subtype_lst))); (v_n = (List.length subtype_lst))
fun_subst_all_deftype (iio) fun_subst_all_deftype_case_0: no premise is ready: (∀ (i_138933 : Nat), i_138933 < v_n → (wf_typevar (._IDX (.mk_uN i_138933))))
Subtype_ok2 (iii) mk_Subtype_ok2: no premise is ready: Forall₂ (fun (var_0 : subtype) (v_typeuse : typeuse) => (fun_unrollht_ C (heaptype_typeuse v_typeuse) var_0)) var_0_lst typeuse_lst; ((List.length comptype'_lst) = (List.length typeuse_lst)); ((List.length comptype'_lst) = (List.length typeuse'_lst_lst)); Forall₃ (fun (var_0 : subtype) (comptype' : comptype) (typeuse'_lst : (List typeuse)) => (var_0 = (.SUB none typeuse'_lst comptype'))) var_0_lst comptype'_lst typeuse'_lst_lst; Forall (fun (comptype' : comptype) => (Comptype_sub C v_comptype comptype')) comptype'_lst; Forall (fun (var_0 : subtype) => (wf_subtype var_0)) var_0_lst; Forall₂ (fun (comptype' : comptype) (typeuse'_lst : (List typeuse)) => (wf_subtype (.SUB none typeuse'_lst comptype'))) comptype'_lst typeuse'_lst_lst
-/
