import SpecTecWP.Locals
import SpecTecWP.Arith

/-!
# The view: typed values, locals and stack

A `VState` is a SpecTec state seen at the level of a Wasm program: the store, the module
instance of the frame, the locals, and the operand stack, top first. A value `V` carries its
type as its constructor; `i32` and `i64` values carry `UInt32` and `UInt64` payloads. A local
is `none` until a non-defaultable local is set.

`Rep s z vs` holds when the SpecTec state `z` with the operand stack `vs` represents `s`. For
`s = ⟨st, m, [some (.i32 a), none], [.i32 c]⟩`, `Rep s z vs` says that `z` has the store `st`,
the frame of `z` has the module instance `m` and the locals `[some (i32v (u a)), none]`, and
`vs = [i32v (u c)]`. Every well-formed state and stack has exactly one representation
(`Rep.exists`, `Rep.unique`, `Rep.functional`).

The `Std.WP.WP` instance on `List instr` has assertions over `VState`: `wp is Q E s` holds when
`Code.wp is` holds from the SpecTec state that represents `s`, for the postconditions `lift Q`
and `liftE E`. `transport` turns a triple into a `Code.wp` statement, and `wp_view_iff` states
that the view loses nothing: on a represented state, `Code.wp` with any postconditions is the
view `wp` of their pullbacks.
-/

namespace SpecTecWP

open Std.WP Lean.Order

/-- An `i32` value of the model. -/
abbrev i32v (x : uN) : val := .CONST .I32 (.mk_num__0 .I32 x)

/-- A Wasm value, with its type as its constructor. -/
inductive V where
  | i32 (a : UInt32)
  | i64 (a : UInt64)
  | f32 (x : fN)
  | f64 (x : fN)
  | vconst (t : vectype) (x : vec_)
  | refI31 (x : u31)
  | refNull
  | refStruct (a : structaddr)
  | refArray (a : arrayaddr)
  | refFunc (a : funcaddr)
  | refExn (a : exnaddr)
  | refHost (a : hostaddr)
  | refExtern (r : ref)
deriving DecidableEq

instance : Inhabited V := ⟨.i32 0⟩

/-- The payload of an `i32` value. -/
def V.asI32 : V → UInt32
  | .i32 a => a
  | _ => 0

@[simp, grind =] theorem V.asI32_i32 (a : UInt32) : (V.i32 a).asI32 = a := rfl

/-- The value of the model that a typed value stands for. -/
def V.enc : V → val
  | .i32 a => i32v (u a)
  | .i64 a => .CONST .I64 (.mk_num__0 .I64 (.mk_uN a.toNat))
  | .f32 x => .CONST .F32 (.mk_num__1 .F32 x)
  | .f64 x => .CONST .F64 (.mk_num__1 .F64 x)
  | .vconst t x => .VCONST t x
  | .refI31 x => .REF_I31_NUM x
  | .refNull => .REF_NULL_ADDR
  | .refStruct a => .REF_STRUCT_ADDR a
  | .refArray a => .REF_ARRAY_ADDR a
  | .refFunc a => .REF_FUNC_ADDR a
  | .refExn a => .REF_EXN_ADDR a
  | .refHost a => .REF_HOST_ADDR a
  | .refExtern r => .REF_EXTERN r

@[simp] theorem V.enc_i32 (a : UInt32) : (V.i32 a).enc = i32v (u a) := rfl

theorem V.enc_injective : Function.Injective V.enc := by
  intro v w h
  cases v <;> cases w <;> simp_all [V.enc, u, UInt32.toNat_inj, UInt64.toNat_inj]

/-- Every well-formed value of the model is the encoding of a typed value. -/
theorem V.exists_enc {v : val} (h : wf_val v) : ∃ w : V, w.enc = v := by
  cases h with
  | val_case_0 nt c hc =>
    cases hc with
    | num__case_0 Inn x hx heq =>
      subst heq
      obtain ⟨n⟩ := x
      cases hx with
      | uN_case_0 _ hb _ =>
        have hb := hb.2
        cases Inn with
        | I32 =>
          simp only [size, numtype_addrtype, Int.ofNat_eq_natCast] at hb
          have e : (UInt32.ofNat n).toNat = n := by simp; omega
          exact ⟨.i32 (UInt32.ofNat n), by simp only [V.enc, u, e]; rfl⟩
        | I64 =>
          simp only [size, numtype_addrtype, Int.ofNat_eq_natCast] at hb
          have e : (UInt64.ofNat n).toNat = n := by simp; omega
          exact ⟨.i64 (UInt64.ofNat n), by simp only [V.enc, e]; rfl⟩
    | num__case_1 Fnn x _ heq =>
      subst heq
      cases Fnn with
      | F32 => exact ⟨.f32 x, rfl⟩
      | F64 => exact ⟨.f64 x, rfl⟩
  | val_case_1 t x _ => exact ⟨.vconst t x, rfl⟩
  | val_case_2 x _ => exact ⟨.refI31 x, rfl⟩
  | val_case_3 => exact ⟨.refNull, rfl⟩
  | val_case_4 a => exact ⟨.refStruct a, rfl⟩
  | val_case_5 a => exact ⟨.refArray a, rfl⟩
  | val_case_6 a => exact ⟨.refFunc a, rfl⟩
  | val_case_7 a => exact ⟨.refExn a, rfl⟩
  | val_case_8 a => exact ⟨.refHost a, rfl⟩
  | val_case_9 r _ => exact ⟨.refExtern r, rfl⟩

/-- A SpecTec state seen at the level of a Wasm program. -/
structure VState where
  store : store
  inst : moduleinst
  locals : List (Option V)
  stack : List V

/-- The value of the local `i`, `none` when it is unset or out of range. -/
def VState.loc (s : VState) (i : Nat) : Option V := s.locals[i]!

attribute [grind =] VState.loc

/-- The state `z` agrees with `s` on the store, the module instance and the locals. -/
def RepF (s : VState) (z : state) : Prop :=
  sof z = s.store ∧ (fof z).MODULE = s.inst ∧
    (fof z).LOCALS = s.locals.map (Option.map V.enc)

/-- The SpecTec state `z` with the operand stack `vs` represents `s`. -/
def Rep (s : VState) (z : state) (vs : Stack) : Prop :=
  RepF s z ∧ vs = s.stack.map V.enc

theorem map_inj_of {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf h.1, map_inj_of hf h.2]

theorem option_map_injective {α β : Type} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [hf.eq_iff]

theorem Rep.unique {s s' : VState} {z : state} {vs : Stack} (h : Rep s z vs) (h' : Rep s' z vs) :
    s = s' := by
  obtain ⟨st, m, ls, stk⟩ := s
  obtain ⟨st', m', ls', stk'⟩ := s'
  obtain ⟨⟨hs, hm, hl⟩, hk⟩ := h
  obtain ⟨⟨hs', hm', hl'⟩, hk'⟩ := h'
  have e1 : st = st' := hs.symm.trans hs'
  have e2 : m = m' := hm.symm.trans hm'
  have e3 : ls = ls' := map_inj_of (option_map_injective V.enc_injective) (hl.symm.trans hl')
  have e4 : stk = stk' := map_inj_of V.enc_injective (hk.symm.trans hk')
  subst e1 e2 e3 e4
  rfl

/-- A `VState` has one representation. -/
theorem Rep.functional {s : VState} {z z' : state} {vs vs' : Stack} (h : Rep s z vs)
    (h' : Rep s z' vs') : z = z' ∧ vs = vs' := by
  obtain ⟨⟨hs, hm, hl⟩, hk⟩ := h
  obtain ⟨⟨hs', hm', hl'⟩, hk'⟩ := h'
  refine ⟨?_, hk.trans hk'.symm⟩
  obtain ⟨st, ⟨L, M⟩⟩ := z
  obtain ⟨st', ⟨L', M'⟩⟩ := z'
  simp only [sof, fof, fun_store, fun_frame] at hs hm hl hs' hm' hl'
  subst hs hm hl
  simp_all

theorem exists_map_of {α β : Type} (f : α → β) :
    ∀ (L : List β), (∀ x ∈ L, ∃ y, f y = x) → ∃ L' : List α, L'.map f = L
  | [], _ => ⟨[], rfl⟩
  | x :: L, h => by
    obtain ⟨y, hy⟩ := h x (List.mem_cons_self ..)
    obtain ⟨L', hL'⟩ := exists_map_of f L (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨y :: L', by simp [hy, hL']⟩

/-- Every well-formed state and stack has a representation. -/
theorem Rep.exists {z : state} {vs : Stack} (hz : wf_state z) (hvs : ∀ v ∈ vs, wf_val v) :
    ∃ s, Rep s z vs := by
  obtain ⟨stk, hstk⟩ := exists_map_of V.enc vs fun v hv => V.exists_enc (hvs v hv)
  cases hz with
  | state_case_0 st f _ hf =>
    cases hf with
    | frame_case_ L m hL _ =>
      obtain ⟨ls, hls⟩ := exists_map_of (Option.map V.enc) L fun o ho => by
        cases o with
        | none => exact ⟨none, rfl⟩
        | some v =>
          obtain ⟨w, hw⟩ := V.exists_enc (hL _ ho v (by simp))
          exact ⟨some w, by simp [hw]⟩
      exact ⟨⟨st, m, ls, stk⟩, ⟨rfl, rfl, hls.symm⟩, hstk.symm⟩

theorem Rep.stack {s : VState} {z : state} {vs : Stack} (st : List V) (h : Rep s z vs) :
    Rep { s with stack := st } z (st.map V.enc) :=
  ⟨h.1, rfl⟩

theorem Rep.get_local {s : VState} {z : state} {vs : Stack} {i : Nat} (h : Rep s z vs) :
    fun_local z (.mk_uN i) = (s.loc i).map V.enc := by
  simp only [fun_local, proj_uN_0, h.1.2.2, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    VState.loc]
  cases s.locals[i]? <;> rfl

theorem map_modify_const {α β : Type} (f : α → β) (a : α) :
    ∀ (L : List α) (i : Nat), (L.map f).modify i (fun _ => f a) = (L.set i a).map f
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | b :: L, i + 1 => by simp [map_modify_const f a L i]

theorem Rep.set_local {s : VState} {z : state} {vs : Stack} {i : Nat} (v : V) (h : Rep s z vs) :
    Rep { s with locals := s.locals.set i (some v) } (with_local z (.mk_uN i) v.enc) vs := by
  refine ⟨⟨(sof_with_local z _ _).trans h.1.1, ?_, ?_⟩, h.2⟩
  · have e : (fof (with_local z (.mk_uN i) v.enc)).MODULE = (fof z).MODULE := by
      simp [with_local, fof, fun_frame]
    rw [e, h.1.2.1]
  · have e : (fof (with_local z (.mk_uN i) v.enc)).LOCALS =
        (fof z).LOCALS.modify i (fun _ => some v.enc) := by
      simp [with_local, fof, fun_frame, proj_uN_0]
    rw [e, h.1.2.2]
    exact map_modify_const (Option.map V.enc) (some v) s.locals i

/-! ## Exits and the lifted postconditions -/

/-- An early exit of an instruction sequence. The values that the exit carries are the stack of
the `VState` in the exception postcondition. -/
inductive VExit where
  | br (l : Nat)
  | ret
  | throw (a : addr)
  | trap

abbrev VAssn := VState → Prop
abbrev VEAssn := VExit → VState → Prop

/-- The SpecTec assertion that holds when the represented `VState` satisfies `P`. -/
def lift (P : VAssn) : Assn := fun z vs => ∃ s, Rep s z vs ∧ P s

/-- The SpecTec exception postcondition that holds when the represented `VState` satisfies
`E`. -/
def liftE (E : VEAssn) : EAssn
  | .br (.mk_uN l) vs => fun z => ∃ s, Rep s z vs ∧ E (.br l) s
  | .ret vs => fun z => ∃ s, Rep s z vs ∧ E .ret s
  | .throw a => fun z => ∃ s, Rep s z [] ∧ E (.throw a) s
  | .trap => fun z => ∃ s, Rep s z [] ∧ E .trap s

/-- `lift P` holds of a SpecTec state that agrees with `s` and has the stack `st`, when `P`
holds of `s` with the stack `st`. -/
theorem lift_of {P : VAssn} {s : VState} {z : state} {vs : Stack} (st : List V)
    (hf : RepF s z) (hvs : vs = st.map V.enc) (hp : P { s with stack := st }) :
    ∃ s', Rep s' z vs ∧ P s' :=
  ⟨{ s with stack := st }, ⟨hf, hvs⟩, hp⟩

instance : WP (List instr) Unit VAssn VEAssn where
  trans is := ⟨fun Q E s => ∀ z vs, Rep s z vs → Code.wp is (lift (Q ())) (liftE E) z vs⟩
  trans_monotone is := by
    intro Q Q' E E' hE hQ s h z vs hr hwf
    refine Safe.mono ?_ ?_ (h z vs hr hwf)
    · rintro z vs ⟨s, hr, hq⟩
      exact ⟨s, hr, hQ () s hq⟩
    · intro e z he
      rcases e with ⟨⟨l⟩, vs⟩ | vs | a | _ <;> obtain ⟨s, hr, h⟩ := he <;> exact ⟨s, hr, hE _ s h⟩

theorem wp_view (is : List instr) (Q : Unit → VAssn) (E : VEAssn) :
    Std.WP.wp is Q E = fun s => ∀ z vs, Rep s z vs → Code.wp is (lift (Q ())) (liftE E) z vs :=
  rfl

/-- A triple over the view holds of the SpecTec model, from the represented state. -/
theorem transport {c : List instr} {P : VAssn} {Q : Unit → VAssn} {E : VEAssn}
    (h : Triple c P Q E) {s : VState} {z : state} {vs : Stack} (hr : Rep s z vs) (hp : P s) :
    Code.wp c (lift (Q ())) (liftE E) z vs :=
  Triple.iff.mp h s hp z vs hr

/-! ## The view loses nothing -/

/-- The view assertion of a SpecTec assertion. -/
def pull (Q : Assn) : VAssn := fun s => ∀ z vs, Rep s z vs → Q z vs

/-- The view exception postcondition of a SpecTec exception postcondition. -/
def pullE (E : EAssn) : VEAssn
  | .br l => fun s => ∀ z vs, Rep s z vs → E (.br (.mk_uN l) vs) z
  | .ret => fun s => ∀ z vs, Rep s z vs → E (.ret vs) z
  | .throw a => fun s => ∀ z vs, Rep s z vs → E (.throw a) z
  | .trap => fun s => ∀ z vs, Rep s z vs → E .trap z

theorem wf_of_code {z : state} {vs : Stack} {is : List instr}
    (h : wf_config (.mk_config z (code vs is))) : wf_state z ∧ ∀ v ∈ vs, wf_val v := by
  obtain ⟨hz, hi⟩ := wf_config_iff.mp h
  refine ⟨hz, fun v hv => wf_val_of_wf_instr (hi _ ?_)⟩
  simp only [code_eq, List.mem_append, List.mem_map, List.mem_reverse]
  exact .inl ⟨v, hv, rfl⟩

/-- A represented assertion holds of the representation. -/
theorem lift_pull {Q : Assn} {z : state} {vs : Stack} (hz : wf_state z)
    (hvs : ∀ v ∈ vs, wf_val v) (hq : Q z vs) : lift (pull Q) z vs := by
  obtain ⟨s, hr⟩ := Rep.exists hz hvs
  exact ⟨s, hr, fun z' vs' hr' => by obtain ⟨rfl, rfl⟩ := Rep.functional hr hr'; exact hq⟩

/-- `Safe` from a well-formed configuration is `Safe` for the lifted pullbacks. -/
theorem Safe.pull {Q : Assn} {E : EAssn} {c : config} (h : Safe Q E c) :
    wf_config c → Safe (lift (pull Q)) (liftE (pullE E)) c := by
  induction h with
  | vals z vs hq =>
    intro hwf
    obtain ⟨hz, hvs⟩ := wf_of_code hwf
    exact .vals z vs (lift_pull hz hvs hq)
  | exit z is e hx he =>
    intro hwf
    refine .exit z is e hx ?_
    cases hx with
    | br vs l rest =>
      obtain ⟨l⟩ := l
      obtain ⟨hz, hvs⟩ := wf_of_code hwf
      exact lift_pull (Q := fun z vs => E (.br (.mk_uN l) vs) z) hz hvs he
    | ret vs rest =>
      obtain ⟨hz, hvs⟩ := wf_of_code hwf
      exact lift_pull (Q := fun z vs => E (.ret vs) z) hz hvs he
    | throw vs a rest =>
      obtain ⟨hz, -⟩ := wf_of_code hwf
      obtain ⟨s, hr⟩ := Rep.exists (vs := []) hz (by simp)
      exact ⟨s, hr, fun z' vs' hr' => by obtain ⟨rfl, -⟩ := Rep.functional hr hr'; exact he⟩
    | trap vs rest =>
      obtain ⟨hz, -⟩ := wf_of_code hwf
      obtain ⟨s, hr⟩ := Rep.exists (vs := []) hz (by simp)
      exact ⟨s, hr, fun z' vs' hr' => by obtain ⟨rfl, -⟩ := Rep.functional hr hr'; exact he⟩
  | step c hprog _ ih =>
    intro _
    exact .step c hprog fun c' hs => ih c' hs (Step.wf_target hs)

/-- On a represented state, `Code.wp` with any postconditions is the view `wp` of their
pullbacks. -/
theorem wp_view_iff {c : List instr} {Q : Assn} {E : EAssn} {s : VState} {z : state}
    {vs : Stack} (hr : Rep s z vs) :
    Std.WP.wp c (fun _ => pull Q) (pullE E) s ↔ Code.wp c Q E z vs := by
  constructor
  · intro h
    refine Code.wp_conseq ?_ ?_ (h z vs hr)
    · rintro z' vs' ⟨s', hr', hp⟩
      exact hp z' vs' hr'
    · intro e z' he
      rcases e with ⟨⟨l⟩, bs⟩ | bs | a | _ <;> obtain ⟨s', hr', hp⟩ := he
      · exact hp z' bs hr'
      · exact hp z' bs hr'
      · exact hp z' [] hr'
      · exact hp z' [] hr'
  · intro h z' vs' hr' hwf
    obtain ⟨rfl, rfl⟩ := Rep.functional hr hr'
    exact Safe.pull (h hwf) hwf

end SpecTecWP
