import SpecTecWP.Locals
import SpecTecWP.Arith

/-!
# The view: typed locals and a typed stack

A `VState` is a SpecTec state seen at the level of a Wasm program: the store, the locals as a
list of typed values `V`, and the operand stack, top first. `Rep s z vs` holds when the SpecTec
state `z` with the operand stack `vs` represents `s`. For example, with
`s = ⟨st, [.i32 a, .i32 b], [.i32 c]⟩`, `Rep s z vs` says `sof z = st`, the locals of the frame
of `z` are `[some (V.i32 a).enc, some (V.i32 b).enc]`, and `vs = [(V.i32 c).enc]`.

The `Std.WP.WP` instance on `List instr` has assertions over `VState`: `wp is Q E s` holds when
`Code.wp is` holds from every SpecTec state that represents `s`, for the postconditions `lift Q`
and `liftE E` that hold of a SpecTec state when one `VState` it represents satisfies `Q` or `E`.
`transport` turns a triple over the view into a `Code.wp` statement over the SpecTec model.
-/

namespace SpecTecWP

open Std.WP Lean.Order

/-- An `i32` value of the model. -/
abbrev i32v (x : uN) : val := .CONST .I32 (.mk_num__0 .I32 x)

/-- A typed Wasm value. -/
inductive V where
  | i32 (a : UInt32)
  | i64 (a : UInt64)
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

@[simp] theorem V.enc_i32 (a : UInt32) : (V.i32 a).enc = i32v (u a) := rfl

theorem V.enc_injective : Function.Injective V.enc := by
  intro v w h
  cases v <;> cases w <;> simp only [V.enc, u, val.CONST.injEq, num_.mk_num__0.injEq,
    uN.mk_uN.injEq, reduceCtorEq, false_and, and_false] at h
  · exact congrArg V.i32 (UInt32.toNat_inj.mp h.2.2)
  · exact congrArg V.i64 (UInt64.toNat_inj.mp h.2.2)

/-- A SpecTec state seen at the level of a Wasm program. -/
structure VState where
  store : store
  locals : List V
  stack : List V

/-- The SpecTec state `z` with the operand stack `vs` represents `s`. -/
def Rep (s : VState) (z : state) (vs : Stack) : Prop :=
  sof z = s.store ∧ (fof z).LOCALS = s.locals.map (fun v => some v.enc) ∧
    vs = s.stack.map V.enc

theorem map_inj_of {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf h.1, map_inj_of hf h.2]

theorem Rep.unique {s s' : VState} {z : state} {vs : Stack} (h : Rep s z vs) (h' : Rep s' z vs) :
    s = s' := by
  obtain ⟨st, ls, stk⟩ := s
  obtain ⟨st', ls', stk'⟩ := s'
  obtain ⟨hs, hl, hk⟩ := h
  obtain ⟨hs', hl', hk'⟩ := h'
  have e1 : st = st' := hs.symm.trans hs'
  have e2 : ls = ls' :=
    map_inj_of (fun a b h => V.enc_injective (Option.some.inj h)) (hl.symm.trans hl')
  have e3 : stk = stk' := map_inj_of V.enc_injective (hk.symm.trans hk')
  subst e1 e2 e3
  rfl

theorem Rep.stack {s : VState} {z : state} {vs : Stack} (st : List V) (h : Rep s z vs) :
    Rep { s with stack := st } z (st.map V.enc) :=
  ⟨h.1, h.2.1, rfl⟩

theorem Rep.get_local {s : VState} {z : state} {vs : Stack} {i : Nat} (h : Rep s z vs)
    (hi : i < s.locals.length) : fun_local z (.mk_uN i) = some (s.locals[i]!).enc := by
  simp [fun_local, proj_uN_0, h.2.1, hi]

theorem map_modify_const {α β : Type} (f : α → β) (a : α) :
    ∀ (L : List α) (i : Nat), (L.map f).modify i (fun _ => f a) = (L.set i a).map f
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | b :: L, i + 1 => by simp [map_modify_const f a L i]

theorem Rep.set_local {s : VState} {z : state} {vs : Stack} {i : Nat} (v : V) (h : Rep s z vs) :
    Rep { s with locals := s.locals.set i v } (with_local z (.mk_uN i) v.enc) vs := by
  refine ⟨(sof_with_local z _ _).trans h.1, ?_, h.2.2⟩
  have e : (fof (with_local z (.mk_uN i) v.enc)).LOCALS =
      (fof z).LOCALS.modify i (fun _ => some v.enc) := by
    simp [with_local, fof, fun_frame, proj_uN_0]
  rw [e, h.2.1]
  exact map_modify_const (fun v => some v.enc) v s.locals i

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

/-- The SpecTec assertion that holds when a represented `VState` satisfies `P`. -/
def lift (P : VAssn) : Assn := fun z vs => ∃ s, Rep s z vs ∧ P s

/-- The SpecTec exception postcondition that holds when a represented `VState` satisfies `E`. -/
def liftE (E : VEAssn) : EAssn
  | .br (.mk_uN l) vs => fun z => ∃ s, Rep s z vs ∧ E (.br l) s
  | .ret vs => fun z => ∃ s, Rep s z vs ∧ E .ret s
  | .throw a => fun z => ∃ s, Rep s z [] ∧ E (.throw a) s
  | .trap => fun z => ∃ s, Rep s z [] ∧ E .trap s

instance : WP (List instr) Unit VAssn VEAssn where
  trans is := ⟨fun Q E s => ∀ z vs, Rep s z vs → Code.wp is (lift (Q ())) (liftE E) z vs⟩
  trans_monotone is := by
    intro Q Q' E E' hE hQ s h z vs hr hwf
    refine Safe.mono ?_ ?_ (h z vs hr hwf)
    · rintro z vs ⟨s, hr, hq⟩
      exact ⟨s, hr, hQ () s hq⟩
    · intro e z he
      rcases e with ⟨⟨l⟩, vs⟩ | vs | a | _ <;> obtain ⟨s, hr, h⟩ := he <;> exact ⟨s, hr, hE _ s h⟩

/-- `lift P` holds of a SpecTec state that represents `s` with the stack replaced by `st`, when
`P` holds of that `VState`. -/
theorem lift_of {P : VAssn} {s : VState} {z : state} {vs : Stack} (st : List V)
    (hs : sof z = s.store) (hl : (fof z).LOCALS = s.locals.map (fun v => some v.enc))
    (hvs : vs = st.map V.enc) (hp : P { s with stack := st }) :
    ∃ s', Rep s' z vs ∧ P s' :=
  ⟨{ s with stack := st }, ⟨hs, hl, hvs⟩, hp⟩

theorem wp_view (is : List instr) (Q : Unit → VAssn) (E : VEAssn) :
    Std.WP.wp is Q E = fun s => ∀ z vs, Rep s z vs → Code.wp is (lift (Q ())) (liftE E) z vs :=
  rfl

/-- A triple over the view holds of the SpecTec model, from every represented state. -/
theorem transport {c : List instr} {P : VAssn} {Q : Unit → VAssn} {E : VEAssn}
    (h : Triple c P Q E) {s : VState} {z : state} {vs : Stack} (hr : Rep s z vs) (hp : P s) :
    Code.wp c (lift (Q ())) (liftE E) z vs :=
  Triple.iff.mp h s hp z vs hr

end SpecTecWP
