import SpecTecWP.InstrLocal
import SpecTecWP.Arith
import WasmWP.Spec

/-!
# The translation from Talos to the SpecTec model

The fragment consists of `i32`/`i64` constants, the integer operators, the local variable
instructions, `drop`, `nop` and `unreachable`. A Talos frame `s` corresponds to the SpecTec
state `zOf s` with the empty store and the frame whose locals are `s.params ++ s.locals`, and
to the stack `stk s`. The Talos store does not change on the fragment.
-/

namespace Adequacy

open SpecTecWP

/-- The SpecTec value of a Talos value of the fragment. -/
def tv : Wasm.Value → val
  | .i32 n => .CONST .I32 (.mk_num__0 .I32 (.mk_uN n.toNat))
  | .i64 n => .CONST .I64 (.mk_num__0 .I64 (.mk_uN n.toNat))
  | _ => .REF_NULL_ADDR

/-- The SpecTec frame of a Talos frame. -/
def frameOf (s : Wasm.Locals) : frame :=
  { LOCALS := (s.params ++ s.locals).map (fun v => some (tv v)), MODULE := default }

/-- The SpecTec state of a Talos frame. -/
def zOf (s : Wasm.Locals) : state := .mk_state default (frameOf s)

/-- The SpecTec stack of a Talos frame. -/
def stk (s : Wasm.Locals) : Stack := s.values.map tv

def i32op (op : binop_Inn) : instr := .BINOP .I32 (.mk_binop__0 .I32 op)
def i32rel (op : relop_Inn) : instr := .RELOP .I32 (.mk_relop__0 .I32 op)

/-- The SpecTec instruction of a Talos instruction of the fragment. -/
def ti : Wasm.Instruction → Option instr
  | .const n => some (instr_val (tv (.i32 n)))
  | .constI64 n => some (instr_val (tv (.i64 n)))
  | .add => some (i32op .ADD)
  | .sub => some (i32op .SUB)
  | .mul => some (i32op .MUL)
  | .divU => some (i32op (.DIV .U))
  | .remU => some (i32op (.REM .U))
  | .and => some (i32op .AND)
  | .or => some (i32op .OR)
  | .xor => some (i32op .XOR)
  | .eqz => some (.TESTOP .I32 (.mk_testop__0 .I32 .EQZ))
  | .eq => some (i32rel .EQ)
  | .ne => some (i32rel .NE)
  | .ltU => some (i32rel (.LT .U))
  | .ltS => some (i32rel (.LT .S))
  | .localGet i => some (.LOCAL_GET (.mk_uN i))
  | .localSet i => some (.LOCAL_SET (.mk_uN i))
  | .localTee i => some (.LOCAL_TEE (.mk_uN i))
  | .drop => some .DROP
  | .nop => some .NOP
  | .unreachable => some .UNREACHABLE
  | _ => none

/-- The SpecTec instruction sequence of a Talos program of the fragment. -/
def tp : Wasm.Program → Option (List instr)
  | [] => some []
  | i :: p => do
    let j ← ti i
    let q ← tp p
    pure (j :: q)

/-- A Talos postcondition, read on SpecTec states and stacks. -/
def postT (st : Wasm.Store Wasm.U) (P : Wasm.Assn) : Assn :=
  fun z vs => ∃ s, z = zOf s ∧ vs = stk s ∧ P st s

/-- A Talos exception postcondition, read on SpecTec exits. -/
def epostT (st : Wasm.Store Wasm.U) (epost : Wasm.EAssn) : EAssn
  | .trap, _ => ∃ msg, ∀ s, epost (.Trap msg) st s
  | .br l vs, z => ∃ s, z = zOf s ∧ vs = stk s ∧ epost (.Break (proj_uN_0 l)) st s
  | _, _ => False

/-! ## Well-formedness of translated states -/

theorem wf_tv (v : Wasm.Value) : wf_val (tv v) := by
  cases v with
  | i32 n =>
    refine .val_case_0 _ _ (.num__case_0 _ _ _ (.uN_case_0 _ _ ⟨by omega, ?_⟩ (by decide)) rfl)
    have := n.toNat_lt; simp [size, numtype_addrtype]; omega
  | i64 n =>
    refine .val_case_0 _ _ (.num__case_0 _ _ _ (.uN_case_0 _ _ ⟨by omega, ?_⟩ (by decide)) rfl)
    have := n.toNat_lt; simp [size, numtype_addrtype]; omega
  | _ => exact .val_case_3

theorem wf_default_moduleinst : wf_moduleinst default := by
  constructor <;> (intro x hx; cases hx)

theorem wf_default_store : wf_store default := by
  constructor <;> (intro x hx; cases hx)

theorem wf_zOf (s : Wasm.Locals) : wf_state (zOf s) := by
  refine .state_case_0 _ _ wf_default_store (.frame_case_ _ _ ?_ wf_default_moduleinst)
  intro o ho v hv
  simp only [List.mem_map] at ho
  obtain ⟨w, -, rfl⟩ := ho
  simp only [Option.toList_some, List.mem_singleton] at hv
  exact hv ▸ wf_tv w

theorem wf_num_u (x : UInt32) : wf_num_ .I32 (.mk_num__0 .I32 (u x)) := by
  have := wf_tv (.i32 x); cases this; assumption

theorem wf_uN_u (x : UInt32) : wf_uN 32 (u x) := by
  have := wf_num_u x; cases this; assumption

theorem tv_i32 (x : UInt32) : tv (.i32 x) = .CONST .I32 (.mk_num__0 .I32 (u x)) := rfl

end Adequacy
