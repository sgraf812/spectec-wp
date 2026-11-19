import Adequacy.Translate
import SpecTecWP.Interp

/-!
# Differential testing of the SpecTec model against Talos

`interp_Step_io` is the interpreter that the Lean backend generates from the SpecTec rules: each
successor it returns carries a proof of `Step`. A test runs a random, well-typed, straight-line program
over all `i32` and `i64` integer instructions in Talos (`Wasm.exec`) and in the interpreter, from the frame `s` with locals `ls`, and
compares the results:

* if Talos falls through with the frame `s'`, the interpreter must reach the values of
  `stk s'` with the locals of `frameOf s'`;
* if Talos traps, the interpreter must reach `[TRAP]`;
* the interpreter must not get stuck on a well-typed program;
* if the interpreter finds several successors of a configuration, they must all lead to the
  same outcome.
-/

namespace Differential

open Wasm (Instruction Value Locals)
open Adequacy

/-- The type and payload of a SpecTec value of the fragment. -/
def payload : val → Option (Bool × Nat)
  | .CONST .I32 (.mk_num__0 .I32 (.mk_uN n)) => some (false, n)
  | .CONST .I64 (.mk_num__0 .I64 (.mk_uN n)) => some (true, n)
  | _ => none

def payloadT : Value → Option (Bool × Nat)
  | .i32 n => some (false, n.toNat)
  | .i64 n => some (true, n.toNat)
  | _ => none

def payloadI (i : instr) : Option (Bool × Nat) :=
  (interp_inv_instr_val i).bind fun ⟨v, _⟩ => payload v

inductive Outcome where
  | values (vs : List (Option (Bool × Nat))) (locals : List (Option (Bool × Nat)))
  | trap
  | stuck (n : Nat)
  | ambiguous (n : Nat) (k : Nat)
  | outOfFuel
  deriving Repr, BEq

/-- Equality of the instructions of the fragment. Two other instructions count as different. -/
def instrEq : instr → instr → Bool
  | .CONST t c, .CONST t' c' => decide (t = t' ∧ c = c')
  | .BINOP t o, .BINOP t' o' => decide (t = t' ∧ o = o')
  | .RELOP t o, .RELOP t' o' => decide (t = t' ∧ o = o')
  | .TESTOP t o, .TESTOP t' o' => decide (t = t' ∧ o = o')
  | .UNOP t o, .UNOP t' o' => decide (t = t' ∧ o = o')
  | .CVTOP t u o, .CVTOP t' u' o' => decide (t = t' ∧ u = u' ∧ o = o')
  | .LOCAL_GET x, .LOCAL_GET y | .LOCAL_SET x, .LOCAL_SET y | .LOCAL_TEE x, .LOCAL_TEE y =>
    decide (x = y)
  | .DROP, .DROP | .NOP, .NOP | .UNREACHABLE, .UNREACHABLE | .TRAP, .TRAP => true
  | _, _ => false

/-- Equality of configurations of the fragment, whose store does not change. -/
def configEq : config → config → Bool
  | .mk_config (.mk_state _ f) is, .mk_config (.mk_state _ f') is' =>
    is.length == is'.length && (is.zip is').all (fun (a, b) => instrEq a b) &&
      decide (f.LOCALS = f'.LOCALS)

/-- The successors of `c`, without repetitions. -/
def successors (c : config) : List config :=
  (interp_Step_io c).foldl (fun acc r => if acc.any (configEq r.1) then acc else acc ++ [r.1]) []

/-- Run the interpreter for at most `fuel` steps. -/
def runSpec (fuel : Nat) (c : config) (n : Nat := 0) : Outcome :=
  match c with
  | .mk_config (.mk_state _ f) is =>
    if is.all (fun i => (payloadI i).isSome) then
      .values (is.map payloadI) (f.LOCALS.map fun o => o.bind payload)
    else match is with
      | [.TRAP] => .trap
      | _ => match fuel, successors c with
        | 0, _ => .outOfFuel
        | _, [] => .stuck n
        | fuel + 1, [c'] => runSpec fuel c' (n + 1)
        | fuel + 1, c' :: cs =>
          -- Several successors are fine if they all lead to the same outcome.
          let o := runSpec fuel c' (n + 1)
          if cs.all (fun c'' => runSpec fuel c'' (n + 1) == o) then o
          else .ambiguous n (cs.length + 1)

def runTalos (fuel : Nat) (s : Locals) (p : Wasm.Program) : Option Outcome :=
  match Wasm.exec fuel { funcs := [] } ({ globals := {}, mem := default, host := () } : Wasm.Store Wasm.U) s p with
  | .Fallthrough _ s' =>
    some (.values (s'.values.reverse.map payloadT) ((s'.params ++ s'.locals).map payloadT))
  | .Trap _ _ => some .trap
  | _ => none

/-! A linear congruential generator, so that the tests are reproducible. -/

def next (g : Nat) : Nat := (g * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def pick (g : Nat) (n : Nat) : Nat := (g / 2 ^ 33) % n

def consts32 : List UInt32 := [0, 1, 2, 3, 7, 31, 32, 0x7fffffff, 0x80000000, 0xffffffff, 0xfffffffe, 100]

def consts64 : List UInt64 :=
  [0, 1, 2, 63, 64, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
   0xffffffffffffffff, 0x80000000, 100]

/-- An operator of the test: its Talos and SpecTec instructions, the types of its operands
(top first, `true` for `i64`) and the type of its result. -/
structure Op where
  talos : Instruction
  spec : instr
  ins : List Bool
  out : Option Bool

def nt (b : Bool) : numtype := if b then .I64 else .I32
def inn (b : Bool) : Inn := if b then .I64 else .I32

def bin (b : Bool) (t : Instruction) (o : binop_Inn) : Op :=
  ⟨t, .BINOP (nt b) (.mk_binop__0 (inn b) o), [b, b], some b⟩
def rel (b : Bool) (t : Instruction) (o : relop_Inn) : Op :=
  ⟨t, .RELOP (nt b) (.mk_relop__0 (inn b) o), [b, b], some false⟩
def un (b : Bool) (t : Instruction) (o : unop_Inn) : Op :=
  ⟨t, .UNOP (nt b) (.mk_unop__0 (inn b) o), [b], some b⟩
def cvt (b₁ b₂ : Bool) (t : Instruction) (o : cvtop__Inn_1_Inn_2) : Op :=
  ⟨t, .CVTOP (nt b₁) (nt b₂) (.mk_cvtop___0 (inn b₂) (inn b₁) o), [b₂], some b₁⟩

def ops32 : List Op :=
  [bin false .add .ADD, bin false .sub .SUB, bin false .mul .MUL,
   bin false .divU (.DIV .U), bin false .divS (.DIV .S), bin false .remU (.REM .U),
   bin false .remS (.REM .S), bin false .and .AND, bin false .or .OR, bin false .xor .XOR,
   bin false .shl .SHL, bin false .shrU (.SHR .U), bin false .shrS (.SHR .S),
   bin false .rotl .ROTL, bin false .rotr .ROTR,
   rel false .eq .EQ, rel false .ne .NE, rel false .ltU (.LT .U), rel false .ltS (.LT .S),
   rel false .gtU (.GT .U), rel false .gtS (.GT .S), rel false .leU (.LE .U),
   rel false .leS (.LE .S), rel false .geU (.GE .U), rel false .geS (.GE .S),
   ⟨.eqz, .TESTOP .I32 (.mk_testop__0 .I32 .EQZ), [false], some false⟩,
   un false .clz .CLZ, un false .ctz .CTZ, un false .popcnt .POPCNT,
   un false .extend8S (.EXTEND (.mk_sz 8)), un false .extend16S (.EXTEND (.mk_sz 16))]

def ops64 : List Op :=
  [bin true .addI64 .ADD, bin true .subI64 .SUB, bin true .mulI64 .MUL,
   bin true .divUI64 (.DIV .U), bin true .divSI64 (.DIV .S), bin true .remUI64 (.REM .U),
   bin true .remSI64 (.REM .S), bin true .andI64 .AND, bin true .orI64 .OR,
   bin true .xorI64 .XOR, bin true .shlI64 .SHL, bin true .shrUI64 (.SHR .U),
   bin true .shrSI64 (.SHR .S), bin true .rotlI64 .ROTL, bin true .rotrI64 .ROTR,
   rel true .eqI64 .EQ, rel true .neI64 .NE, rel true .ltUI64 (.LT .U),
   rel true .ltSI64 (.LT .S), rel true .gtUI64 (.GT .U), rel true .gtSI64 (.GT .S),
   rel true .leUI64 (.LE .U), rel true .leSI64 (.LE .S), rel true .geUI64 (.GE .U),
   rel true .geSI64 (.GE .S),
   ⟨.eqzI64, .TESTOP .I64 (.mk_testop__0 .I64 .EQZ), [true], some false⟩,
   un true .clzI64 .CLZ, un true .ctzI64 .CTZ, un true .popcntI64 .POPCNT,
   un true .extend8SI64 (.EXTEND (.mk_sz 8)), un true .extend16SI64 (.EXTEND (.mk_sz 16)),
   un true .extend32SI64 (.EXTEND (.mk_sz 32)),
   cvt false true .wrapI64 .WRAP, cvt true false .extendSI32 (.EXTEND .S),
   cvt true false .extendUI32 (.EXTEND .U)]

def ops : List Op := ops32 ++ ops64

def constOp (g : Nat) (b : Bool) : Op :=
  if b then
    let n := consts64.getD (pick g consts64.length) 0
    ⟨.constI64 n, instr_val (tv (.i64 n)), [], some true⟩
  else
    let n := consts32.getD (pick g consts32.length) 0
    ⟨.const n, instr_val (tv (.i32 n)), [], some false⟩

/-- Pop the operand types `ins` from the type stack `ts`, if they are on top. -/
def popTypes : List Bool → List Bool → Option (List Bool)
  | [], ts => some ts
  | i :: ins, t :: ts => if i == t then popTypes ins ts else none
  | _ :: _, [] => none

/-- A random program of length `len` over locals of types `lt`, with the type stack `ts`. -/
def gen (lt : List Bool) : Nat → Nat → List Bool → List Op
  | 0, _, _ => []
  | len + 1, g, ts =>
    let g₁ := next g
    let g₂ := next g₁
    let k := pick g 20
    let push (o : Op) := o :: gen lt len g₂ ((o.out.toList) ++ (popTypes o.ins ts).getD ts)
    let pushConst := push (constOp g₂ (pick g₁ 2 == 1))
    if ts.isEmpty ∨ k < 5 then
      if k < 2 ∧ !lt.isEmpty then
        let i := pick g₁ lt.length
        push ⟨.localGet i, .LOCAL_GET (.mk_uN i), [], some (lt.getD i false)⟩
      else pushConst
    else if k < 15 then
      -- Try a few operators; fall back to a constant.
      let cands := (List.range 6).filterMap fun j =>
        let o := ops.getD (pick ((List.range j).foldl (fun a _ => next a) g₁) ops.length) (constOp g false)
        if (popTypes o.ins ts).isSome then some o else none
      match cands with
      | o :: _ => push o
      | [] => pushConst
    else match ts, k with
      | t :: _, 15 => push ⟨.drop, .DROP, [t], none⟩
      | t :: _, 16 =>
        match (List.range lt.length).find? (fun i => lt.getD i false == t) with
        | some i => push ⟨.localSet i, .LOCAL_SET (.mk_uN i), [t], none⟩
        | none => push ⟨.nop, .NOP, [], none⟩
      | t :: _, 17 =>
        match (List.range lt.length).find? (fun i => lt.getD i false == t) with
        | some i => push ⟨.localTee i, .LOCAL_TEE (.mk_uN i), [t], some t⟩
        | none => push ⟨.nop, .NOP, [], none⟩
      | _, 18 => if pick g₁ 4 == 0 then push ⟨.unreachable, .UNREACHABLE, [], none⟩
                 else push ⟨.nop, .NOP, [], none⟩
      | _, _ => push ⟨.nop, .NOP, [], none⟩

structure Result where
  agree : Nat := 0
  traps : Nat := 0
  failures : List (Wasm.Program × Option Outcome × Outcome) := []

def test (count len : Nat) (seed : Nat := 1) : Result := Id.run do
  let mut r : Result := {}
  let mut g := seed
  for _ in [0:count] do
    g := next g
    let lt := (List.range (pick g 4)).map fun i => (g / 2 ^ (i + 3)) % 2 == 1
    let ls : List Value := lt.zipIdx.map fun (b, i) =>
      if b then .i64 (consts64.getD ((g / 11 + i) % 12) 0)
      else .i32 (consts32.getD ((g / 7 + i) % 12) 0)
    let s : Locals := { locals := ls }
    let p := gen lt len (next g) []
    let spec := runSpec 500 (.mk_config (zOf s) (p.map Op.spec))
    let talos := runTalos 1000 s (p.map Op.talos)
    if talos == some spec then
      r := { r with agree := r.agree + 1, traps := r.traps + (if spec == .trap then 1 else 0) }
    else r := { r with failures := r.failures ++ [(p.map Op.talos, talos, spec)] }
  return r

end Differential
