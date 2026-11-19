import SpecTecWP.Interp

/-! Smoke tests of the generated interpreter `interp_Step_pure_io`. -/

namespace InterpTest

def c32 (n : Nat) : instr := .CONST .I32 (.mk_num__0 .I32 (.mk_uN n))
def bin (op : binop_Inn) : instr := .BINOP .I32 (.mk_binop__0 .I32 op)
def rel (op : relop_Inn) : instr := .RELOP .I32 (.mk_relop__0 .I32 op)

def showInstr : instr → String
  | .CONST .I32 (.mk_num__0 .I32 (.mk_uN n)) => s!"i32.const {n}"
  | .CONST .I32 _ => "i32.const ?"
  | .TRAP => "trap"
  | .NOP => "nop"
  | .DROP => "drop"
  | _ => "?"

def run (l : List instr) : List (List String) :=
  (interp_Step_pure_io l).map fun r => r.1.map showInstr

#eval run [c32 2, c32 3, bin .ADD]
#eval run [c32 7, c32 0, bin (.DIV .U)]
#eval run [c32 7, c32 2, bin (.DIV .U)]
#eval run [c32 2, c32 3, rel (.LT .U)]
#eval run [c32 0, .TESTOP .I32 (.mk_testop__0 .I32 .EQZ)]
#eval run [c32 1, .DROP]
#eval run [.NOP]
#eval run [.UNREACHABLE]
#eval run [c32 1, .TRAP, .NOP]
#eval run [c32 1, c32 2]

end InterpTest
