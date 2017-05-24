
// An executor executes an instruction set or language as a state
// machine. For a given state "s", "exec(s)" returns two possible next
// states. "branchCondition(s)" returns the condition under which the
// first of those states should be taken. When "s" is executing a
// non-branching instruction, it is common for "state(s)" to return (s2,
// null), and for "branchCondition(s)" to return true.
module AbstractExecutor {
  import opened SatLib : AbstractSatLib

  type State
  function method branchCondition(s: State): SatLib.BoolExpr
  function method exec(s: State): (State, State)
}


// Implements a basic subset of the LLVM intermediate representation.
//   http://llvm.org/docs/LangRef.html
module LlvmExecutor {
  import opened SatLib : AbstractSatLib

  type Reg = int  // Index into map of registers, State.regs

  datatype Instr =
    Add(dest: Reg, op1: Reg, op2: Reg)
  | Icmp(dest: Reg, op1: Reg, op2: Reg)
  | Br(cond: Reg, label1: int, label2: int)

  datatype State = State(ip: int, regs: Map<int, IntExpr>), halted: bool)

  var program = [
    Add(0, 1, 2),
    Icmp(0, 0, 1),
    Br(0, 0, 3),
  ];

  function method getInitialState(): State {
    State(0, map[], false)
  }

  function method branchCondition(s: State): SatLib.Equation {
    match program[s.ip]
      case Add(_, _, _): true
      case Icmp(_, _, _): true
      case Br(cond, _, _): cond
  }

  function method exec(s: State): (State, State) {
    if s.halted {
      (null, null)
    } else {

      match program[s.ip]

        case Add(dest, op1, op2):
          (State(
            s.ip + 1,
            s.regs[dest := add(op1, op2)],
            false
          ), null)

        case Icmp(dest, op1, op2):
          (State(
            s.ip + 1,
            s.regs[dest := cmp(op1, op2)],
            false
          ), null)

        case Br(cond, label1, label2):
          (
            State(
              label1
              s.regs,
              false
            ),
            State(
              label2
              s.regs,
              false
            )
          )

    }
  }

}
