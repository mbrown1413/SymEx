
// An executor executes an instruction set or language as a state
// machine. For a given state "s", "exec(s)" returns two possible next
// states. "branchCondition(s)" returns the condition under which the
// first of those states should be taken. When "s" is executing a
// non-branching instruction, it is common for "state(s)" to return (s2,
// null), and for "branchCondition(s)" to return true.
module AbstractExecutor {
  import opened SatLib : AbstractSatLib

  type State
  method getInitialState() returns (s: State)
  method branchCondition(s: State) returns (cond: SatLib.BoolExpr)
  method exec(s: State) returns (s1: State, s2: State)
}



// Implements a basic subset of the LLVM intermediate representation.
//   http://llvm.org/docs/LangRef.html
module LlvmExecutor {
  import opened SatLib : AbstractSatLib

  type Reg = int  // Index into map of registers, State.regs

  datatype Instr =
    Add(add_dest: Reg, add_op1: Reg, add_op2: Reg)
  | Icmp(icmp_dest: Reg, icmp_op1: Reg, icmp_op2: Reg)
  | Br(br_cond: Reg, br_label1: int, br_label2: int)

  datatype State = State(ip: int, regs: map<Reg, IntExpr>) | HaltedState

  method program() returns (instrs: array<Instr>) {
    instrs := new Instr[3];
    instrs[0] := Add(0, 1, 2);
    instrs[1] := Icmp(0, 0, 1);
    instrs[2] := Br(0, 0, 3);
    return instrs;
  }

  method getInitialState() returns (s: State) {
    return State(0, map[]);
  }

  method branchCondition(s: State) returns (cond: SatLib.BoolExpr) {
    var prog := program();
    return match prog[s.ip]
      case Add(_, _, _) => getTrueBool()
      case Icmp(_, _, _) => getTrueBool()
      case Br(cond, _, _) => cmp(s.regs[cond], intConst(1));
  }

  method exec(s: State) returns (s1: State, s2: State) {
    if s.HaltedState? {
      return HaltedState, HaltedState;
    } else {

      var prog := program();

      match prog[s.ip] {

        case Add(dest, op1, op2) =>
          return State(
            s.ip + 1,
            s.regs[dest := add(s.regs[op1], s.regs[op2])]
          ), HaltedState;

        case Icmp(dest, op1, op2) =>
          return State(
            s.ip + 1,
            s.regs[dest := boolToInt(cmp(s.regs[op1], s.regs[op2]))]
          ), HaltedState;

        case Br(cond, label1, label2) =>
          return State(
            label1,
            s.regs
          ), State(
            label2,
            s.regs
          );
      }

    }
  }

}
