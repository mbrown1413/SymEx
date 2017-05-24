//Todo:
//Figure out tree representation with Michael's queue stuff.
//Figure out following classes/modules/etc.:
//    State: how we represent variable value assignemnts here will
//        affect how we implement PC.
//    Scheduler: need to manage tree, add and pop functions, reason
//        about state exploration.
//    PC: need to figure out how to represent and call external
//        SAT solver.
//    exec module: come up with an interface for (sybolic) instruction
//        execution.

//We need to define State, it should have: PC, variables, variables to
//values mapping, instructions, and a function to get the next instruction.

//We need to build the scheduler.  It needs to do bookkeeping and build a tree
//about which we can prove the properties from the king paper.

//PC is a boolean expression over symbolic inputs (values).  Need to have
//update functions for this to be used in exec.  The important thing with
//PC is that we can give it to a SAT solver.  Assuming we want this to run code
//beyond a proof, that means calling a solver from dafny, and ensuring the PC
//conforms to the solver's interface.

include "Dpll.dfy"
include "PropLogic.dfy"
include "scheduler.dfy"

module AbstractSatLib {

    type BoolExpr
    function method sat(f1: BoolExpr): bool
    function method and(f1: BoolExpr, f2: BoolExpr): BoolExpr
    function method not(f1: BoolExpr): BoolExpr

    type IntExpr
    function method add(f1: IntExpr, f2: IntExpr): IntExpr
    function method cmp(f1: IntExpr, f2: IntExpr): BoolExpr

}

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

import opened Exec : AbstractExecutor
import opened dpll : DPLL


// The core of the symbolic execution engine. Explore state in the order
// according to the scheduler, ensuring that a state is only explored if
// it can be reached (the path condition leading to it is satisfyable).
method main() returns (tree: array<NodeMaybe>)
  decreases *  // Possibly non-terminating

  //King Prop 1
  ensures forall i ::
    var node_i := match tree[i] case Some(node) => node;
    0<=i<=tree.Length ==> SatLib.sat(node_i.pc);

  //King Prop 2
  /*
  ensures forall j,k ::
    var node_j := match tree[j] case Some(node) => node;
    var node_k := match tree[k] case Some(node) => node;
    0<=j<=tree.Length && 0<=k<=tree.Length ==> isLeaf(node_j, tree) && isLeaf(node_k, tree) && j!=k ==> !(SatLib.sat(SatLib.and(node_j.pc, node_k.pc)))
  */
  /*
    match tree[j]
      case None => false
      case Some(node_j) =>
        (match tree[k]
          case None => false
          case Some(node_k) =>
            0<=j<=tree.Length && 0<=k<=tree.Length ==> isLeaf(node_j, tree) && isLeaf(node_k, tree) && j!=k ==> !(SatLib.sat(SatLib.and(node_j.pc, node_k.pc)))
        );
  */

{
  var scheduler := new TreeQueue();

  while !scheduler.isEmpty()
    decreases *  // Possibly non-terminating
  {
    var state_node := scheduler.Dequeue();
    if state_node != null{
      step_execution(scheduler, state_node);
    }

  }
  tree := scheduler.getTree();
  return tree;
}

// Enqueue the children of state_node, but only if their path condition
// is satisfyable.
method step_execution(scheduler: TreeQueue, state_node: Node)
{
  var bc := Exec.branchCondition(state_node.state);
  var (s1_state, s2_state) := Exec.exec(state_node.state);
  var s1_pc := SatLib.and(state_node.pc, bc);
  var s2_pc := SatLib.and(state_node.pc, SatLib.not(bc));
  var node1 := new Node(s1_state, s1_pc);
  var node2 := new Node(s2_state, s2_pc);
  if !SatLib.sat(s1_pc) {
    scheduler.RightEnqueue(node2);
  } else if !SatLib.sat(s2_pc) {
    scheduler.LeftEnqueue(node1);
  } else {
    scheduler.DoubleEnqueue(node1, node2);
  }
}

module SAT_Func{
import opened dpll : DPLL

method SAT(formula: Formula) returns (sat_bool: bool)
decreases *
{
var alpha : Option<Assignment> := dpll.DPLL(formula);

 var temp_sat_bool := false;
  if !(alpha == Option<Assignment>.None){
   temp_sat_bool := true;
  }
sat_bool := temp_sat_bool;
}

}


