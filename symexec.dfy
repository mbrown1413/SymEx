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
include "executor.dfy"

//TODO: Add "abstract" here once a concrete one is implemented.
module AbstractSatLib {

    type BoolExpr
    function method getTrueBool(): BoolExpr
    function method and(f1: BoolExpr, f2: BoolExpr): BoolExpr
    function method not(f1: BoolExpr): BoolExpr
    function method boolToInt(b: BoolExpr): IntExpr

    type IntExpr
    function method intConst(i: int): IntExpr
    function method intSymbolic(i: int): IntExpr
    function method add(f1: IntExpr, f2: IntExpr): IntExpr
    function method cmp(f1: IntExpr, f2: IntExpr): BoolExpr

    function method {:verify false} sat(f1: BoolExpr): bool

      // Used for King Property 1
      //TODO: Possibly derive this from simpler rules
      ensures sat(getTrueBool())
      ensures forall a,b :: sat(a) ==>
        sat(and(a,b)) || sat(and(a,not(b)))

      // Used for King Property 2
      //ensures forall a :: !sat(and(a, not(a)))
      //ensures forall a,b,c,d ::
      //  sat(and( and(a, b), and(c, d) )) ==
      //  sat(and( and(a, c), and(b, d) ))
      //ensures forall a,b ::
      //  !sat(a) ==> !sat( and(a, b) )
      //ensures forall a,b ::
      //  sat( and(a, b) ) ==
      //  sat( and(b, a) )

}

import opened Exec : LlvmExecutor
import opened dpll : DPLL

method Main()
  decreases *
{
  var tree := symex();
}

// The core of the symbolic execution engine. Explore state in the order
// according to the scheduler, ensuring that a state is only explored if
// it can be reached (the path condition leading to it is satisfyable).
method symex() returns (tree: array<NodeMaybe>)
  decreases *  // Possibly non-terminating
  ensures tree != null

  // King Property 1
  // All nodes in the tree should be satisfyable.
  //
  // Verification: This property is simple to verify since we explicitly don't
  // enqueue to the scheduler if the path condition is not satisfyable. We
  // simply added this as a loop invariant in the main loop.
  ensures forall i :: 0 <= i < tree.Length ==> match tree[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;

  // King Property 2
  // Path conditions in leaf nodes do not overlap.
  // That is, any assignment of variables leads to exactly one leaf node.
  //ensures tree.Length >= 1
  //ensures forall i,j :: 0 <= i < tree.Length && 0 <= j < tree.Length ==>
  //  var node_i := match tree[i] case Some(node) => node case None => null;
  //  var node_j := match tree[j] case Some(node) => node case None => null;
  //  node_i != null //&& node_j != null && i != j &&
  //  isLeaf(i, tree) &&
  //  isLeaf(j, tree)
  //  ==> !SatLib.sat(SatLib.and(node_i.pc, node_j.pc))

{
  var initState := getInitialState();
  var scheduler := new TreeQueue(initState);

  assert !scheduler.isEmpty();
  while !scheduler.isEmpty()
    decreases *  // Possibly non-terminating
    invariant scheduler.a != null
    invariant scheduler.Valid()

    // Nodes are always satisfyable (else they are not enqueued)
    // Used to verify King Prop 1
    invariant forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;

    // Used to verify King Prop 2
    //invariant scheduler.end < scheduler.a.Length
    //invariant forall i,j :: 0 <= i <= scheduler.end && 0 <= j <= scheduler.end ==>
    //var node_i := match scheduler.a[i] case Some(node) => node case None => null;
    //var node_j := match scheduler.a[j] case Some(node) => node case None => null;
    //node_i != null && node_j != null && i != j &&
    //  isLeaf(i, scheduler.a) &&
    //  isLeaf(j, scheduler.a)
    //  ==> !isAncestor(i, j)
    //  //!isAncestor(i, j)
    //  //==> !sat( and(node_i.pc, node_j.pc) )

  {
    var state_node := scheduler.Dequeue();
    if state_node != null {
      step_execution(scheduler, state_node);
    }

  }

  return scheduler.a;
}

// Enqueue the children of state_node, but only if their path condition
// is satisfyable.
method step_execution(scheduler: TreeQueue, state_node: Node)
  requires scheduler != null
  requires scheduler.a != null
  requires state_node != null
  requires SatLib.sat(state_node.pc)
  requires scheduler.Valid() && scheduler.start >= 0

  ensures scheduler.a != null
  ensures scheduler.Valid()

  // King 1
  requires forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;
  ensures forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;

  modifies scheduler
{

  var bc := Exec.branchCondition(state_node.state);
  var s1_state, s2_state := Exec.exec(state_node.state);
  var s1_pc := SatLib.and(state_node.pc, bc);
  var s2_pc := SatLib.and(state_node.pc, SatLib.not(bc));

  var node1: Node := null;
  var node2: Node := null;
  var node1_maybe: NodeMaybe := NodeMaybe.None;
  var node2_maybe: NodeMaybe := NodeMaybe.None;
  if !SatLib.sat(s1_pc) {
    node2 := new Node(s2_state, s2_pc);
    node1_maybe, node2_maybe := scheduler.Enqueue(null, node2);
  } else if !SatLib.sat(s2_pc) {
    node1 := new Node(s1_state, s1_pc);
    node1_maybe, node2_maybe := scheduler.Enqueue(node1, null);
  } else {
    node1 := new Node(s1_state, s1_pc);
    node2 := new Node(s2_state, s2_pc);
    node1_maybe, node2_maybe := scheduler.Enqueue(node1, node2);
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


