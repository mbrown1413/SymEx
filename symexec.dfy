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

//include "Dpll.dfy"
//include "PropLogic.dfy"
include "sat.dfy"
include "scheduler.dfy"
include "executor.dfy"

import opened Exec : LlvmExecutor

method Main()
  decreases *
{
  var scheduler := symex();
  scheduler.printTree();
}

// Path conditions in leaf nodes do not overlap.
// That is, any assignment of variables leads to exactly one leaf node.
predicate king2(scheduler: TreeQueue)
  requires scheduler != null
  requires scheduler.a != null
  reads scheduler, scheduler.a
  reads *
{
  forall i,j :: 0 <= i < scheduler.a.Length && 0 <= j < scheduler.a.Length ==>
    var node_i := match scheduler.a[i] case Some(node) => node case None => null;
    var node_j := match scheduler.a[j] case Some(node) => node case None => null;
    node_i != null && node_j != null && i != j &&
    isLeaf(i, scheduler.a) &&
    isLeaf(j, scheduler.a)
    ==> (
      !SatLib.sat(SatLib.and(node_i.pc, node_j.pc))
    )
}

// The core of the symbolic execution engine. Explore state in the order
// according to the scheduler, ensuring that a state is only explored if
// it can be reached (the path condition leading to it is satisfyable).
method symex() returns (scheduler: TreeQueue)
  decreases *  // Possibly non-terminating
  ensures scheduler != null
  ensures scheduler.a != null

  // King Property 1
  // All nodes in the tree should be satisfyable.
  //
  // Verification: This property is simple to verify since we explicitly don't
  // enqueue to the scheduler if the path condition is not satisfyable. We
  // simply added this as a loop invariant in the main loop.
  ensures forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;

  // King Property 2
  ensures scheduler.a.Length >= 1
  ensures king2(scheduler)

{
  var initState := getInitialState();
  scheduler := new TreeQueue(initState);

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
    invariant king2(scheduler)
    //invariant 2*scheduler.start+2 >= scheduler.end

  {
    var state_node := scheduler.Dequeue();
    if state_node != null {
      step_execution(scheduler, state_node);
    }

  }

  return scheduler;
}

// Enqueue the children of state_node, but only if their path condition
// is satisfyable.
method step_execution(scheduler: TreeQueue, state_node: Node)
  requires scheduler != null
  requires scheduler.a != null
  requires state_node != null
  requires SatLib.sat(state_node.pc)
  requires scheduler.Valid() && scheduler.start >= 0
  requires scheduler.a[scheduler.start].Some?
  requires scheduler.a[scheduler.start].v == state_node
  requires scheduler.start >= 0

  ensures scheduler.Valid()

  // Used for King 1
  requires forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;
  ensures forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true;

  // Used for King 2
  requires king2(scheduler)
  ensures king2(scheduler)
  requires isLeaf(scheduler.start, scheduler.a)

  modifies scheduler
{
  var halted := Exec.halted(state_node.state);
  if halted {
    return;
  }

  var bc := Exec.branchCondition(state_node.state);
  var s1_state, s2_state := Exec.exec(state_node.state);
  var s1_pc := SatLib.and(state_node.pc, bc);
  var s2_pc := SatLib.and(state_node.pc, SatLib.not(bc));

  // Used for King 1
  assert !SatLib.sat(SatLib.and(s1_pc, s2_pc));

  // state_node satisfies King 2
  // This is exactly like King 2, except node_j is always the last dequeue'd
  // node.
  assert forall i :: 0 <= i < scheduler.a.Length ==>
    var node_i := match scheduler.a[i] case Some(node) => node case None => null;
    var node_j := match scheduler.a[scheduler.start] case Some(node) => node case None => null;
    node_i != null && node_j != null && i != scheduler.start &&
    isLeaf(i, scheduler.a)
    ==> (
      !SatLib.sat(SatLib.and(node_i.pc, node_j.pc))
    );

  // Intermediate assertion that helps prove the next one.
  assert forall i :: 0 <= i < scheduler.a.Length ==>
    var node_i := match scheduler.a[i] case Some(node) => node case None => null;
    var node_j := match scheduler.a[scheduler.start] case Some(node) => node case None => null;
    node_i != null && node_j != null && i != scheduler.start &&
    isLeaf(i, scheduler.a)
    ==> (
      (!SatLib.sat(SatLib.and(SatLib.and(node_i.pc, node_j.pc), bc))) &&
      (!SatLib.sat(SatLib.and(node_i.pc, SatLib.and(node_j.pc, bc)))) &&
      (!SatLib.sat(SatLib.and(SatLib.and(node_i.pc, node_j.pc), SatLib.not(bc)))) &&
      (!SatLib.sat(SatLib.and(node_i.pc, SatLib.and(node_j.pc, SatLib.not(bc)))))
    );

  // Path conditions for the nodes we are about to enqueue do not overlap with
  // any existing leaves, except the parent node.
  // Final precondition we need before Enqueue.
  assert forall i :: 0 <= i < scheduler.a.Length ==>
    var node_i := match scheduler.a[i] case Some(node) => node case None => null;
    node_i != null && i != scheduler.start &&
    isLeaf(i, scheduler.a)
    ==> (
      (!SatLib.sat(SatLib.and(node_i.pc, s1_pc))) &&
      (!SatLib.sat(SatLib.and(node_i.pc, s2_pc)))
    );

  var node1: Node := null;
  var node2: Node := null;
  var node1_maybe: NodeMaybe := NodeMaybe.None;
  var node2_maybe: NodeMaybe := NodeMaybe.None;
  if !SatLib.sat(s1_pc) {

    // Used for King 2
    // Uses: Negation Axiom of "or"
    assert SatLib.sat(s2_pc);

    node2 := new Node(s2_state, s2_pc);
    node1_maybe, node2_maybe := scheduler.Enqueue(null, node2);
  } else if !SatLib.sat(s2_pc) {
    node1 := new Node(s1_state, s1_pc);
    node1_maybe, node2_maybe := scheduler.Enqueue(node1, null);
  } else {
    node1 := new Node(s1_state, s1_pc);
    node2 := new Node(s2_state, s2_pc);

    // Used for King 2
    assert !SatLib.sat(SatLib.and(s1_pc, s2_pc));
    assert !SatLib.sat(SatLib.and(node1.pc, node2.pc));

    node1_maybe, node2_maybe := scheduler.Enqueue(node1, node2);
  }
}

/*
module SAT_Func{
import opened dpll : DPLL
import opened PropLogic

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
*/

