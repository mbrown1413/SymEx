
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

// King Property 1
// All nodes in the tree should be satisfyable.
//
// Verification: This property is simple to verify since we explicitly don't
// enqueue to the scheduler if the path condition is not satisfyable. We
// simply added this as a loop invariant in the main loop.
predicate king1(scheduler: Scheduler)
  requires scheduler != null
  requires scheduler.a != null
  reads *
{
  forall i :: 0 <= i < scheduler.a.Length ==> match scheduler.a[i]
    case Some(node) => node != null && SatLib.sat(node.pc)
    case None => true
}

// King Property 2
// Path conditions in leaf nodes do not overlap.
// That is, any assignment of variables leads to exactly one leaf node.
//
// Verification: "step_execution()" and "Scheduler.Enqueue()" have the major
// proof obligations. "Scheduler.Enqueue()" requires and ensures king2, but it
// has some preconditions needed to prove this, namely that the input nodes
// don't have overlapping pc's with any other leaves (except parent) and the
// two input nodes don't overlap with each other. "step_execution()" must prove
// that these preconditions hold. It does so using basic boolean axioms that
// are assumed by the sat interface (see sat.dfy).
predicate king2(scheduler: Scheduler)
  requires scheduler != null
  requires scheduler.a != null
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
method symex() returns (scheduler: Scheduler)
  decreases *
  ensures scheduler != null
  ensures scheduler.a != null
  ensures scheduler.a.Length >= 1

  ensures king1(scheduler)
  ensures king2(scheduler)
{
  var initState := getInitialState();
  scheduler := new Scheduler(initState);

  assert !scheduler.isEmpty();
  while !scheduler.isEmpty()
    decreases *
    invariant scheduler.a != null
    invariant scheduler.Valid()

    invariant king1(scheduler)
    invariant king2(scheduler)

  {
    var node := scheduler.Dequeue();
    if node != null {
      step_execution(scheduler, node);
    }

  }

  return scheduler;
}

// Enqueue the children of state_node, but only if their path condition
// is satisfyable.
method step_execution(scheduler: Scheduler, state_node: Node)
  requires scheduler != null
  requires scheduler.a != null
  requires state_node != null
  requires scheduler.Valid() && scheduler.start >= 0
  requires scheduler.a[scheduler.start].Some?
  requires scheduler.a[scheduler.start].v == state_node
  requires scheduler.start >= 0

  ensures scheduler.Valid()

  // Used for King 1
  requires king1(scheduler)
  ensures king1(scheduler)
  requires SatLib.sat(state_node.pc)

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

  // Path conditions for the nodes we are about to enqueue do not overlap with
  // any existing leaves, except the parent node.
  // Final precondition we need before Enqueue.
  // Uses: Associativity of "and"
  // Uses: Zero Axiom of "and"
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
  if SatLib.sat(s1_pc) && SatLib.sat(s2_pc) {
    node1 := new Node(s1_state, s1_pc);
    node2 := new Node(s2_state, s2_pc);

    // Used for King 2
    // Uses: Communativity of "and"
    // Uses: Associativity of "and"
    // Uses: Negation Axiom of "and"
    // Uses: Zero Axiom of "and"
    assert !SatLib.sat(SatLib.and(node1.pc, node2.pc));

  } else if SatLib.sat(s1_pc) {
    node1 := new Node(s1_state, s1_pc);
  } else if SatLib.sat(s2_pc) {
    node2 := new Node(s2_state, s2_pc);
  }

  scheduler.Enqueue(node1, node2);
}
