// Implements scheduler with the Scheduler class.

class {:autocontracts} Node
{
  var state: State;
  var pc: SatLib.BoolExpr;
  constructor (input_state: State, input_pc: SatLib.BoolExpr)
    requires SatLib.sat(input_pc)
    ensures SatLib.sat(pc)
    ensures state == input_state
    ensures pc == input_pc
  {
    state, pc := input_state, input_pc;
  }
}
datatype NodeMaybe = Some(v:Node) | None

// Scheduler
// Stores a tree where each node contains a state and the path condition
// that leads to that state. When a state only has one possible next
// state, the node will be NodeMaybe.None, otherwise in will be
// Some(Node).
//
// The enqueue operations assign children to the last dequeued node. All
// children of a dequeued node should be enqueued before the next item
// is dequeued.
//
// Alternate array-base queue implementation found in:
//   "Developing Verified Programs with Dafny", figure 4.
//   https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml233.pdf
class {:autocontracts false} Scheduler
{

  // Stores tree for states and path condition
  var a: array<NodeMaybe>;

  // Indexes into "a".
  // start points to the last dequeued node.
  // end points to the highest index None enqueued.
  var start: int, end: int;

  predicate Valid()
    reads *
  {
    a != null &&
    -1 <= start <= end < a.Length &&
    end >= 0 &&

    // Used for King 2
    (forall i :: 0 <= end < i < a.Length ==> a[i].None?) &&
    2*start + 2 >= end &&

    a.Length >= 1
  }

  constructor (initState: State)
    modifies this
    ensures Valid()
    ensures a != null
    ensures start == -1 && end == 0
    ensures a.Length == 1 && match a[0]
      case Some(node) => node != null &&
                         node.pc == SatLib.getTrueBool() &&
                         node.state == initState &&
                         fresh(node)
      case None => false;
    ensures !IsEmpty()
    ensures fresh(a)
  {
    a := new NodeMaybe[1];
    start := -1;
    end := 0;
    var node := new Node(initState, SatLib.getTrueBool());
    a[0] := NodeMaybe.Some(node);
  }

  // Enqueues the nodes lc and rc as children of the last dequeued node.
  method Enqueue(lc: Node, rc: Node)
    requires Valid()
    ensures Valid()
    modifies this

    requires start >= 0  // There has been a dequeue
    requires a[start].Some?

    // Used for King Property 1
    requires lc == null || SatLib.sat(lc.pc)
    requires rc == null || SatLib.sat(rc.pc)
    requires king1(this)
    ensures king1(this)

    // Used for King Property 2
    requires king2(this)
    ensures king2(this)
    ensures end >= old(end)
    requires isLeaf(start, a);
    // input nodes must not be sat with any leaves, except start
    requires forall i :: 0 <= i < a.Length ==>
      var node_i := match a[i] case Some(node) => node case None => null;
      node_i != null && i != start &&
      isLeaf(i, a)
      ==> (
        (lc != null ==> !SatLib.sat(SatLib.and(node_i.pc, lc.pc))) &&
        (rc != null ==> !SatLib.sat(SatLib.and(node_i.pc, rc.pc)))
      );
    // King 2 between lc and rc
    requires (lc != null && rc != null) ==> !SatLib.sat(SatLib.and(lc.pc, rc.pc));

    ensures fresh(a)
  {
    var l_index := 2*start + 1;  // right/left children indices
    var r_index := 2*start + 2;

    // Grow tree if needed
    a := expandTree(a, r_index);
    assert Valid();
    assert king2(this);

    // Set child nodes
    var lc_node := if lc != null then NodeMaybe.Some(lc) else NodeMaybe.None;
    var rc_node := if rc != null then NodeMaybe.Some(rc) else NodeMaybe.None;
    a[l_index] := lc_node;
    a[r_index] := rc_node;
    end := r_index;

    // Parent is no longer a leaf and children are now leaves
    assert (lc_node.Some? || rc_node.Some?) ==> !isLeaf(start, a);
    assert a[l_index].Some? ==> isLeaf(l_index, a);
    assert a[r_index].Some? ==> isLeaf(r_index, a);

  }

  method Dequeue() returns (d: Node)
    requires Valid()
    ensures Valid()

    ensures -1 <= old(start) < start < a.Length
    ensures a[start] == a[old(start)+1];
    ensures d != null ==> a[start].Some?
    ensures d != null ==> d == a[start].v
    requires -1 <= start < a.Length-1

    // Deque'd elements must be leaves
    ensures start >= a.Length || a[start].None? || isLeaf(start, a)

    // Used for King Property 1
    requires king1(this)
    ensures king1(this)
    requires match a[start+1]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures d == null || SatLib.sat(d.pc)

    // Used for King Property 2
    requires king2(this)
    ensures king2(this)
    ensures end == old(end)

    requires !IsEmpty()
    modifies this
  {
    start := start+1;
    d := match a[start]
      case Some(node) => node
      case None => null;
  }

  function method IsEmpty(): bool
    requires Valid()
    ensures Valid()
    reads *

    requires king1(this)
    ensures king1(this)
  {
    start == end
  }

  method PrintTree() returns ()
      requires a != null
    {
    var i := 0;
    while i < a.Length
      decreases a.Length - i
    {
      print "tree[", i, "] = ";
      match a[i] {
        case Some(node) =>
          if node == null {
            print "NULL";
          } else {
            print "Node(\n";
            print "    pc = ", node.pc, "\n";
            print "    state = ", node.state, "\n";
            print ")\n";
          }
        case None =>
          print "None\n";
      }
      i := i + 1;
    }
  }

}

// Expand tree "a" with "defaultValue" so "a[index]" is within the array bounds.
method expandTree(a: array<NodeMaybe>, index: int) returns (b: array<NodeMaybe>)
  requires a != null
  requires 0 <= index < 2*(a.Length+1)-1

  ensures b != null
  ensures a.Length <= b.Length
  ensures index < b.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] == b[i]
  ensures forall i :: a.Length <= i < b.Length ==> b[i].None?
  ensures fresh(b)

{

  // Expand array if needed
  var new_len := a.Length;
  if a.Length <= index {
    new_len := 2*(a.Length+1)-1;  // Next (2^i)-1
  }
  assert new_len > index;

  // Create fresh copy of "a"
  b := new NodeMaybe[new_len];
  forall i | 0 <= i < b.Length
  { // Set to None
    b[i] := NodeMaybe.None;
  }
  forall i | 0 <= i < a.Length
  { // Copy a to b
    b[i] := a[i];
  }

  return b;
}

function method isLeaf(nodeIndex: int, tree:array<NodeMaybe>): bool
  requires tree != null
  requires 0 <= nodeIndex < tree.Length
  reads tree
{
  var l_child := 2*nodeIndex+1;
  var r_child := 2*nodeIndex+2;
  if tree[nodeIndex].None? then
    false  // Calling isLeaf on non-existent node.
  else if r_child < tree.Length then
    // Both children must be None to be a leaf.
    assert l_child < tree.Length;
    tree[l_child].None? && tree[r_child].None?
  else
    // Children are off the end of the array, they are assumed
    // None.
    true
}
