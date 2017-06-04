// Implements scheduler with the TreeQueue class.

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

// TreeQueue
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
class {:autocontracts false} TreeQueue
{

  // Stores tree for states and path condition
  var a: array<NodeMaybe>;

  // Indexes into "a".
  // start points to the last dequeued node.
  // end points to the highest index None enqueued.
  var start: int, end: int;

  //ghost var states: set<object>;

  predicate Valid()
    reads this
  {
    a != null &&
    -1 <= start <= end < a.Length &&
    end >= 0 &&
    a.Length >= 1
  }

  constructor (initState: State)
    modifies this
    ensures Valid()
    ensures a != null
    ensures start == -1 && end == 0
    ensures a.Length == 1 && match a[0]
      case Some(node) => node != null &&
                         node.pc == getTrueBool() &&
                         node.state == initState
      case None => false;
    ensures forall i :: 0 <= i <= end ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures !isEmpty()
    //ensures fresh(this)
    ensures fresh(a)
    ensures fresh(a[0])
  {
    a := new NodeMaybe[1];
    start := -1;
    end := 0;
    var node := new Node(initState, getTrueBool());
    a[0] := NodeMaybe.Some(node);
    //states := {};
  }

  method Enqueue(lc: Node, rc: Node) returns (lc_node: NodeMaybe, rc_node: NodeMaybe)
    requires Valid()
    ensures Valid()
    modifies this
    //modifies a
    //modifies states

    requires start >= 0
    ensures 0 <= 2*start + 1 < a.Length
    ensures 0 <= 2*start + 2 < a.Length
    ensures match a[2*start + 1]
        case Some(n) => n == lc
        case None => lc == null
    ensures match a[2*start + 2]
        case Some(node) => node == rc
        case None => rc == null

    // Used for King Property 1
    requires lc == null || SatLib.sat(lc.pc)
    requires rc == null || SatLib.sat(rc.pc)
    requires forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;
    ensures forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;
    requires forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;

    ensures fresh(a)
    //ensures a == old(a) || fresh(a)
    //ensures lc_node == null || match
    //ensures forall i :: 0 <= i < a.Length ==> fresh(a[i]) || a[i] == old(a[i])
    //ensures forall i :: 0 <= i < a.Length ==> fresh(a[i]) || a[i].None? || (i < old(a.Length) && a[i] == old(a[i]))
  {
    //states := states + {lc.state, rc.state};
    var l_index := 2*start + 1;  // right/left children indices
    var r_index := 2*start + 2;

    // Expand array if needed
    /*
    if a.Length <= r_index {
      var new_len := 2*(a.Length+1)-1;  // Next (2^i)-1
      assert new_len > r_index;
      var b := new NodeMaybe[new_len];
      assert a.Length < b.Length;
      forall i | 0 <= i < b.Length
      { // Set to None
        b[i] := NodeMaybe.None;
      }
      forall i | 0 <= i < a.Length < b.Length
      { // Copy a to b
        b[i] := a[i];
      }
      assert forall k :: 0 <= k < a.Length < b.Length ==> a[k] == b[k];
      a := b;
    }
    */
    var new_len;
    if a.Length <= r_index {
      new_len := 2*(a.Length+1)-1;  // Next (2^i)-1
      assert new_len > r_index;
    } else {
      new_len := a.Length;
    }
    var b := new NodeMaybe[new_len];
    assert a.Length <= b.Length;
    forall i | 0 <= i < b.Length
    { // Set to None
      b[i] := NodeMaybe.None;
    }
    forall i | 0 <= i < a.Length < b.Length
    { // Copy a to b
      b[i] := a[i];
    }
    assert forall k :: 0 <= k < a.Length < b.Length ==> a[k] == b[k];
    a := b;

    assert forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;
    assert forall i :: 0 <= i < a.Length ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;

    assert a.Length > r_index > l_index >= 0;
    assert lc == null || SatLib.sat(lc.pc);
    assert rc == null || SatLib.sat(rc.pc);

    lc_node := if lc != null then NodeMaybe.Some(lc) else NodeMaybe.None;
    rc_node := if rc != null then NodeMaybe.Some(rc) else NodeMaybe.None;
    assert match lc_node
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    assert match rc_node
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    a[l_index] := lc_node;
    a[r_index] := rc_node;

    assert forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;

    // Nodes between old end and l_index must be set to null.
    forall i | end < i < l_index
    {
      a[i] := NodeMaybe.None;
    }
    assert forall i :: end <= i < r_index ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;

    end := r_index;

    assert forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;

    return lc_node, rc_node;
  }
  
  method Dequeue() returns (d: Node)
    requires Valid()
    ensures Valid()

    ensures -1 <= old(start) < start < a.Length
    ensures a[start] == a[old(start)+1];

    // Used for King Property 1
    ensures forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;
    requires forall i :: 0 <= i <= end ==>
      match a[i]
        case Some(node) => node != null && SatLib.sat(node.pc)
        case None => true;
    requires -1 <= start < a.Length-1
    requires match a[start+1]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    requires start < end
    ensures d == null || SatLib.sat(d.pc)

    requires forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;

    requires !isEmpty()

    modifies this
  {
    start := start+1;
    d := match a[start]
      case Some(node) => node
      case None => null;
    assert d == null || SatLib.sat(d.pc);
  }
  
  function method isEmpty(): bool
    requires Valid()
    ensures Valid()
    reads this
    reads a
    reads *

    requires forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
  { 
    //forall i :: start <= i <= end ==> a[i].None?
    start == end
  } 
}

function method isLeaf(nodeIndex: int, tree:array<NodeMaybe>): bool
{
  true//tree[2*nodeIndex+1].Some? && tree[2*nodeIndex+2].Some?
}

//// Is node at idx1 ancestor of node at idx2?
//function isAncestor(idx1: int, idx2: int): bool
//{
//  exists i :: 0 <= i ==> idx2 / pow2(i) == idx1
//}
//
//function pow2(n: int): int
//  requires n >= 0
//{
//  if (n == 0) then 1 else 2 * pow2(n-1)
//}
