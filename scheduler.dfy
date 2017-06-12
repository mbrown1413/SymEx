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
    ensures !isEmpty()
    ensures fresh(a)
  {
    a := new NodeMaybe[1];
    start := -1;
    end := 0;
    var node := new Node(initState, SatLib.getTrueBool());
    a[0] := NodeMaybe.Some(node);
  }

  method Enqueue(lc: Node, rc: Node) returns (lc_node: NodeMaybe, rc_node: NodeMaybe)
    requires Valid()
    ensures Valid()
    modifies this

    requires start >= 0
    requires a[start].Some?

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
    requires forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;

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

    //assert r_index > end;
    //assert forall i :: r_index < i < a.Length ==> a[i].None?;

    a := expandTree(a, r_index);

    assert Valid();
    assert king2(this);

    lc_node := if lc != null then NodeMaybe.Some(lc) else NodeMaybe.None;
    rc_node := if rc != null then NodeMaybe.Some(rc) else NodeMaybe.None;
    a[l_index] := lc_node;
    a[r_index] := rc_node;
    end := r_index;

    assert (lc_node.Some? || rc_node.Some?) ==> !isLeaf(start, a);
    assert a[l_index].Some? ==> isLeaf(l_index, a);
    assert a[r_index].Some? ==> isLeaf(r_index, a);

    // King 2 between lc, rc and other leaves
    assert forall i :: 0 <= i < a.Length ==>
      var node_i := match a[i] case Some(node) => node case None => null;
      node_i != null && isLeaf(i, a)
      ==> (
        ((lc != null && i != l_index) ==> !SatLib.sat(SatLib.and(node_i.pc, lc.pc))) &&
        ((rc != null && i != r_index) ==> !SatLib.sat(SatLib.and(node_i.pc, rc.pc)))
      );

    assert king2(this);

    // lc and rc become leaves, and start is no longer a leaf
    //assert forall i :: r_index < i < a.Length ==> a[i].None?;
    //assert (a[l_index].None? && a[r_index].None?) || !isLeaf(start, a);
    //assert a[l_index].Some? ==> isLeaf(l_index, a);
    //assert a[r_index].Some? ==> isLeaf(r_index, a);

    //assert match a[l_index]
    //  case None => true
    //  case Some(node) => lc == null || node.pc == lc.pc;
    //assert match a[r_index]
    //  case None => true
    //  case Some(node) => rc == null || node.pc == rc.pc;

    // King 2 for all the nodes not modified
    //assert forall i,j :: 0 <= i < a.Length && 0 <= j < a.Length ==>
    //  var node_i := match a[i] case Some(node) => node case None => null;
    //  var node_j := match a[j] case Some(node) => node case None => null;
    //  node_i != null && node_j != null && i != j &&
    //  isLeaf(i, a) &&
    //  isLeaf(j, a) &&
    //  i != l_index && i != r_index && j != l_index && j != r_index
    //  ==> !SatLib.sat(SatLib.and(node_i.pc, node_j.pc));

    //assert 
    //  var node_l := match a[l_index] case Some(node) => node case None => null;
    //  var node_r := match a[r_index] case Some(node) => node case None => null;
    //  node_l != null && node_r != null
    //  ==> !SatLib.sat(SatLib.and(node_l.pc, node_r.pc)) &&
    //      !SatLib.sat(SatLib.and(node_r.pc, node_l.pc));

    //assert forall i,j :: 0 <= i < a.Length && 0 <= j < a.Length ==>
    //  var node_i := match a[i] case Some(node) => node case None => null;
    //  var node_j := match a[j] case Some(node) => node case None => null;
    //  node_i != null && node_j != null && i != j &&
    //  isLeaf(i, a) &&
    //  isLeaf(j, a) &&
    //  ((i == l_index && j == r_index) || (i == r_index && j == l_index)) &&
    //  (i != l_index || i != r_index || j != l_index || j != r_index)
    //  ==> !SatLib.sat(SatLib.and(node_i.pc, node_j.pc));

    //assert forall i,j :: 0 <= i < a.Length && 0 <= j < a.Length ==>
    //  var node_i := match a[i] case Some(node) => node case None => null;
    //  var node_j := match a[j] case Some(node) => node case None => null;
    //  node_i != null && node_j != null && i != j &&
    //  isLeaf(i, a) &&
    //  isLeaf(j, a) &&
    //  !((i == l_index && j == r_index) || (i == r_index && j == l_index)) &&
    //  (i != l_index || i != r_index || j != l_index || j != r_index)
    //  ==> !SatLib.sat(SatLib.and(node_i.pc, node_j.pc));

    //assert forall i,j :: 0 <= i < a.Length && 0 <= j < a.Length ==>
    //  var node_i := match a[i] case Some(node) => node case None => null;
    //  var node_j := match a[j] case Some(node) => node case None => null;
    //  node_i != null && node_j != null && i != j &&
    //  isLeaf(i, a) &&
    //  isLeaf(j, a)
    //  ==> !SatLib.sat(SatLib.and(node_i.pc, node_j.pc));

    return lc_node, rc_node;
  }
  
  method Dequeue() returns (d: Node)
    requires Valid()
    ensures Valid()

    ensures -1 <= old(start) < start < a.Length
    ensures a[start] == a[old(start)+1];
    ensures d != null ==> a[start].Some?
    ensures d != null ==> d == a[start].v

    // Deque'd elements must be leaves
    ensures start >= a.Length || a[start].None? ||isLeaf(start, a)

    // Used for King Property 1
    requires -1 <= start < a.Length-1
    requires match a[start+1]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures d == null || SatLib.sat(d.pc)

    requires forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => true;

    // Used for King Property 2
    requires king2(this)
    ensures king2(this)
    ensures end == old(end)
    //requires 2*start+2 >= end

    requires !isEmpty()

    modifies this
  {
    start := start+1;
    d := match a[start]
      case Some(node) => node
      case None => null;
  }
  
  function method isEmpty(): bool
    requires Valid()
    ensures Valid()
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

  method printTree() returns ()
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
            print "  ", node.state, "  ", SatLib.boolExprToStr(node.pc), "\n";
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

  // Used for King 2
  // Leaveness is the same. Expansed None nodes are not leaves
  //ensures forall i :: 0 <= i < a.Length ==> (isLeaf(i, a) == isLeaf(i, b));
  //ensures forall i :: a.Length <= i < b.Length ==> !isLeaf(i, b);

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

  //assert a.Length <= b.Length;
  //assert forall k :: 0 <= k < a.Length ==> a[k] == b[k];
  //assert forall k :: a.Length <= k < b.Length ==> b[k].None?;

  //assert forall k :: 0 <= k < 2*k+2 < a.Length ==> (isLeaf(k, a) ==> isLeaf(k, b));
  //assert forall k :: a.Length <= k < 2*k+2 < b.Length ==> end < 2*k+2;
  //assert forall k :: a.Length <= k < 2*k+2 < b.Length ==> (isLeaf(k, a) ==> isLeaf(k, b));
  //assert forall k :: 0 <= k < a.Length <= 2*k+2 < b.Length ==> (isLeaf(k, a) ==> isLeaf(k, b));
  //assert forall k :: 0 <= k < a.Length ==> (isLeaf(k, a) ==> isLeaf(k, b));
  //assert forall k :: 0 <= k < a.Length ==> (!isLeaf(k, a) ==> !isLeaf(k, b));
  //assert forall i :: 0 <= end < i < a.Length ==> a[i].None?;
  //assert forall k :: 0 <= k < a.Length ==> (isLeaf(k, a) == isLeaf(k, b));

  //assert forall k :: a.Length <= k < b.Length ==> !isLeaf(k, b);

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

// Is node at idx1 ancestor of node at idx2?
function isAncestor(idx1: int, idx2: int): bool
  requires idx1 >= 0 && idx2 >= 0
{
  if idx1 == 0 then
    true
  else if idx2 == 0 then
    false
  else
    exists i :: 0 <= i ==> idx2 / pow2(i) == idx1
}

function pow2(n: int): int
  decreases n
  requires n >= 0
  ensures pow2(n) > 0
{
  if (n == 0) then 1 else 2 * pow2(n-1)
}
