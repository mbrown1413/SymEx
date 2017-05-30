// Implements scheduler with the TreeQueue class.

class {:autocontracts} Node
{
  var state: State;
  var pc: SatLib.BoolExpr;
  constructor (input_state: State, input_pc: SatLib.BoolExpr)
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
  // start points to the next node to be dequeued.
  // end points to the highest non-None node in the tree.
  var start: int, end: int;

  predicate Valid() {
    (a != null) && (0 <= start <= end < a.Length) && a.Length > 1
  }

  constructor ()
    ensures a != null
    ensures forall i :: 0 <= i < a.Length ==> match a[i]
      case Some(node) => node != null && SatLib.sat(node.pc)
      case None => false;
  {
    a, start, end := new NodeMaybe[10], 0, 0;
  }

  method getTree() returns (T: array<NodeMaybe>)
  {
    T := new NodeMaybe[a.Length];
    T := a;
  }

  method DoubleEnqueue(lc: Node, rc: Node)
    ensures 0 <= 2*start + 2 < a.Length
    ensures match a[2*start + 1]
        case Some(n) => n == lc
        case None => false
    ensures match a[2*start + 2]
        case Some(node) => node == rc
        case None => false
  {

    var b := new NodeMaybe[2*(a.Length+1)-1];
    assert a.Length < b.Length;

    // Copy a to b
    forall i | 0 <= i < a.Length < b.Length
    {
      b[i] := a[i];
    }
    assert forall k :: 0 <= k < a.Length < b.Length ==> a[k] == b[k];

    b[2*start + 1]:= NodeMaybe.Some(lc);
    b[2*start + 2]:= NodeMaybe.Some(rc);
    a, end := b, 2*start + 2;
  }
  
  method LeftEnqueue(d: Node)
    ensures a[2*(start-1)+1] == NodeMaybe.Some(d);
    ensures a[2*(start-1)+2] == NodeMaybe.None;
  {
    var b := new NodeMaybe[3 * a.Length];
    b := a;
    b[2*(start-1)+1]:= NodeMaybe.Some(d);
    b[2*(start-1)+2]:= NodeMaybe.None;
    a, end := b, 2*(start-1)+1;
  }
  
  method RightEnqueue(d: Node)
    ensures a[2*(start-1)+1] == NodeMaybe.None;
    ensures a[2*(start-1)+2] == NodeMaybe.Some(d);
  {
    var b := new NodeMaybe[3 * a.Length];
    b := a;
    b[2*(start-1)+1]:= NodeMaybe.None;
    b[2*(start-1)+2]:= NodeMaybe.Some(d);
    a, end := b, 2*(start-1)+2;
  }
  
  method Dequeue() returns (d: Node)
    ensures a[start] == a[old(start)+1];
  {
    start := start+1;
    d := match a[start]
      case Some(node) => node
      case None => null;
  }
  
  function method isEmpty(): bool
    ensures isEmpty() ==> forall i :: end < i <= a.Length ==> a[i].None?
  { 
    a[end] == NodeMaybe.None
  } 
}

function method isLeaf(nodeIndex: int, tree:array<NodeMaybe>): bool
{
  (tree[2*nodeIndex+1].Some?) && (tree[2*nodeIndex+2].Some?)
}
