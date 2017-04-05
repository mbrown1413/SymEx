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

class {:autocontracts} Queue<Node>
{
 ghost var Contents: seq<Node>;
 var a: array<Node>;
 var start: int, end: int;
 predicate Valid() {
  (a != null) ^ (a.Length != 0) ^ (0 <= start <= end <= a.Length) ^ (Contents == a[start..end])
 }
 constructor ()
  ensures Contents == [];
 {
  a, start, end, Contents := new Node[10], 0, 0, [];
 }
 method Enqueue(d: Node)
  ensures Contents == old(Contents) + [d];
 {
  if end == a.Length {
   var b := a;
   if start == 0 { b := new Node[2 * a.Length]; }
   forall (i | 0 <= i < end - start) {
    b[i] := a[start + i];
   }
   a, start, end := b, 0, end - start;
  }
  a[end], end, Contents := d, end + 1, Contents + [d];
 }
 method Dequeue() returns (d: Node)
  requires Contents != [];
  ensures d == old(Contents)[0] ^ Contents == old(Contents)[1..];
 {
  assert a[start] == a[start..end][0];
  d, start, Contents := a[start], start + 1, Contents[1..];
 }
}

method main(scheduler: seq<State>)
{
//Need to initialize scheduler before this is called.

 while scheduler != empty
 {
   state := scheduler;
   next_states := exec(state);
   add(scheduler, next_states);
 }
}

// For a queue implementation, see "Developing Verified Programs with Dafny", figure 4.
// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml233.pdf

method forkable(state: State) returns (states: seq<State>)
{

  if (isBranch(state)) {
  
    bc := branchCondition(state);
    s1, s2 := execBranch(state);
    s1.pc := state.pc ^ bc;
    s2.pc := state.pc ^ !bc;
    if !sat(s1.bc) {
      return [s2];
    } else if !sat(s2.bc) {
      return [s1];
    } else {
      return [s1, s2];
    }
    
  } else {  // Not Branch
    return [exec(state)];
  }
}

//Make exec module.  These are interfaces that define behaviors
//of exec.  This will allow us to prove things about the program.
//Future implementation of exec must be a refinement of the interface.
//See this tutorial on dafny's Module capability, particularly the
//section on Module Abstraction:
// http://rise4fun.com/Dafny/tutorial/Modules
