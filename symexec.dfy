//We need to define State, it should have: PC, variables, variables to
//values mapping, instructions, and a function to get the next instruction.

//We need to build the scheduler.  It needs to do bookkeeping and build a tree
//about which we can prove the properties from the king paper.

//PC is a boolean expression over symbolic inputs (values).  Need to have
//update functions for this to be used in exec.  The important thing with
//PC is that we can give it to a SAT solver.  Assuming we want this to run code
//beyond a proof, that means calling a solver from dafny, and ensuring the PC
//conforms to the solver's interface.

method main(scheduler: array<State>)
{
//XXX: need to initialize scheduler before this is called.

 while scheduler != empty
 {
   state = pop(scheduler)
   next_states = exec(state)
   add(scheduler, next_states)
 }
}

method exec(state: State)
{
  nIn = nextIns(state))
  //Depending on how we model memory, it might not matter if the
  //instruction is symbolic or not.
  if (!isSymb(nIn)
  {
    return doStuff()
  }
  else if (isPC(nIn))
  {
    return doStuffSymbolic()
  }
  else{
    Right = state
    Left = state
    PC(Right) = PC(Right) && nextIns(state)
    PC(Left) = PC(Left) && !nextIns(state)
    return (doStuff(Left), doStuff(Right))
  }
}
