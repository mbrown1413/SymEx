//We need to define State, it should have: PC, variables, variables to
//values mapping, instructions, and a function to get the next instruction.

//We need to build the scheduler.  It needs to do bookkeeping and build a tree
//about which we can prove the properties from the king paper.

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
