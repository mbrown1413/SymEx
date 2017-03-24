method main(scheduler: array<State>)
{
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
