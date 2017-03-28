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

method main(scheduler: array<State>)
{
//Need to initialize scheduler before this is called.

 while scheduler != empty
 {
   state = pop(scheduler)
   next_states = exec(state)
   add(scheduler, next_states)
 }
}

// For a queue implementation, see "Developing Verified Programs with Dafny", figure 4.
// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml233.pdf

method forkable(state: State)
{
  nIn = nextIns(state))
  //Depending on how we model memory, it might not matter if the
  //instruction is symbolic or not.
  if (!isSymb(nIn)
  {
    return exec()
  }
  else if (isPC(nIn))
  {
    return exec_symbolic()
  }
  else{
    Right = state
    Left = state
    PC(Right) = PC(Right) && nextIns(state)
    PC(Left) = PC(Left) && !nextIns(state)
    return (exec(Left), exec(Right))
  }
}

//Make exec module.  These are interfaces that define behaviors
//of exec.  This will allow us to prove things about the program.
//Future implementation of exec must be a refinement of the interface.
//XXX: Michael: add tutoiral explaining this.
