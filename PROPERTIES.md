
In a 1976 paper entitled "Symbolic execution and program testing," James C.
King described symbolic execution and pointed out some properties that symbolic
executor have. The properties that SymEx proves are taken from the King paper.
We have creatively named them King 1, King 2 and King 3.

    J.C. King.  Symbolic execution and program testing. Communications of the ACM 19(7), 385–394 (1976)

SymEx produces a full execution tree, which these properties are asserted on.
We make assumptions that the SAT solver we use behaves correctly, which is
expressed in code in `sat.dfy`.

Here are some resources I found helpful in figuring out how to prove things in Dafny:
  * [Dafny troubleshooting guide](http://www.cse.chalmers.se/edu/year/2016/course/TDA567_Testing_debugging_and_verification/dafny_troubleshooting.pdf) - Some good tips and a guide to common verification errors.
  * [Dafny Digest](https://www.cse.unsw.edu.au/~se2011/16s1/lectures/DafnyTerm3.pdf) - A few examples.
  * [Rigorous Software Development, Lecture 9](http://cs.nyu.edu/wies/teaching/rsd-13/material/lec09.pdf) - More examples.


## King 1

Every node must be satisfiable. For every node's path condition `pc`, it must
be satisfiable: `sat(pc)`

See `king2()` in `symexec.dfy` for the predicate for this property.

### Verification

This property is simple to verify since we explicitly don't enqueue nodes to
the scheduler if the path condition is not satisfyable. We simply added this as
a loop invariant in the main loop and in `StepExecution()`. We also make the
`Node` class so we can't create any nodes with unsatisfiable path conditions.


## King 2

Every leaf node must have a distinct path condition. For every pair of leaf
nodes, the conjunction of their path conditions `pc1` and `pc2` must not be
satisfiable: `!sat(and(pc1, pc2))`

See `king1()` in `symexec.dfy` for the predicate for this property.

### Verification

`StepExecution()` and `Scheduler.Enqueue()` contain the major proof
obligations.  `Scheduler.Enqueue()` requires and ensures king2, but it has some
preconditions needed to prove that king2 is a postcondition, namely that the
input nodes don't have overlapping pc's with any other leaves (except parent)
and the two input nodes don't overlap with each other. `StepExecution()` must
prove that these preconditions hold. It does so using basic boolean axioms
that are assumed by the sat interface (see sat.dfy).


## King 3

This is King's commutativity property.

Have not specified or verified this.
