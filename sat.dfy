

extern "Z3SatLib" module Z3SatLib {

    type {:compile false} BoolExpr
    extern function method getTrueBool(): BoolExpr
    extern function method and(f1: BoolExpr, f2: BoolExpr): BoolExpr
    extern function method not(f1: BoolExpr): BoolExpr
    extern function method boolToInt(b: BoolExpr): IntExpr
    extern function method boolExprToStr(b: BoolExpr): string

    type {:compile false} IntExpr
    extern function method intConst(i: int): IntExpr
    extern function method intSymbolic(i: int): IntExpr
    extern function method add(f1: IntExpr, f2: IntExpr): IntExpr
    extern function method cmp(f1: IntExpr, f2: IntExpr): BoolExpr

    extern function method {:verify false} sat(f1: BoolExpr): bool

      // Following are all of the assumptions about the SAT solver we use for
      // our proofs.

      ////////////////////////////////////
      ///// Used for King Property 1 /////
      ////////////////////////////////////

      // Used to ensure the initial node in the scheduler is satisfyable.
      ensures sat(getTrueBool())


      ////////////////////////////////////
      ///// Used for King Property 2 /////
      ////////////////////////////////////

      // Negation Axiom of "and"
      // Used in "step_execution()" to prove two child pc's do not overlap.
      ensures forall a :: !sat(and(a, not(a)))

      // Zero Axiom of "and"
      // Used in "step_execution()" to prove !sat( and(pc1, pc2) ).
      // Used in "step_execution()" to prove new path conditions are not
      //   satisfyable with existing leaves.
      ensures forall a,b ::
        !sat(a) ==> !sat( and(a, b) )

      // Communativity of "and"
      // Used in "Scheduler.Enqueue()" to prove king2 postcondition.
      // Used in "step_execution()" to prove !sat( and(pc1, pc2) ).
      ensures forall a,b ::
        sat( and(a, b) ) ==
        sat( and(b, a) )

      // Associativity of "and"
      // Used in "step_execution()" to prove !sat( and(pc1, pc2) ).
      // Used in "step_execution()" to prove new path conditions are not
      //   satisfyable with existing leaves.
      ensures forall a,b,c :: ( !sat( and(and(a,b),c) ) )
                         <==> ( !sat( and(a,and(b,c)) ) );

}
