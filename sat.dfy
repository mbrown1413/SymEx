
//TODO: Add "abstract" here once a concrete one is implemented.
abstract module AbstractSatLib {

    type BoolExpr
    function method getTrueBool(): BoolExpr
    function method and(f1: BoolExpr, f2: BoolExpr): BoolExpr
    function method not(f1: BoolExpr): BoolExpr
    function method boolToInt(b: BoolExpr): IntExpr
    function method boolExprToStr(b: BoolExpr): string

    type IntExpr
    function method intConst(i: int): IntExpr
    function method intSymbolic(i: int): IntExpr
    function method add(f1: IntExpr, f2: IntExpr): IntExpr
    function method cmp(f1: IntExpr, f2: IntExpr): BoolExpr

    function method {:verify false} sat(f1: BoolExpr): bool
      ensures sat(getTrueBool())

      // Used for King Property 1
      //TODO: Possibly derive this from simpler rules
      ensures forall a,b :: sat(a) ==>
        sat(and(a,b)) || sat(and(a,not(b)))

      // Used for King Property 2
      //ensures forall a :: !sat(and(a, not(a)))
      //ensures forall a,b,c,d ::
      //  sat(and( and(a, b), and(c, d) )) ==
      //  sat(and( and(a, c), and(b, d) ))
      //ensures forall a,b,c :: sat( and(and(a,b),c) ) <==> sat( and(a,and(b,c)) )
      ensures forall a,b ::
        !sat(a) ==> !sat( and(a, b) )
      ensures forall a,b ::
        sat( and(a, b) ) ==
        sat( and(b, a) )

}


extern "NetworkSatLib" module NetworkSatLib {

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

      // Used for King Property 1
      //TODO: Possibly derive this from simpler rules
      ensures sat(getTrueBool())
      ensures forall a,b :: sat(a) ==>
        sat(and(a,b)) || sat(and(a,not(b)))
      ensures forall a,b,c,d ::
        sat(and( and(a, b), and(c, d) )) ==
        sat(and( and(a, c), and(b, d) ))

      // Used for King Property 2
      ensures forall a :: !sat(and(a, not(a)))
      ensures forall a,b ::
        !sat(a) ==> !sat( and(a, b) )
      ensures forall a,b ::
        sat( and(a, b) ) ==
        sat( and(b, a) )
      ensures forall a,b,c :: ( !sat( and(and(a,b),c) ) )
                         <==> ( !sat( and(a,and(b,c)) ) );

}
