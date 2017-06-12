
using System;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Numerics;

using Microsoft.Z3;

namespace @NetworkSatLib {

  public class BoolExpr
  {
    public Microsoft.Z3.BoolExpr expr;   
    public BoolExpr(Microsoft.Z3.BoolExpr s) {
      expr = s;
    }
  }

  public class IntExpr
  {
    public Microsoft.Z3.ArithExpr expr;
    public IntExpr(Microsoft.Z3.ArithExpr s) {
      expr = s;
    }
  }

  public partial class __default {
    static Microsoft.Z3.Context ctx;

    public static void getTrueBool(out BoolExpr e) {
      e = new BoolExpr(ctx.MkTrue()); 

    }
    public static BoolExpr getTrueBool() {
      BoolExpr e;
      getTrueBool(out e);
      return e;
    }

    public static void and(BoolExpr f1, BoolExpr f2, out BoolExpr e) {
      e = new BoolExpr(ctx.MkAnd(f1.expr, f2.expr));
    }

    public static BoolExpr and(BoolExpr f1, BoolExpr f2) {
      BoolExpr e;
      and(f1, f2, out e);
      return e;
    }

    public static void not(BoolExpr f1, out BoolExpr e) {
      e = new BoolExpr(ctx.MkNot(f1.expr));
    }
    public static BoolExpr not(BoolExpr f1) {
      BoolExpr e;
      not(f1, out e);
      return e;
    }

    public static void boolToInt(BoolExpr b, out IntExpr e) {
      e = new IntExpr((Microsoft.Z3.IntExpr)ctx.MkITE(b.expr, intConst(1).expr, intConst(0).expr));
    }
    public static IntExpr boolToInt(BoolExpr b) {
      IntExpr e;
      boolToInt(b, out e);
      return e;
    }

    public static void boolExprToStr(BoolExpr b, out string e) {
      e = b.expr.ToString();
    }
    public static string boolExprToStr(BoolExpr b) {
      string e;
      boolExprToStr(b, out e);
      return e;
    }


    public static void intConst(BigInteger i, out IntExpr e) {
      e = new IntExpr(ctx.MkInt((int)i));
    }
    public static IntExpr intConst(BigInteger i) {
      IntExpr e;
      intConst(i, out e);
      return e;
    }

    public static void intSymbolic(BigInteger i, out IntExpr e) {
      e = new IntExpr(ctx.MkIntConst("reg"+i.ToString()));
    }
    public static IntExpr intSymbolic(BigInteger i) {
      IntExpr e;
      intSymbolic(i, out e);
      return e;
    }

    public static void add(IntExpr f1, IntExpr f2, out IntExpr e) {
      e = new IntExpr(ctx.MkAdd(f1.expr, f2.expr));
    }
    public static IntExpr add(IntExpr f1, IntExpr f2) {
      IntExpr e;
      add(f1, f2, out e);
      return e;
    }

    public static void cmp(IntExpr f1, IntExpr f2, out BoolExpr e) {
       e = new BoolExpr(ctx.MkEq(f1.expr, f2.expr));
    }
    public static BoolExpr cmp(IntExpr f1, IntExpr f2) {
      BoolExpr e;
      cmp(f1, f2, out e);
      return e;
    }

    public static bool sat(BoolExpr f1) {
      Solver s = ctx.MkSolver();
      s.Assert(f1.expr);
      return s.Check() == Status.SATISFIABLE;
    }

  }

}





