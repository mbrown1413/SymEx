
using System;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Numerics;

namespace @NetworkSatLib {

  public class BoolExpr
  {
    public string expr;
    public BoolExpr(string s) {
      expr = s;
    }
  }

  public class IntExpr
  {
    public string expr;
    public IntExpr(string s) {
      expr = s;
    }
  }

  public partial class __default {

    public static void getTrueBool(out BoolExpr e) {
      e = new BoolExpr("True");
    }
    public static BoolExpr getTrueBool() {
      BoolExpr e;
      getTrueBool(out e);
      return e;
    }

    public static void and(BoolExpr f1, BoolExpr f2, out BoolExpr e) {
      e = new BoolExpr(String.Format(
        "z3.And({0}, {1})",
        f1.expr, f2.expr
      ));
    }
    public static BoolExpr and(BoolExpr f1, BoolExpr f2) {
      BoolExpr e;
      and(f1, f2, out e);
      return e;
    }

    public static void not(BoolExpr f1, out BoolExpr e) {
      e = new BoolExpr(String.Format(
        "z3.Not({0})",
        f1.expr
      ));
    }
    public static BoolExpr not(BoolExpr f1) {
      BoolExpr e;
      not(f1, out e);
      return e;
    }

    public static void boolToInt(BoolExpr b, out IntExpr e) {
      e = new IntExpr(String.Format(
        "z3.If({0}, 1, 0)",
        b.expr
      ));
    }
    public static IntExpr boolToInt(BoolExpr b) {
      IntExpr e;
      boolToInt(b, out e);
      return e;
    }

    public static void boolExprToStr(BoolExpr b, out string e) {
      e = b.expr;
    }
    public static string boolExprToStr(BoolExpr b) {
      string e;
      boolExprToStr(b, out e);
      return e;
    }


    public static void intConst(BigInteger i, out IntExpr e) {
      e = new IntExpr(String.Format(
        "z3.IntVal(\"{0}\")",
        i
      ));
    }
    public static IntExpr intConst(BigInteger i) {
      IntExpr e;
      intConst(i, out e);
      return e;
    }

    public static void intSymbolic(BigInteger i, out IntExpr e) {
      e = new IntExpr(String.Format(
        "z3.Int(\"reg{0}\")",
        i
      ));
    }
    public static IntExpr intSymbolic(BigInteger i) {
      IntExpr e;
      intSymbolic(i, out e);
      return e;
    }

    public static void add(IntExpr f1, IntExpr f2, out IntExpr e) {
      e = new IntExpr(String.Format(
        "({0} + {1})",
        f1.expr, f2.expr
      ));
    }
    public static IntExpr add(IntExpr f1, IntExpr f2) {
      IntExpr e;
      add(f1, f2, out e);
      return e;
    }

    public static void cmp(IntExpr f1, IntExpr f2, out BoolExpr e) {
      e = new BoolExpr(String.Format(
        "({0} == {1})",
        f1.expr, f2.expr
      ));
    }
    public static BoolExpr cmp(IntExpr f1, IntExpr f2) {
      BoolExpr e;
      cmp(f1, f2, out e);
      return e;
    }

    public static bool sat(BoolExpr f1) {
      string answer = makeTcpRequest(f1.expr);
      return answer == "Y";
    }
    public static string makeTcpRequest(string s) {
      // Modified from: 
      //   https://www.devarticles.com/c/a/C-Sharp/Network-Programming-in-C-sharp/1/
      IPAddress addr = IPAddress.Loopback;
      EndPoint ep = new IPEndPoint(addr, 8000);

      Socket sock = new Socket(AddressFamily.InterNetwork,SocketType.Stream,ProtocolType.Tcp);
      sock.Connect(ep);

      string request_string = s + '\n';
      Encoding ASCII = Encoding.ASCII;
      Byte[] ByteGet = ASCII.GetBytes(request_string);
      Byte[] RecvBytes = new Byte[256];

      sock.Send(ByteGet, ByteGet.Length, 0);
      Int32 bytes = sock.Receive(RecvBytes, RecvBytes.Length, 0);
      String strRetPage = null;
      strRetPage = strRetPage + ASCII.GetString(RecvBytes, 0, bytes);
      while (bytes > 0)
      {
        bytes = sock.Receive(RecvBytes, RecvBytes.Length, 0);
        strRetPage = strRetPage + ASCII.GetString(RecvBytes, 0, bytes);
        //Console.WriteLine(strRetPage );
      }
      sock.Shutdown(SocketShutdown.Both);
      sock.Close();
      Console.WriteLine(strRetPage);
      return strRetPage;
    }

  }

}
