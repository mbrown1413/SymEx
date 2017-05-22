using System;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;

namespace @DimacsUtils {
  public partial class Dimacs
  {
    static string GetLine(string text, int lineNo)
    {
      string[] lines = text.Replace("\r", "").Split('\n');
      return lines.Length >= lineNo ? lines[lineNo] : null;
    }

    static int NumLines(string text)
    {
      return text.Replace("\r", "").Split('\n').Length;
    }

    static void FmlaFromString(string dimacs, out int[][] clauses)
    {
      clauses = null;

      int nlines = NumLines(dimacs);
      if (nlines < 2) return;

      int n = 0;
      var comment = true;
      while (comment) comment = GetLine(dimacs, n++).Split(' ')[0].Trim() == "c";
      n--;

      string[] metadata = GetLine(dimacs, n).Split(' ');
      if (metadata.Length < 4 || metadata[0] != "p" || metadata[1] != "cnf") return;

      int nvars = int.Parse(metadata[2]);
      int nclauses = int.Parse(metadata[3]);

      if (nlines < n + nclauses) return;
      n++;

      clauses = new int[nclauses][];
      for (int i = 0; i < nclauses; i++)
      {
        var line = GetLine(dimacs, n + i).Split(' ');
        int[] clause = Array.ConvertAll(line, int.Parse);
        clauses[i] = clause;
      }    
    }

    public static void FmlaFromFile(char[] filename, out int[][] clauses)
    {
      FmlaFromString(System.IO.File.ReadAllText(new string(filename)), out clauses);
    }
  }
}