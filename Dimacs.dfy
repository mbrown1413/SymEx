
include "Io.dfy"
include "PropLogic.dfy"

extern "DimacsUtils" module DimacsUtils
{
  import opened DafnyIO  
  import opened PropLogic

  extern "Dimacs" class Dimacs
  {
    extern "FmlaFromFile" static method FmlaFromFile(name: array<char>) returns (phi: array<array<int32>>)

    static method convert_dimacs(benchmark: array<array<int32>>) returns (phi: Formula)
      requires benchmark != null
    {
      phi := [];

      var i:nat := 0;
      while(i < benchmark.Length) 
        invariant i <= benchmark.Length
      {
        var clause:seq<Literal> := [];
        var j:nat := 0;

        if(benchmark[i] != null) {      
          while(j < benchmark[i].Length-1)
            invariant benchmark[i] != null
            invariant j <= benchmark[i].Length
          {        
            var lit := (benchmark[i][j]) as int;
            var s := if lit < 0 then False else True;        
            clause := clause + [V(if lit < 0 then -1*lit else lit, s)];
            j := j + 1;
          }
        }

        phi := phi + [clause];
        i := i + 1;
      }
    }

  }
}
