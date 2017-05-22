
include "Io.dfy"
include "Dimacs.dfy"
include "PropLogic.dfy"

module DPLL
{
  import opened DimacsUtils
  import opened DafnyIO
  import opened PropLogic

  method get_fmla_vars(phi: Formula) returns (vars: seq<Var>)
    decreases *
  {
    vars := [];
    var i := 0;

    while(i < |phi|)
    {
      var j := 0;
      var c := phi[i];

      while(j < |c|)
      {
        if(c[j].V? && c[j].v !in vars) { vars := vars + [c[j].v]; }
        j := j + 1;      
      }    
        
      i := i + 1;
    }    
  }

method eval_literal (I : Interpretation, a : Literal) returns (b : Option<bool>)
{
	if a.C? {
		if a.b == True{return Some(true);}
		else{return Some(false);}
	}
	else{
		if a.v !in I {return None;}
		if I[a.v].0 == a.s{return Some(true);}
		else{return Some(false);}
	}
}

method sat_clause (I : Interpretation, c : Clause) returns (b : Option<bool>)
	// If one of the literals is true, then the whole clause is true.
	// Else if one of the literals is unassigned, then returns None.
	// If all of the literals are assigned to false, then returns false.
{
	var i := 0;
	var counter := 0;
	while i < |c|{
		var v := eval_literal(I, c[i]);
		if v.Some? && v.value{
			return Some(true);
		}else{
			if v.None?{counter := counter + 1;}
		}
		i := i + 1;
		// assert !v.value; // ensures that all the literals are assigned to false.
	}
	if counter != 0{return None;}
	return Some(false);
}

method is_unit (I : Interpretation, c : Clause) returns (b : bool)
	// I does not satisfy c.
	// All but one literals in c are assigned.
{
	var sat_c := sat_clause(I, c);
	if sat_c.Some?{return false;}
	// Check if there is exactly one literal unassigned.
	var counter := 0;
	var i := 0;
	while i < |c|{
		var assigned := eval_literal(I, c[i]);
		if assigned.None?{
			counter := counter + 1;
		}
		i := i + 1;
	}
	if counter == 1{
		assert sat_c.None? || !sat_c.value; // ensures that c is not satisfied. 
		return true;
	}
	else{
		return false;
	}
}

method exist_units (I : Interpretation, phi : Formula) returns (b : bool, c : Clause)
	// requires phi != [] // or maybe write a if clause?
{
	var i := 0;
	while i < |phi|{
		var u := is_unit(I, phi[i]);
		if u{
			return true, phi[i];
		}
		assert !u;
		i := i + 1;
	}
	return false, [];
}

method propagate(I : Interpretation, c : Clause, level : nat) returns (I' : Interpretation)
{
	var b := is_unit(I, c);
	if !b{ return I; }
	var i := 0;
	var v := -1; // initial value of the unassigned variable.
	var s := True; // initial value of the truth of v.
	var d : set<Var> := {}; // initial value of the set of causes.
	I' := I;
	assert forall k : Var :: k in I ==> k in I';
	while i < |c|{
		if c[i].V? && c[i].v !in I{
			v := c[i].v;
			s := c[i].s;
			//I' := I'[v := (s, false)];
		}else{
			if c[i].V? && c[i].v in I{
				var di := I[c[i].v].2;
				d := d + di;
			}
		}
		i := i + 1;}
	I' := I'[v := (s, false, d, level)];
}

method decide(I : Interpretation, phi : Formula, level : nat) returns (I' : Interpretation, succ_level : nat)
	decreases *
{
	I' := I;
	var i := 0;
	var vars := get_fmla_vars(phi); // should be in parameters
	while i < |vars|{
		if vars[i] !in I{
			succ_level := level + 1;
			I' := I'[vars[i] := (True, true, {vars[i]}, succ_level)];
			return I', succ_level;
		}
		i := i + 1;
	}
	assert I' == I; // ensures that I is unchanged.
	return I, level;
}

method has_decision(I : Interpretation, phi : Formula) returns (b : bool)
	decreases *
{
	var i := 0;
	var vars := get_fmla_vars(phi);
	while i < |vars|{
		if vars[i] in I && I[vars[i]].1 {return true;}
		i := i + 1;
	}
	return false;
}

method sat_formula(I : Interpretation, phi : Formula) returns (b : Option<bool>, c : Clause)
	// if phi is falsified, return false with a conflicted clause.
{
	var i := 0;
	var counter := 0;
	while i < |phi|{
		var v := sat_clause(I, phi[i]);
		if v.Some? && !v.value{
			return Some(false), phi[i];
		}
		else{
			if v.None?{counter := counter + 1;}
		}
		i := i + 1;
	}
	if counter != 0{return None, [];}
	return Some(true),[];
}

method Var_set_to_seq(s : set<Var>, sv : seq<Var>) returns (s' : seq<Var>)
	decreases *
	// sv stands for the sequence of all the variables in the given formula.
{
	var i := 0;
	s' := [];
	while i < |sv|{
		if sv[i] in s{
			s' := s' + [sv[i]];
		}
		i := i + 1;
	}
	return s';
}

method cut_interpretation(I : Interpretation, level : nat, sv : seq<Var>) returns (I' : Interpretation)
	// given a decision level, jump back to that level of interpretation.
{
	var i := 0;
	I' := map[];
	while i < |sv|{
		if sv[i] in I && I[sv[i]].3 <= level{
			I' := I'[sv[i] := I[sv[i]]];
		}
		i := i + 1;
	}
	return I';
}

method get_conflict_causes(I : Interpretation, c : Clause, sv : seq<Var>) returns(s' : seq<Var>)
	decreases *
	// c is a conflict clause.
{
	var i := 0;
	var s : set<Var> := {};
	while i < |c|{
		if c[i].V? && c[i].v in I{
			s := s + I[c[i].v].2;
		}
		i := i + 1;
	}
	s' := Var_set_to_seq(s, sv);
}

method backjump(I : Interpretation, phi : Formula, c : Clause, sv : seq<Var>, s : seq<Var>, level : nat) returns (I' : Interpretation, phi' : Formula, jump_level : nat)
	// we start from the highest decision level, namely 0
	// try to find a level such that exactly one conflict cause is undefined in that level of interpretation
	// it is not hard to prove that this satisfies the backjumping rule
	// s := get_conflict_causes(I, c, sv);
	decreases *
{
	// compute the learned clause from conflict causes.
	var k := 0;
	var learned_clause : Clause := []; 
	while k < |s|{
		learned_clause := learned_clause + [V(s[k], False)];
		k := k + 1;
	}
	phi' := phi + [learned_clause];
	// decide backjump level.
	var i := 0;
	while i <= level{
		I' := cut_interpretation(I, i, sv);
		var j := 0;
		var counter := 0;
		var l : Var := -1;
		while j < |s|{
			if s[j] !in I'{counter := counter + 1;l := s[j];}
			j := j + 1;
		}
		if counter == 1{
			var cause_set := set z | z in s;
			print("Jumping to level : ");
			print(i);
			print("\n");
			cause_set := cause_set - {l};
			I' := I'[l := (False, false, cause_set, i)];
			return I', phi', i;
		}
		i := i + 1;
	}
	print("Backjumping failed.\n"); // should never happen.
}

method CDCL(phi: Formula) returns (sat : bool, I : Interpretation)
	decreases *
{
	var vars := get_fmla_vars(phi);
	var phi' := phi;
	I := map[];
	var decision_level : nat := 0; 
	while true
		decreases *
	{
		var has_units, unit := exist_units(I, phi');
		while has_units
			decreases *
		{
			I := propagate(I, unit, decision_level);
			has_units, unit := exist_units(I, phi');
		}
		I,  decision_level := decide(I, phi', decision_level);
		var sat, conflict := sat_formula(I, phi');
		if sat.Some? && !sat.value{
			var has_d := has_decision(I, phi');
			if !has_d{ // print("UNSAT");
				print("Decisions exhausted. \n");
				//print(conflict);
				//print("\n");
				//print(I);
			return false, I;}
			// backjumping
			var s := get_conflict_causes(I, conflict, vars);
			if s == []{print("Conflict causes exhausted.\n"); return false, I;}
			I, phi', decision_level := backjump(I, phi', conflict, vars, s, decision_level);
		}
		else{
			if sat.Some? && sat.value{
			return true, I;}
		}
	}
}

method DPLL(phi : Formula) returns (alpha : Option<Assignment>)
	decreases *
{
	var vars := get_fmla_vars(phi);
	var sat, I := CDCL(phi);
	var alpha' : Assignment := map[];
	if sat{
		// print(sat);
		var i := 0;
		while i < |vars|{
			if vars[i] in I{alpha' := alpha'[vars[i] := I[vars[i]].0];}			
			i := i + 1;
		}
		return Some(alpha');
	}else{
		return None;
	}
}
	
  method print_assignment(phi: Formula, alpha: Assignment)
    decreases *
  {
    var vars := get_fmla_vars(phi);
    var i := 0;

    while(i < |vars|)
      invariant i <= |vars|
    {
      if(vars[i] in alpha) {
        print "  ";
        print vars[i];
        print " => ";
        print if alpha[vars[i]] == True then "T" else "F";
        print "\n"; 
      }
      i := i + 1;
    }
  }

  method run_benchmark(phi: Formula, name: string, expected_result: Option<bool>)
    decreases *
  {
    var alpha := DPLL(phi);
    var pre := "\n[" + name + "]: ";

    if(expected_result.Some?) {      
      var expected := if expected_result.value then "sat" else "unsat";
    
      if(alpha.Some? != expected_result.value) {
        print(pre + "failed (expected " + expected + ")\n");
      } else {
        print(pre + "succeeded with " + expected + "\n");
      }      
    } else {
      print(pre + "returned " + if alpha.Some? then "sat\n" else "unsat\n");
    }

    if(alpha.Some?) {
      print("satisfying assignment:\n");
      print_assignment(phi, alpha.value);      
    }

    print("----------------------------\n");
  }

  method {:main} Main(ghost env:HostEnvironment)
    requires env != null && env.Valid() && env.ok.ok()
    decreases *
  {

    var n_args := HostConstants.NumCommandLineArgs(env);
    if(n_args < 2) { return; }

    var dimacs_path := HostConstants.GetCommandLineArg(1, env);
    var path_exists := FileStream.FileExists(dimacs_path, env);

    if(!path_exists) { return; }

    var benchmark := Dimacs.FmlaFromFile(dimacs_path);
    if(benchmark == null) { return; }

    var phi := Dimacs.convert_dimacs(benchmark);  

    run_benchmark(phi, dimacs_path[..], None);
  }

}
