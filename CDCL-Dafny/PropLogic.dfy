module PropLogic
{
  datatype Option<T> = Some(value:T) | None

  datatype Bool = True | False
  datatype Literal = V(v: Var, s: Bool) | C(b: Bool)

  type Var = int
  type Clause = seq<Literal>
  type Formula = seq<Clause>
  type Assignment = map<Var, Bool>
	type Interpretation = map<Var, (Bool, bool, set<Var>, nat)> //variable -> (value, is decided?, set of cause decisions, decision levels)
}
