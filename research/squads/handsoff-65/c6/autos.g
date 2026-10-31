# usage: gap -q -c 'ORDER:=343; IDS:=[4];' autos.g   -> phi/aut_<ORDER>_<i>.txt : one line per automorphism (images of el, el[0]=id)
if not IsBound(IDS) then IDS := [1..NrSmallGroups(ORDER)]; fi;
for i in IDS do
  G := SmallGroup(ORDER, i);
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  A := AutomorphismGroup(G);
  NMAX := 300;
  auts := Set(List([1..3000], i -> Random(A)));
  auts := auts{[1..Minimum(NMAX, Length(auts))]};
  fn := Concatenation("phi/aut_", String(ORDER), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(Length(auts)), "\n");
  for alpha in auts do
    AppendTo(out, JoinStringsWithSeparator(List(el, g -> String(Position(el, Image(alpha, g)) - 1)), " "), "\n");
  od;
  CloseStream(out);
  PrintTo(Concatenation("phi/aut_", String(ORDER), "_", String(i), ".info"), StructureDescription(G), " |Aut|=", Size(A), " sample=", Length(auts), "\n");
od;
QUIT;
