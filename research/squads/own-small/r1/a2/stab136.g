# For each group of order N: Aut-orbit reps r1 of elements (as in gap_export_aut.g), and for each r1 the orbits of
# Stab_Aut(r1) on G (reps). Output: dir/s<N>_<id>.txt: "N R" then per r1: "r1 K2 reps..." (element index, identity 0).
for id in [1..NrSmallGroups(N)] do
  G := SmallGroup(N, id);
  el := Concatenation([One(G)], Filtered(AsSSortedList(G), x -> x <> One(G)));
  A := AutomorphismGroup(G);
  orbs := Orbits(A, el);
  reps := List(orbs, o -> Minimum(List(o, x -> Position(el, x))) - 1);
  Sort(reps);
  out := OutputTextFile(Concatenation(dir, "/s", String(N), "_", String(id), ".txt"), false);
  SetPrintFormattingStatus(out, false);
  WriteAll(out, Concatenation(String(N), " ", String(Length(reps)), "\n"));
  for r in reps do
    S := Stabilizer(A, el[r+1], OnPoints);
    so := Orbits(S, el);
    s2 := List(so, o -> Minimum(List(o, x -> Position(el, x))) - 1);
    Sort(s2);
    WriteAll(out, Concatenation(String(r), " ", String(Length(s2)), " ", JoinStringsWithSeparator(List(s2, String), " "), "\n"));
  od;
  CloseStream(out);
od;
QUIT;
