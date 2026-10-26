# Round 3: Aut(G)-orbit representatives of every group of orders 25..36, lines "R n i count codes..." (codes as in groups/g<n>.txt).
Dir := "/home/user/degree-diameter/research/raise-d3D8-r3/groups/";
for n in [25..36] do
  f := Concatenation(Dir, "reps_", String(n), ".txt");
  PrintTo(f, "");
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    els := Concatenation([One(G)], Filtered(AsSortedList(G), x -> x <> One(G)));
    A := AutomorphismGroup(G);
    orbs := Orbits(A, els, function(x, phi) return Image(phi, x); end);
    codes := List(orbs, o -> Position(els, o[1]) - 1);
    AppendTo(f, "R ", String(n), " ", String(i), " ", String(Length(codes)));
    for c in codes do AppendTo(f, " ", String(c)); od;
    AppendTo(f, "\n");
  od;
  Print("reps order ", n, " done\n");
od;
QUIT;
