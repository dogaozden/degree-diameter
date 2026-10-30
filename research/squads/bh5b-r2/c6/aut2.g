for o in [544,560] do
  n := NrSmallGroups(o);
  Print("order ", o, " groups ", n, "\n");
  for i in [1..n] do
    G := SmallGroup(o, i);
    A := AutomorphismGroup(G);
    Print(o, " ", i, " ", StructureDescription(G), " aut=", Size(A), "\n");
  od;
od;
QUIT;
