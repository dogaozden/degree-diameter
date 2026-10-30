for o in [516,520,528,540,544,560] do
  n := NrSmallGroups(o);
  Print("order ", o, " groups ", n, "\n");
  for i in [1..n] do
    G := SmallGroup(o, i);
    A := AutomorphismGroup(G);
    Print(o, " ", i, " ", StructureDescription(G), " aut=", Size(A), " 2part=", 2^Length(Factors(Size(G)))>0 , "\n");
  od;
od;
QUIT;
