for i in [1..NrSmallGroups(176)] do
  G := SmallGroup(176, i);
  Print(i, " ", Size(AutomorphismGroup(G)), " ", StructureDescription(G), "\n");
od;
QUIT;
