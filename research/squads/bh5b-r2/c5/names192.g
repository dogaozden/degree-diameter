for i in [1..NrSmallGroups(192)] do
  G := SmallGroup(192, i);
  Print(i, " ", StructureDescription(G), "\n");
od;
QUIT;
