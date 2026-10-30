for i in [1..NrSmallGroups(192)] do
  G := SmallGroup(192, i);
  Print(i, " ", Size(AutomorphismGroup(G)), " ", Size(Centre(G)), " ", Length(ConjugacyClasses(G)), " ", StructureDescription(G), "\n");
od;
QUIT;
