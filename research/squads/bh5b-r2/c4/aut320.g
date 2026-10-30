LoadPackage("AutPGrp");
for i in [1..NrSmallGroups(320)] do
  G := SmallGroup(320,i);
  A := AutomorphismGroup(G);
  inv := Number(Elements(G), x -> x<>One(G) and x^2=One(G));
  Print(320," ",i," ",Size(A)," ",inv," ",StructureDescription(G),"\n");
od;
QUIT;
