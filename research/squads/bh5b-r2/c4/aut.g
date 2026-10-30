LoadPackage("AutPGrp");
for o in [304,312] do
  for i in [1..NrSmallGroups(o)] do
    G := SmallGroup(o,i);
    A := AutomorphismGroup(G);
    inv := Number(Elements(G), x -> x<>One(G) and x^2=One(G));
    Print(o," ",i," ",Size(A)," ",inv," ",StructureDescription(G),"\n");
  od;
od;
QUIT;
