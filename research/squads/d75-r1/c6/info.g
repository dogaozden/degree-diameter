for o in [603,605,609,624,651,657] do
  for i in [1..NrSmallGroups(o)] do
    G := SmallGroup(o,i);
    Print(o," ",i," abelian=",IsAbelian(G)," ninv=",Number(AsList(G),x->Order(x)=2)," aut=",Size(AutomorphismGroup(G)),"  ", StructureDescription(G), "\n");
  od;
od;
QUIT;
