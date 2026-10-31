for n in [115..127] do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then
      Print(n, " ", i, " ", StructureDescription(G), " ord2=", Number(Elements(G), x -> x<>One(G) and x^2=One(G)), "\n");
    fi;
  od;
od;
QUIT;
