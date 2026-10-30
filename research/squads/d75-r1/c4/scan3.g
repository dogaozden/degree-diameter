Print("N1296 ", NrSmallGroups(1296), " N1296 ", NrSmallGroups(1296), "\n");
for i in [1..NrSmallGroups(1296)] do
  G := SmallGroup(1296, i);
  if IsAbelian(G) then continue; fi;
  ninv := Number(AsList(G), x -> x <> One(G) and x^2 = One(G));
  Print(1296, " ", i, " ", ninv, "\n");
od;
QUIT;
