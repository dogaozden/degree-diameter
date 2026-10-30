# stage 1: involution counts of every non-abelian group of the orders (fast); prints ORD id ninv
for ORD in [1216,1224,1232,1248,1260,1280,1296,1312] do
  for i in [1..NrSmallGroups(ORD)] do
    G := SmallGroup(ORD, i);
    if IsAbelian(G) then continue; fi;
    ninv := Number(AsList(G), x -> x <> One(G) and x^2 = One(G));
    Print(ORD, " ", i, " ", ninv, "\n");
  od;
od;
QUIT;
