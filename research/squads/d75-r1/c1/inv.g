# inv.g: for SmallGroup(640,i), i in [LO..HI]: id, number of involutions, abelian flag
for i in [LO..HI] do
  G := SmallGroup(640, i);
  ab := IsAbelian(G);
  ninv := Number(AsList(G), x -> x <> One(G) and x^2 = One(G));
  Print(640, " ", i, " ", ninv, " ", ab, "\n");
od;
QUIT;
