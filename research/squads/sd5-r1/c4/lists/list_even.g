# even orders LO..HI: id, number of involution classes, number of non-central involution classes, non-abelian flag
for n in [LO..HI] do
  if n mod 2 <> 0 then continue; fi;
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    cl := Filtered(ConjugacyClasses(G), c -> Order(Representative(c)) = 2);
    nc := Number(cl, c -> Size(c) > 1);
    if nc >= 1 then
      Print(n, " ", i, " ", Length(cl), " ", nc, " ", IsAbelian(G), "\n");
    fi;
  od;
od;
QUIT;
