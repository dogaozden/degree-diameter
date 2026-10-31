# c1 filter: SmallGroups of order 1561-1640 (not 1568,1584,1600), largest prime p >= 19 with p || N,
# normal Sylow p of order p, d = |G : C_G(P)| >= 3, center <= 6, involutions <= 15.
for N in [1561..1640] do
  if N in [1568,1584,1600] then continue; fi;
  if IsPrime(N) then continue; fi;
  p := Maximum(PrimeDivisors(N));
  if p < 19 or N mod (p*p) = 0 then continue; fi;
  for ID in [1..NumberSmallGroups(N)] do
    G := SmallGroup(N, ID);;
    P := SylowSubgroup(G, p);;
    if not IsNormal(G, P) then continue; fi;
    d := Index(G, Centralizer(G, P));;
    if d < 3 then continue; fi;
    z := Size(Centre(G));;
    if z > 6 then continue; fi;
    inv := Number(Elements(G), x -> Order(x) = 2);;
    if inv > 15 then continue; fi;
    Print(N, " ", ID, " ", p, " ", d, " ", z, " ", inv, " ", StructureDescription(G : short), "\n");
  od;
od;
QUIT;
