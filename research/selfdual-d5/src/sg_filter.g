# sg_filter.g: for each "N ID ..." line of the file LIST: largest prime p of N, whether the Sylow p-subgroup P is normal
# and of order p, the order d of the action of G on P (|G : C_G(P)|), the center size and the number of involutions.
# Output "N ID p normal d center inv".
ls := List(SplitString(StringFile(LIST), "\n"), l -> SplitString(l, " "));;
for l in ls do
  if Length(l) < 2 then continue; fi;
  N := Int(l[1]); ID := Int(l[2]); G := SmallGroup(N, ID);
  p := Maximum(PrimeDivisors(N)); P := SylowSubgroup(G, p);
  nor := IsNormal(G, P) and Size(P) = p;
  d := 0; if nor then d := Index(G, Centralizer(G, P)); fi;
  Print(N, " ", ID, " ", p, " ", nor, " ", d, " ", Size(Centre(G)), " ", Number(Elements(G), x -> Order(x) = 2), "\n");
od;
QUIT;
