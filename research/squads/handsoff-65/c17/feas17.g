# list groups of orders ORDERS with an element x of order 3 whose subgroup <x> is NOT normal (needed for full double cosets)
for n in ORDERS do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    if n mod 3 = 0 then
      x3 := Filtered(AsList(G), g -> Order(g) = 3);
      ok := false;
      for x in x3 do
        if not IsNormal(G, Subgroup(G, [x])) then ok := true; break; fi;
      od;
      if ok then Print(n, " ", i, " ", StructureDescription(G), "\n"); fi;
    fi;
  od;
od;
QUIT;
