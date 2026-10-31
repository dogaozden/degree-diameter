# enumerate non-solvable groups of orders 1519..1700 in the SmallGroups library
for N in [1519..1700] do
  if N mod 60 <> 0 and N mod 168 <> 0 then continue; fi;
  for ID in [1..NrSmallGroups(N)] do
    G := SmallGroup(N, ID);
    if not IsSolvableGroup(G) then
      Print(N, " ", ID, " ", StructureDescription(G), " center ", Size(Centre(G)), " inv ", Number(Elements(G), x -> Order(x) = 2), "\n");
    fi;
  od;
od;
QUIT;
