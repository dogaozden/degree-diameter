# list non-solvable, non-almost-simple SmallGroups of order ORDER
res := [];
for i in [1..NrSmallGroups(ORDER)] do
  G := SmallGroup(ORDER, i);
  if not IsSolvable(G) then
    S := Socle(G);
    almost := IsSimple(S) and Size(Centralizer(G, S)) = 1;
    # almost simple means: socle simple and G/socle... use: socle simple and C_G(socle)=1
    Add(res, [i, almost, StructureDescription(G)]);
  fi;
od;
Print(Filtered(res, r -> not r[2]), "\n");
QUIT;
