# list the IdGroup classes of index-2 subgroups E of groups G of order ORDER (G nonabelian or abelian)
Print("n=", NrSmallGroups(ORDER), "\n");
res := [];
for id in [1..NrSmallGroups(ORDER)] do
  G := SmallGroup(ORDER, id);
  for N in NormalSubgroups(G) do
    if Index(G, N) = 2 then
      Add(res, [id, IdGroup(N), IsAbelian(G)]);
    fi;
  od;
od;
Print(res, "\n");
Print("distinct E: ", Set(List(res, x -> x[2])), "\n");
QUIT;
