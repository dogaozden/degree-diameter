# list non-abelian SmallGroups of order 657..700 (N ID), one per line
for N in [657..700] do
  for i in [1..NumberSmallGroups(N)] do
    G := SmallGroup(N, i);
    if not IsAbelian(G) then Print(N, " ", i, "\n"); fi;
  od;
od;
QUIT;
