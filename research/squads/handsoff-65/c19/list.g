for n in [401..420] do
  k := NrSmallGroups(n);
  na := 0; ids := [];
  for i in [1..k] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then Add(ids, i); na := na + 1; fi;
  od;
  Print(n, " groups=", k, " nonabelian=", na, " ", ids, "\n");
od;
QUIT;
