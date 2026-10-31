tot := 0;
for n in [401..420] do
  k := NrSmallGroups(n);
  na := Number([1..k], i -> not IsAbelian(SmallGroup(n, i)));
  tot := tot + na;
  Print(n, ":", k, "/", na, " ");
od;
Print("\nTOTAL nonabelian=", tot, "\n");
QUIT;
