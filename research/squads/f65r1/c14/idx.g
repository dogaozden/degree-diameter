for n in [343,344,348,350,351,354,355,356,357,358,360,345] do
  Print(n, " ", Filtered([1..NrSmallGroups(n)], i -> not IsAbelian(SmallGroup(n,i))), "\n");
od;
QUIT;
