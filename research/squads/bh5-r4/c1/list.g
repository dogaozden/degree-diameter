for n in [1176,1200] do
  Print("order ", n, " groups ", NrSmallGroups(n), "\n");
  Print("nonsolvable: ", Filtered([1..NrSmallGroups(n)], i -> not IsSolvable(SmallGroup(n, i))), "\n");
od;
for n in [1160,1164,1168,1180,1188,1196] do
  Print("order ", n, " groups ", NrSmallGroups(n), "\n");
od;
QUIT;
