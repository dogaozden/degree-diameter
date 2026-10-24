for n in [1093..1140] do
  if SmallGroupsAvailable(n) then Print(n, ":", NumberSmallGroups(n), " "); else Print(n, ":NA "); fi;
od;
Print("\n");
QUIT;
