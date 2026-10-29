for n in [290..300] do Print(n, " ", NrSmallGroups(n), "\n"); od;
for n in [290..300] do for i in [1..NrSmallGroups(n)] do G:=SmallGroup(n,i); Print(n," ",i," ",StructureDescription(G)," ab=",IsAbelian(G),"\n"); od; od;
QUIT;
