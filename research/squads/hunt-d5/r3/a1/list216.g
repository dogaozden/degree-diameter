for i in [1..NrSmallGroups(216)] do G:=SmallGroup(216,i);
Print(i," ",IsAbelian(G)," ",Size(G/DerivedSubgroup(G))," ",Size(DerivedSubgroup(G))," ",Size(Centre(G))," ",Size(G/Centre(G)),"\n"); od;
QUIT;
