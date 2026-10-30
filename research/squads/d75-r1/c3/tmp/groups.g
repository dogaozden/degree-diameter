Print(NumberSmallGroups(301), " ", NumberSmallGroups(305), " ", NumberSmallGroups(304), " ", NumberSmallGroups(312), " ", NumberSmallGroups(327), "\n");
for id in [1,2] do Print("301,",id," ",IsAbelian(SmallGroup(301,id))," ", StructureDescription(SmallGroup(301,id)),"\n"); od;
for id in [1,2] do Print("305,",id," ",IsAbelian(SmallGroup(305,id))," ", StructureDescription(SmallGroup(305,id)),"\n"); od;
Print("327: ", List([1..NumberSmallGroups(327)], i->StructureDescription(SmallGroup(327,i))), "\n");
QUIT;
