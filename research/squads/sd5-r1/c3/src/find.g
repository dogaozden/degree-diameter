for n in [360,420] do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n,i);
    if not IsSolvable(G) then Print(n," ",i," ",StructureDescription(G)," inv ", Number(AsList(G), x->Order(x)=2), "\n"); fi;
  od;
od;
Print(StructureDescription(SmallGroup(336,114)), " ", Number(AsList(SmallGroup(336,114)), x->Order(x)=2), "\n");
for i in [1..NrSmallGroups(360)] do
  G:=SmallGroup(360,i); if IsSolvable(G) = false or (not IsSolvable(G)) then continue; fi;
  if Size(Centre(G))=3 and not IsSolvable(DerivedSubgroup(G)) then Print("360 ",i," ",StructureDescription(G),"\n"); fi;
od;
QUIT;
