for i in [1..NrSmallGroups(224)] do G:=SmallGroup(224,i);
if not IsAbelian(G) then Print(i," ",Size(DerivedSubgroup(G)),"\n"); fi; od;
