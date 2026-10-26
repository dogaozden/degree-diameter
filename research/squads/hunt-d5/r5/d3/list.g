for n in [369..400] do
for i in [1..NrSmallGroups(n)] do G:=SmallGroup(n,i);
if not IsAbelian(G) then Print(n," ",i," ",Size(G/DerivedSubgroup(G))," ",Size(Centre(G)),"\n"); fi; od; od;
