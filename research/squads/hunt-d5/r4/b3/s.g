t:=Runtime();;
for i in [1..300] do H:=SmallGroup(640,i*70);; D:=Size(DerivedSubgroup(H));; Z:=Size(Centre(H));; od;
Print("300 groups ms ", Runtime()-t, "\n");
QUIT;
