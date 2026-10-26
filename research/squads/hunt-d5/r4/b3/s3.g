for i in [1000,5000,10000,15000,20000,21541] do t:=Runtime();; H:=SmallGroup(640,i);; a:=Runtime()-t;; D:=Size(DerivedSubgroup(H));; b:=Runtime()-t; ZZ:=Size(Centre(H));; c:=Runtime()-t; Print(i," construct ",a," der ",b," cen ",c," G' ",D," Z ",ZZ,"\n"); od;
QUIT;
