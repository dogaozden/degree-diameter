for n in [606..650] do
  if NrSmallGroups(n) > 0 then
    for i in [1..NrSmallGroups(n)] do
      H:=SmallGroup(n,i);;
      ab:=IsAbelian(H);;
      D:=Size(DerivedSubgroup(H));;
      ZZ:=0;;
      if n/D <= 64 then ZZ:=Size(Centre(H)); fi;;
      Print(n," ",i," ",ab," ",D," ",ZZ,"\n");
    od;
  fi;
od;
QUIT;
