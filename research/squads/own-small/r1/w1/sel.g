for N in [401..500] do
  k := NrSmallGroups(N);
  if k <= 40 then
    for id in [1..k] do
      G := SmallGroup(N,id);
      if not IsAbelian(G) then
        ab := AbelianInvariants(G);
        if IsEvenInt(Product(ab)) then
          Print(N, " ", id, " ", ab, "\n");
        fi;
      fi;
    od;
  fi;
od;
QUIT;
