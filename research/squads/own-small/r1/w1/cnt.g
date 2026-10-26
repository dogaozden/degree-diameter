for N in [401..500] do
  k := NrSmallGroups(N);
  nab := Number([1..k], id -> not IsAbelian(SmallGroup(N,id)));
  if k <= 40 and nab > 0 then Print(N, " ", k, " ", nab, "\n"); fi;
od;
QUIT;
