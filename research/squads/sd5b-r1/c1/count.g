tot := 0;;
for N in [1561..1640] do
  if N in [1568,1584,1600] then continue; fi;
  if IsPrime(N) then continue; fi;
  k := NumberSmallGroups(N);;
  tot := tot + k;;
  Print(N, " ", k, " ", Collected(Factors(N)), "\n");
od;
Print("TOTAL ", tot, "\n");
QUIT;
