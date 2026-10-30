L := [];
for o in [1731,1734..1845] do
  if o mod 3 = 0 then Add(L, [o, NrSmallGroups(o)]); fi;
od;
Print(L, "\n");
QUIT;
