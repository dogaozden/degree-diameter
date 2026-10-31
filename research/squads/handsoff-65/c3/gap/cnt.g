LoadPackage("smallgrp");
L := [];
for m in [1372..1600] do
  if IsInt(m) then Add(L, [m, NumberSmallGroups(m)]); fi;
od;
Print(Filtered(L, x -> x[2] > 0 and x[2] <= 300), "\n");
Print("total ", Sum(L, x -> x[2]), "\n");
QUIT;
