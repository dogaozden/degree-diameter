# list groups of order 1802..1999 with 3 | n, few involutions; print id, #invol, #order3
for n in [1802..1999] do
  if n mod 3 = 0 and n mod 8 <> 0 then
    k := NrSmallGroups(n);
    if k <= 130 then
      for i in [1..k] do
        G := SmallGroup(n, i);
        inv := Number(Elements(G), x -> Order(x) = 2);
        if inv <= 6 then
          Print(n, " ", i, " ", inv, " ", Number(Elements(G), x -> Order(x) = 3), " ", IdGroup(G)[2] = i, "\n");
        fi;
      od;
    fi;
  fi;
od;
QUIT;
