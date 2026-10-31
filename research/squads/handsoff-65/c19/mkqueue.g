out := OutputTextFile("queue_raw.txt", false);
for n in [401..420] do
  k := NrSmallGroups(n);
  for i in [1..k] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then
      inv := Number(Elements(G), x -> Order(x) = 2);
      AppendTo(out, n, " ", i, " ", inv, "\n");
    fi;
  od;
od;
CloseStream(out);
QUIT;
