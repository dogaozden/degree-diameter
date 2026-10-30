for i in [473, 475, 476] do
  G := SmallGroup(1200, i);
  Print("1200/", i, " index-2 normal subgroups: ", Length(Filtered(NormalSubgroups(G), N -> Index(G, N) = 2)), "\n");
od;
QUIT;
