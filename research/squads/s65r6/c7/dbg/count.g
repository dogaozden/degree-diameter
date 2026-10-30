Read("dc2_lib.g");
for o in [742,746,748,754,758] do
for id in [1..NrSmallGroups(o)] do
  G := SmallGroup(o, id);
  Hs := SubsOfOrder(G, 2);
  Hs2 := Filtered(Hs, H -> Size(Core(G, H)) = 1);
  Hs3 := Filtered(Hs2, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
  Print(o, " ", id, " invclasses=", Length(Hs), " corefree=", Length(Hs2), " nonHaar=", Length(Hs3), "\n");
od; od;
QUIT;
