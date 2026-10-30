Read("dc2_lib.g");
SKIPHAAR := true;
tot := 0;
for o in [744,750,752,756,760] do
  ot := 0;
  for id in [1..NrSmallGroups(o)] do
    G := SmallGroup(o, id);
    Hs := SubsOfOrder(G, 2);
    Hs2 := Filtered(Hs, H -> Size(Core(G, H)) = 1);
    Hs3 := Filtered(Hs2, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
    m := Length(Hs3);
    if m > 0 then ot := ot + m*(m+1)/2; Print(o, " ", id, " nonHaarH=", m, "\n"); fi;
  od;
  Print("ORDER ", o, " pairs=", ot, "\n");
  tot := tot + ot;
od;
Print("TOTAL pairs=", tot, "\n");
QUIT;
