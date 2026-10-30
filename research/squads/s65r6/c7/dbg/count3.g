Read("dc2_lib.g");
SKIPHAAR := true;
tot := 0;
for o in [742,744,746,748,750,752,754,756,758,760] do
  ot := 0; og := 0;
  for id in [1..NrSmallGroups(o)] do
    G := SmallGroup(o, id);
    Hs := Filtered(SubsOfOrder(G, 2), H -> Size(Core(G, H)) = 1);
    NI := Filtered(NormalSubgroups(G), N -> Index(G, N) = 2);
    n := Length(Hs); c := 0;
    for i in [1..n] do for j in [i..n] do
      if not ForAny(NI, N -> Size(Intersection(N, Hs[i])) = 1 and Size(Intersection(N, Hs[j])) = 1) then c := c + 1; fi;
    od; od;
    if c > 0 then og := og + 1; Print(o, " ", id, " pairs=", c, "\n"); fi;
    ot := ot + c;
  od;
  Print("ORDER ", o, " pairs=", ot, " groups_with_pairs=", og, "\n");
  tot := tot + ot;
od;
Print("TOTAL pairs=", tot, "\n");
QUIT;
