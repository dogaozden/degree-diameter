# expected pair counts after the same filters as ExportPairs (core-free, SKIPHAAR); no output files written
Read("dc2_lib.g");
H_ORDER := 2;
SKIPHAAR := true;
for o in [736] do
  for id in [1..NrSmallGroups(o)] do
    G := SmallGroup(o, id);
    if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
    Hs := SubsOfOrder(G, 2);
    Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
    Hs := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
    Print(o, " ", id, " classes_after_filter ", Length(Hs), " pairs ", Length(Hs)*(Length(Hs)+1)/2, "\n");
  od;
od;
QUIT;
