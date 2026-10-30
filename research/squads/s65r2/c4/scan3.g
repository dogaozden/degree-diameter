# for each order and group id: number of H classes of order 3 with trivial core and no normal complement of index 3
Read("dc2_lib.g");
for ord in [1035,1038,1041,1047,1050,1053,1059,1062,1065,1068,1071,1074,1077] do
  res := [];
  for id in [1..NrSmallGroups(ord)] do
    G := SmallGroup(ord, id);
    if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
    Hs := SubsOfOrder(G, 3);
    Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
    Hs := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 3 or Size(Intersection(N, H)) > 1));
    if Length(Hs) > 0 then Add(res, id); fi;
  od;
  Print("ORDER ", ord, " valid-H groups: ", res, "\n");
od;
QUIT;
