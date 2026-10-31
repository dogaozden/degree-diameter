# independent check: count groups with a non-central involution outside every normal index-2 subgroup (the SKIPHAAR-surviving candidates)
for n in [740, 744, 748, 752, 760, 764] do
  res := [];
  for id in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, id);
    if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
    inv := Filtered(List(ConjugacyClasses(G), Representative), t -> Order(t) = 2);
    idx2 := Filtered(NormalSubgroups(G), N -> Index(G, N) = 2);
    cnt := 0;
    for t in inv do
      H := Subgroup(G, [t]);
      if Size(Core(G, H)) = 1 and ForAll(idx2, N -> Size(Intersection(N, H)) > 1) then cnt := cnt + 1; fi;
    od;
    if cnt > 0 then Add(res, [id, cnt]); fi;
  od;
  Print("ORDER ", n, " groups_with_candidates ", res, "\n");
od;
QUIT;
