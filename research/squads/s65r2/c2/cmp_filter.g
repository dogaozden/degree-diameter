Read("dc2_lib.g");
bad := 0; tot := 0;
for id in [1..NrSmallGroups(96)] do
  G := SmallGroup(96, id);
  if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
  Hs := SubsOfOrder(G, 2);
  Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
  old := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
  M := Subgroup(G, Concatenation(GeneratorsOfGroup(DerivedSubgroup(G)), List(Elements(G), g -> g^2)));
  new := Filtered(Hs, H -> IsSubset(M, H));
  tot := tot + 1;
  if Length(old) <> Length(new) then bad := bad + 1; Print("DIFF ", id, " ", Length(old), " ", Length(new), "\n"); fi;
od;
Print("checked ", tot, " groups, mismatches ", bad, "\n");
QUIT;
