SKIPHAAR := true;
Read("dc2_lib.g");
lines := List(SplitString(StringFile("valid.txt"), "\n"), l -> List(SplitString(l, " "), Int));
for p in lines do
  if Length(p) < 2 then continue; fi;
  G := SmallGroup(p[1], p[2]);
  if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
  Hs := SubsOfOrder(G, 2);
  Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
  Hs := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
  for H in Hs do
    Print(p[1], " ", p[2], " NH ", Size(Normalizer(G, H)), " ndc ", Length(DoubleCosets(G, H, H)), "\n");
  od;
od;
QUIT;
