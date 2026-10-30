# stage 2: for candidate (ORD, id) pairs in cands.txt, count the H-classes that pass the bi-coset filters
# (core-free, not Haar-type via SKIPHAAR) for |H| = 2: prints ORD id ninv nInvClasses ncases
SKIPHAAR := true;
Read("dc2_lib.g");
lines := List(SplitString(StringFile("cands.txt"), "\n"), l -> List(SplitString(l, " "), Int));
for p in lines do
  if Length(p) < 3 then continue; fi;
  G := SmallGroup(p[1], p[2]);

  Hs := SubsOfOrder(G, 2);
  ninvcl := Length(Hs);
  Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
  Hs := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> 2 or Size(Intersection(N, H)) > 1));
  Print(p[1], " ", p[2], " ", p[3], " ", ninvcl, " ", Length(Hs), "\n");
od;
QUIT;
