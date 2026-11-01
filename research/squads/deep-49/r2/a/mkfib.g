Read("/home/user/degree-diameter/research/squads/deep-49/r2/a/export_r2a.g");
dir := "/home/user/degree-diameter/research/squads/deep-49/r2/a/g/";
S5 := SymmetricGroup(5);
A5 := AlternatingGroup(5);
MakeFib := function(name, X)
  local P, e1, e2, K, x1, gens, H, subs;
  X := Image(IsomorphismPermGroup(X));
  P := DirectProduct(S5, X);
  e1 := Embedding(P, 1); e2 := Embedding(P, 2);
  subs := Filtered(NormalSubgroups(X), N -> Index(X, N) = 2);
  Print(name, " X order ", Size(X), " index-2 subgroups ", Length(subs), " X ", StructureDescription(X), "\n");
  K := subs[1];
  x1 := First(Elements(X), x -> not x in K);
  gens := Concatenation(List(GeneratorsOfGroup(A5), a -> Image(e1, a)),
                        List(GeneratorsOfGroup(K), k -> Image(e2, k)),
                        [Image(e1, (1,2)) * Image(e2, x1)]);
  H := Subgroup(P, gens);
  Print(name, " size ", Size(H), " ab ", AbelianInvariants(H), " classes ", NrConjugacyClasses(H), "\n");
  return H;
end;
G1 := MakeFib("S5fD21", DihedralGroup(42));
ExportGroup(G1, Concatenation(dir, "S5fD21.exp"));
G2 := MakeFib("S5fF42", SmallGroup(42,1));
ExportGroup(G2, Concatenation(dir, "S5fF42.exp"));
G3 := MakeFib("S5fC3D7", DirectProduct(CyclicGroup(3), DihedralGroup(14)));
ExportGroup(G3, Concatenation(dir, "S5fC3D7.exp"));
G4 := MakeFib("S5fC7S3", DirectProduct(CyclicGroup(7), SymmetricGroup(3)));
ExportGroup(G4, Concatenation(dir, "S5fC7S3.exp"));
Print("S5xF21 invariants ", AbelianInvariants(DirectProduct(S5, SmallGroup(21,1))), " classes ", NrConjugacyClasses(DirectProduct(S5, SmallGroup(21,1))), "\n");
Print("SmallGroup(42,1) ", StructureDescription(SmallGroup(42,1)), "\n");
G5 := DirectProduct(A5, Image(IsomorphismPermGroup(DirectProduct(CyclicGroup(7), SymmetricGroup(3)))));
Print("A5xC7S3 size ", Size(G5), " classes ", NrConjugacyClasses(G5), "\n");
ExportGroup(G5, Concatenation(dir, "A5xC7S3.exp"));
QUIT;
