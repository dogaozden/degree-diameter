Read("export.g");
M := SL(5,3); V := GF(3)^5; e := BasisVectors(Basis(V));
stab := function(gens)
  return Stabilizer(M, Subspace(V, gens), function(U, g) return Subspace(V, List(BasisVectors(Basis(U)), v -> v*g)); end);
end;
S1 := stab([e[1]]); S2 := stab(e{[1,2]}); S3 := stab(e{[1..3]}); S4 := stab(e{[1..4]});
iso := IsomorphismPermGroup(M); G := Image(iso);
H := Image(iso, Intersection(S1, S3)); K := Image(iso, Intersection(S2, S4));
Print(ExportCosetGraph(G, H, K, "flag_test.edges"), "\n");
QUIT;
