Read("cosetcheck.g");
G := PSL(5,3);   # natural action on 121 points of PG(4,3)
V := GF(3)^5;
# Build subspace stabilizers via the matrix group, then map to the permutation group.
M := SL(5,3);
e := BasisVectors(Basis(V));
stab := function(gens)  # stabilizer in M of the subspace spanned by gens
  return Stabilizer(M, Subspace(V, gens), function(U, g) return Subspace(V, List(BasisVectors(Basis(U)), v -> v*g)); end);
end;
# flags: W1 = <e1>, W2 = <e1,e2>, W3 = <e1,e2,e3>, W4 = <e1..e4>, rows act on the right
S1 := stab([e[1]]); S2 := stab(e{[1,2]}); S3 := stab(e{[1..3]}); S4 := stab(e{[1..4]});
HA := Intersection(S1, S3); HB := Intersection(S2, S4);
Print("orders ", Size(HA), " ", Size(HB), " ", Size(Intersection(HA,HB)), "\n");
r := CosetGraphReport(M, HA, HB);
Print(r, "\n");
QUIT;
