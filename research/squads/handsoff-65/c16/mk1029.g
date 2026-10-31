# Groups of order 3*343 = 1029 (no SmallGroups library): G = P x| C3, P = SmallGroup(343,i) (Sylow 7 is normal).
# For each P and a sample of automorphisms of order 3 (up to conjugacy in Aut(P)) build G and export the bi-coset
# pairs for subgroups of order 3 (dc2_lib.g ExportPairs). Files: OUTDIR/g1029_<i>_<k>_<a>_<b>.dc2
Read("dc2_lib.g");
Q := CyclicGroup(IsPermGroup, 3);
reps := [];   # list of [i, phi]
for i in [1..5] do
  P := SmallGroup(343, i);
  A := AutomorphismGroup(P);
  autos := [];
  # identity (direct product) plus random order-3 automorphisms, deduplicated by conjugacy in Aut(P)
  Add(autos, IdentityMapping(P));
  for t in [1..60] do
    x := Random(A); o := Order(x);
    if o mod 3 = 0 then
      y := x^(o/3);
      if ForAll(autos, a -> not IsConjugate(A, a, y)) then Add(autos, y); fi;
    fi;
  od;
  Print("P", i, " ", StructureDescription(P), " classes of order-3 auts: ", Length(autos), "\n");
  for k in [1..Length(autos)] do
    phi := autos[k];
    if k = 1 then
      hom := GroupHomomorphismByImages(Q, A, [Q.1], [One(A)]);
    else
      hom := GroupHomomorphismByImages(Q, A, [Q.1], [phi]);
    fi;
    if hom = fail then Print("no hom ", i, " ", k, "\n"); continue; fi;
    G := SemidirectProduct(Q, hom, P);
    G := Image(IsomorphismPermGroup(G));
    Print("  G order ", Size(G), " k=", k, "\n");
    ExportPairs(G, 3, Concatenation("x1029/g1029_", String(i), "_", String(k)));
  od;
od;
QUIT;
