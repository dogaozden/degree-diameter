SemiList := function(H, N)
  local A, Ael, nat, Hab, hg, cands, res, tup, psi, phi, G, combos;
  A := AutomorphismGroup(N);
  Ael := Elements(A);
  nat := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
  Hab := Image(nat);
  hg := MinimalGeneratingSet(Hab);
  cands := List(hg, h -> Filtered(Ael, x -> x^Order(h) = One(A)));
  res := [];
  combos := Cartesian(cands);
  for tup in combos do
    psi := GroupHomomorphismByImages(Hab, A, hg, tup);
    if psi <> fail then
      phi := nat * psi;
      G := SemidirectProduct(H, phi, N);
      Add(res, G);
    fi;
  od;
  return res;
end;
N := CyclicGroup(IsPermGroup, 311);
H := SmallGroup(8,4);
L := SemiList(H, N);
Print("count ", Length(L), "\n");
for G in L do
  Print(Size(G), " ", AbelianInvariants(G), " ", StructureDescription(G), " gens ", Length(MinimalGeneratingSet(G)), " metac ", ForAny(NormalSubgroups(G), M -> IsCyclic(M) and IsCyclic(FactorGroup(G,M))), "\n");
od;
QUIT;
