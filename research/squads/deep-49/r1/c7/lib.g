# c7 library: N = C_m (normal, cyclic) semidirect H, H = SmallGroups(|H|, i)
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
      Add(res, SemidirectProduct(H, phi, N));
    fi;
  od;
  return res;
end;

IsMetac := function(G)
  return ForAny(NormalSubgroups(G), M -> IsCyclic(M) and IsCyclic(FactorGroup(G, M)));
end;

GabOrder := function(G)
  return Product(AbelianInvariants(G));
end;

DedupeG := function(L)
  local reps, keys, G, key, found, i;
  reps := []; keys := [];
  for G in L do
    key := [AbelianInvariants(G), Size(Centre(G)), NrConjugacyClasses(G),
            Collected(List(AsList(G), Order))];
    found := false;
    for i in [1..Length(reps)] do
      if keys[i] = key and IsomorphismGroups(G, reps[i]) <> fail then
        found := true; break;
      fi;
    od;
    if not found then Add(reps, G); Add(keys, key); fi;
  od;
  return reps;
end;

# builds the list for order n = m * |H|, prime m, H from SmallGroups(|H|)
# writes one line per kept group to the output stream, exports to EXPDIR
MakeOrder := function(m, hsz, prefix)
  local i, H, L, keep, G, cnt, d, out, fn, reps, ab, Hi;
  keep := [];
  for i in [1..NrSmallGroups(hsz)] do
    H := SmallGroup(hsz, i);
    L := SemiList(H, CyclicGroup(IsPermGroup, m));
    for G in L do
      if GabOrder(G) <= 309 then
        Add(keep, [i, G]);
      fi;
    od;
  od;
  Print("candidates after |G/G'|: ", Length(keep), "\n");
  return keep;
end;
