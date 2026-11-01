# count admissible G-sets (same enumeration as src/gsets.g dosets) without writing them
LoadPackage("smallgrp");
stabok := function(H) return ForAll(Set(Factors(Size(H))), p -> p <= 3); end;
countsets := function(G, N)
  local Ks, K, cls, adm, sizes, half, combos, cc, c, rec2, i, j, tot, nper, kk, cnt;
  half := N / 2; Ks := [G];
  Append(Ks, Filtered(List(NormalSubgroups(G)), S -> Index(G, S) = 2));
  res := [];
  for kk in [1..Length(Ks)] do
    K := Ks[kk];
    cls := List(ConjugacyClassesSubgroups(G), Representative);
    adm := Filtered(cls, H -> stabok(H) and IsSubgroup(K, H));
    if K = G then
      sizes := List(adm, H -> Index(G, H));
      combos := RestrictedPartitions(half, Set(sizes));
      cc := 0;
      for c in combos do
        rec2 := 1;
        for i in Set(c) do
          j := Number(c, x -> x = i);
          rec2 := rec2 * Binomial(Number(sizes, x -> x = i) + j - 1, j);
        od;
        cc := cc + rec2;
      od;
      Add(res, [kk, "pres", Length(adm), cc, cc*cc]);
    else
      sizes := List(adm, H -> Index(G, H));
      combos := RestrictedPartitions(N, Set(sizes));
      cnt := 0;
      for c in combos do
        rec2 := 1;
        for i in Set(c) do
          j := Number(c, x -> x = i);
          rec2 := rec2 * Binomial(Number(sizes, x -> x = i) + j - 1, j);
        od;
        cnt := cnt + rec2;
      od;
      Add(res, [kk, "rev", Length(adm), cnt]);
    fi;
  od;
  return res;
end;
for pr in [[12,3],[18,3],[18,4],[24,3],[24,12],[24,13],[36,11],[36,9],[48,48]] do
  G := SmallGroup(pr[1], pr[2]);
  Print(pr, " ", StructureDescription(G), " ", countsets(G, 170), "\n");
od;
QUIT;
