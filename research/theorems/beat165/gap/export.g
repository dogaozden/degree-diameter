# Write the edge list of Cos(G; H, K) (sides G/H then G/K; edges = G-orbit of the pair (H, K)) in apsp.c format:
# first line n, then "a b" with 0 <= a < nA <= b < nA+nB.
ExportCosetGraph := function(G, H, K, file)
  local actH, actK, nA, nB, gens, comb, pair, orb, e, out;
  actH := FactorCosetAction(G, H); actK := FactorCosetAction(G, K);
  nA := Index(G, H); nB := Index(G, K);
  gens := GeneratorsOfGroup(G);
  # combined permutations on [1..nA] u [nA+1..nA+nB]
  comb := List(gens, g -> PermList(Concatenation(OnTuples([1..nA], Image(actH, g)),
                                                 OnTuples([1..nB], Image(actK, g)) + nA)));
  pair := [1, nA + 1];   # the coset H and the coset K share the edge L = H n K
  orb := Orbit(Group(comb), pair, OnTuples);
  out := OutputTextFile(file, false); SetPrintFormattingStatus(out, false);
  PrintTo(out, nA + nB, "\n");
  for e in orb do AppendTo(out, e[1]-1, " ", e[2]-1, "\n"); od;
  CloseStream(out);
  return [nA, nB, Length(orb)];
end;
