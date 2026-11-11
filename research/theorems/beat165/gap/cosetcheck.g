# Diameter test for the bipartite coset graph Cos(G; H, K): sides G/H and G/K, gH ~ gK (edges = G/(H n K)).
# A-side ball of radius 4 around H is {gH : g in HKHKH}; diameter <= 5 iff HKHKH = G = KHKHK.
# We compute in the permutation actions on G/H and G/K, using the partitions into K-orbits and H-orbits.
BallSteps := function(G, H, K)
  # returns the list of ball sizes at radius 0,2,4 on side G/H (as numbers of cosets)
  local act, n, img, orbH, orbK, idH, idK, S, i, step;
  act := FactorCosetAction(G, H);
  n := Index(G, H);
  orbK := Orbits(Image(act, K), [1..n]);
  orbH := Orbits(Image(act, H), [1..n]);
  idK := []; for i in [1..Length(orbK)] do idK{orbK[i]} := List(orbK[i], x -> i); od;
  idH := []; for i in [1..Length(orbH)] do idH{orbH[i]} := List(orbH[i], x -> i); od;
  step := function(S, orb, id)  # union of the orbits meeting S
    local blocks, T, b;
    blocks := Set(List(S, x -> id[x]));
    T := [];
    for b in blocks do Append(T, orb[b]); od;
    return Set(T);
  end;

  S := [ 1 ];
  # find the point fixed by H that corresponds to the coset H: FactorCosetAction maps H to the stabilizer of 1? check
  if not ForAll(GeneratorsOfGroup(Image(act, H)), g -> 1^g = 1) then
    Error("base point is not 1");
  fi;
  S := step(S, orbK, idK); S := step(S, orbH, idH);
  i := Length(S);
  S := step(S, orbK, idK); S := step(S, orbH, idH);
  return [n, i, Length(S), Length(orbH)];
end;

CosetGraphReport := function(G, H, K)
  local L, dA, dB, a, b;
  L := Intersection(H, K);
  dA := Index(H, L); dB := Index(K, L);
  a := BallSteps(G, H, K);
  b := BallSteps(G, K, H);
  return rec(nA := a[1], nB := b[1], dA := dA, dB := dB, ballA := a{[2,3]}, ballB := b{[2,3]},
             rankA := a[4], rankB := b[4], ok := (a[3] = a[1] and b[3] = b[1]),
             connected := (Group(Concatenation(GeneratorsOfGroup(H), GeneratorsOfGroup(K))) = G));
end;
