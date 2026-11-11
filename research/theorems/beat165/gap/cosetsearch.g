# Search for bipartite coset graphs Cos(G; H, K) of diameter <= 5 and max degree <= DMAX.
# Sides: right cosets of H and of K; edges: right cosets of L = H n K. Degrees [H:L], [K:L].
# Diameter <= 5 iff HKHKH = G = KHKHK, tested in the coset actions with orbit partitions.
LoadPackage("tomlib");

Closure2 := function(S, orbA, idA, orbB, idB)
  # S -> union of B-orbits meeting S -> union of A-orbits meeting that
  local blocks, T, b;
  blocks := Set(S, x -> idB[x]); T := [];
  for b in blocks do Append(T, orbB[b]); od;
  blocks := Set(T, x -> idA[x]); T := [];
  for b in blocks do Append(T, orbA[b]); od;
  return Set(T);
end;

OrbitIds := function(orbs, n)
  local id, i; id := [];
  for i in [1..Length(orbs)] do id{orbs[i]} := ListWithIdenticalEntries(Length(orbs[i]), i); od;
  return id;
end;

# ball sizes (radius 2, radius 4) around the base point of G/H, alternating K and H
SideTest := function(act, n, H, K)
  local orbH, orbK, idH, idK, S2, S4;
  orbH := Orbits(Image(act, H), [1..n]); idH := OrbitIds(orbH, n);
  orbK := Orbits(Image(act, K), [1..n]); idK := OrbitIds(orbK, n);
  S2 := Closure2([1], orbH, idH, orbK, idK);
  if Length(S2) = n then return [Length(S2), n, Length(orbH)]; fi;
  S4 := Closure2(S2, orbH, idH, orbK, idK);
  return [Length(S2), Length(S4), Length(orbH)];
end;

MooreSide := function(dA, dB) return 1 + dA*(dB-1) + dA*(dB-1)*(dA-1)*(dB-1); end;

found := [];
SearchTom := function(name, DMAX, DMIN, NLO, NHI, MINTOT, logfile)
  local t, G, o, nc, idx, h, H, actH, Ls, L, dA, k, dB, K0, cands, X, g, K1, NL, reps, r, K, a, b, cnt, seen, key, tried;
  t := TableOfMarks(name);
  if t = fail then return; fi;
  G := UnderlyingGroup(t); o := OrdersTom(t); nc := Length(o);
  idx := List(o, x -> Size(G)/x);
  AppendTo(logfile, "== ", name, " |G|=", Size(G), "\n");
  tried := 0;
  for h in [1..nc] do
    if idx[h] < NLO or idx[h] > NHI then continue; fi;
    H := RepresentativeTom(t, h);
    actH := fail;
    Ls := Filtered(LowIndexSubgroups(H, DMAX), L -> Index(H, L) >= DMIN);
    for L in Ls do
      dA := Index(H, L);
      for k in [1..nc] do
        if o[k] mod Size(L) <> 0 then continue; fi;
        dB := o[k]/Size(L);
        if dB < DMIN or dB > DMAX then continue; fi;
        if idx[k] < NLO or idx[k] > NHI or idx[h] + idx[k] < MINTOT then continue; fi;
        if idx[h] > MooreSide(dA, dB) or idx[k] > MooreSide(dB, dA) then continue; fi;
        K0 := RepresentativeTom(t, k);
        cands := Filtered(LowIndexSubgroups(K0, dB), X -> Index(K0, X) = dB and IsConjugate(G, X, L));
        seen := [];
        for X in cands do
          g := RepresentativeAction(G, X, L);
          K1 := K0^g;
          NL := Normalizer(G, L);
          reps := RightTransversal(NL, Normalizer(NL, K1));
          if Length(reps) > 2000 then
            AppendTo(logfile, "  skip: ", Length(reps), " overgroups for h=", h, " k=", k, "\n");
            continue;
          fi;
          for r in reps do
            K := K1^r;
            if Size(Intersection(H, K)) <> Size(L) then continue; fi;
            tried := tried + 1;
            if actH = fail then actH := FactorCosetAction(G, H); fi;
            a := SideTest(actH, idx[h], H, K);
            if a[2] < idx[h] then
              continue;
            fi;
            b := SideTest(FactorCosetAction(G, K), idx[k], K, H);
            AppendTo(logfile, "  A-side ok: h=", h, " k=", k, " dA=", dA, " dB=", dB, " nA=", idx[h], " nB=", idx[k],
              " ballB=", b, "\n");
            if b[2] = idx[k] then
              AppendTo(logfile, "FOUND ", name, " total=", idx[h]+idx[k], " maxdeg=", Maximum(dA,dB),
                " dA=", dA, " dB=", dB, " nA=", idx[h], " nB=", idx[k], " h=", h, " k=", k, "\n");
              Add(found, rec(name := name, G := G, H := H, K := K, dA := dA, dB := dB, nA := idx[h], nB := idx[k]));
            fi;
          od;
        od;
      od;
    od;
  od;
  AppendTo(logfile, "   tried ", tried, "\n");
end;
