# Bipartite coset graphs Cos(G; H, K') with K' = K^g: sides G/H and G/K', edges G/(H n K').
# Candidates for a pair of subgroups (H, K): the H-orbits of size dA <= DMAX on the cosets G/K
# (point Kg <-> K' = K^g, H n K' = Stab_H(Kg), dA = orbit length); need dB = |K|/|H n K'| <= DMAX.
# Diameter <= 5 iff the radius-4 balls cover both sides: HK'HK'H = G and K'HK'HK' = G.
LoadPackage("tomlib");
if not IsBound(VERBOSE) then VERBOSE := false; fi;

OrbitIds := function(orbs)
  local id, i; id := [];
  for i in [1..Length(orbs)] do id{orbs[i]} := ListWithIdenticalEntries(Length(orbs[i]), i); od;
  return id;
end;

# radius-2 and radius-4 ball sizes around point p, alternating the two orbit partitions (Y first, then X)
Ball4 := function(p, orbX, idX, orbY, idY)
  local S, i, blocks, T, b, n;
  S := [p];
  for i in [1, 2] do
    blocks := Set(S, x -> idY[x]); T := [];
    for b in blocks do Append(T, orbY[b]); od;
    blocks := Set(T, x -> idX[x]); S := [];
    for b in blocks do Append(S, orbX[b]); od;
    if i = 1 then n := Length(S); fi;
  od;
  return [n, Length(S)];
end;

MooreSide := function(dA, dB) return 1 + dA*(dB-1) + dA*(dB-1)*(dA-1)*(dB-1); end;

# H, K subgroups of G with the actions actH on G/H (point 1 = H) and actK on G/K (point 1 = K).
PairSearch := function(G, H, K, actH, actK, nH, nK, DMAX, DMIN, MINTOT, logfile, tag)
  local orbsHonK, orb, dA, p, g, Kp, L, dB, orbH_H, id_H_H, orbKp, idKp, a, b, orbK_K, id_K_K,
        orbHp, idHp, res, ntested;
  res := []; ntested := 0;
  orbsHonK := Orbits(Image(actK, H), [1..nK]);
  orbH_H := fail;
  for orb in orbsHonK do
    dA := Length(orb);
    if dA < DMIN or dA > DMAX then continue; fi;
    # |H n K'| = |H|/dA, so dB = |K| dA/|H| is known before any stabilizer computation
    if (Size(K)*dA) mod Size(H) <> 0 then continue; fi;
    dB := Size(K)*dA/Size(H);
    if dB < DMIN or dB > DMAX then continue; fi;
    if nH > MooreSide(dA, dB) or nK > MooreSide(dB, dA) or nH + nK < MINTOT then continue; fi;
    p := orb[1];
    g := RepresentativeAction(Image(actK), 1, p);
    g := PreImagesRepresentative(actK, g);                  # 1^g = p, i.e. the coset K*g
    Kp := K^g;                                              # stabilizer of the coset K*g
    L := Intersection(H, Kp);
    dB := Size(K)/Size(L);
    if dB < DMIN or dB > DMAX then continue; fi;
    if Size(H)/Size(L) <> dA then Error("orbit/stabilizer mismatch"); fi;
    if nH > MooreSide(dA, dB) or nK > MooreSide(dB, dA) or nH + nK < MINTOT then continue; fi;
    ntested := ntested + 1;
    # A-side: ball around H in G/H, alternating K'-orbits and H-orbits
    if orbH_H = fail then orbH_H := Orbits(Image(actH, H), [1..nH]); id_H_H := OrbitIds(orbH_H); fi;
    orbKp := Orbits(Image(actH, Kp), [1..nH]); idKp := OrbitIds(orbKp);
    a := Ball4(1, orbH_H, id_H_H, orbKp, idKp);
    if VERBOSE or a[2] >= nH/2 then
      AppendTo(logfile, "  cand ", tag, " dA=", dA, " dB=", dB, " nA=", nH, " nB=", nK, " |L|=", Size(L),
        " ballA=", a, " rankA=", Length(orbH_H), "\n");
    fi;
    if a[2] < nH then continue; fi;
    # B-side: ball around K' in G/K: base point p (stabilizer K'), alternating H-orbits and K'-orbits
    orbK_K := Orbits(Image(actK, Kp), [1..nK]); id_K_K := OrbitIds(orbK_K);
    orbHp := Orbits(Image(actK, H), [1..nK]); idHp := OrbitIds(orbHp);
    b := Ball4(p, orbK_K, id_K_K, orbHp, idHp);
    AppendTo(logfile, "  A ok ", tag, " dA=", dA, " dB=", dB, " nA=", nH, " nB=", nK, " ballA=", a, " ballB=", b, "\n");
    if b[2] = nK then
      AppendTo(logfile, "FOUND ", tag, " total=", nH + nK, " dA=", dA, " dB=", dB, " nA=", nH, " nB=", nK, "\n");
      Add(res, rec(H := H, K := Kp, dA := dA, dB := dB, nA := nH, nB := nK));
    fi;
  od;
  return [res, ntested];
end;

# all pairs of TOM classes with indices in [NLO, NHI]
SearchTom2 := function(name, DMAX, DMIN, NLO, NHI, MINTOT, logfile)
  local t, G, o, nc, idx, cls, acts, reps, i, j, h, k, r, tot, found, t0;
  t := TableOfMarks(name);
  if t = fail then AppendTo(logfile, "no table ", name, "\n"); return []; fi;
  G := UnderlyingGroup(t); o := OrdersTom(t); nc := Length(o);
  idx := List(o, x -> Size(G)/x);
  cls := Filtered([1..nc], i -> idx[i] >= NLO and idx[i] <= NHI);
  AppendTo(logfile, "== ", name, " |G|=", Size(G), " classes in range: ", Length(cls), "\n");
  reps := []; acts := [];
  found := []; tot := 0; t0 := Runtime();
  for i in [1..Length(cls)] do
    reps[i] := RepresentativeTom(t, cls[i]);
    acts[i] := fail;
  od;
  for i in [1..Length(cls)] do
    for j in [1..Length(cls)] do
      h := cls[i]; k := cls[j];
      if idx[h] + idx[k] < MINTOT then continue; fi;
      if idx[h] < idx[k] then continue; fi;     # each unordered pair once (A = larger side)
      # some dA in [DMIN..DMAX] must give an integral dB = |K| dA / |H| in [DMIN..DMAX]
      if not ForAny([DMIN..DMAX], dA -> (o[k]*dA) mod o[h] = 0 and o[k]*dA/o[h] >= DMIN and o[k]*dA/o[h] <= DMAX
                     and idx[h] <= MooreSide(dA, o[k]*dA/o[h]) and idx[k] <= MooreSide(o[k]*dA/o[h], dA)) then
        continue;
      fi;
      if acts[i] = fail then acts[i] := FactorCosetAction(G, reps[i]); fi;
      if acts[j] = fail then acts[j] := FactorCosetAction(G, reps[j]); fi;
      r := PairSearch(G, reps[i], reps[j], acts[i], acts[j], idx[h], idx[k], DMAX, DMIN, MINTOT, logfile,
        Concatenation(name, " h=", String(h), " k=", String(k)));
      Append(found, r[1]); tot := tot + r[2];
    od;
  od;
  AppendTo(logfile, "   ", name, ": tested ", tot, " candidates, found ", Length(found), ", ",
    Int((Runtime()-t0)/1000), " s\n");
  return found;
end;
