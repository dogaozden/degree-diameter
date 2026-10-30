SubsOfOrderFast := function(G, h)
  # classes of subgroups of order h for small h without ConjugacyClassesSubgroups: cyclic ones from element classes,
  # V4 from involutions in the centraliser of an involution, S3 from involutions inverting an element of order 3.
  local reps, add, c, x, t, u, S;
  reps := [];
  add := function(S) if Size(S) = h and ForAll(reps, R -> not IsConjugate(G, R, S)) then Add(reps, S); fi; end;
  for c in ConjugacyClasses(G) do
    x := Representative(c);
    if Order(x) = h then add(Subgroup(G, [x])); fi;
    if h = 4 and Order(x) = 2 then
      for u in Filtered(Elements(Centralizer(G, x)), y -> Order(y) = 2 and y <> x) do add(Subgroup(G, [x, u])); od;
    fi;
    if h = 6 and Order(x) = 3 then
      for u in Filtered(Elements(Normalizer(G, Subgroup(G, [x]))), y -> Order(y) = 2 and x^y = x^-1) do add(Subgroup(G, [x, u])); od;
    fi;
  od;
  return reps;
end;
SubsOfOrder := function(G, h)
  local reps, x, S, c;
  if h in [4, 6] or IsPrimeInt(h) then return SubsOfOrderFast(G, h); fi;
  if IsPrimeInt(h) then
    reps := [];
    for c in ConjugacyClasses(G) do
      x := Representative(c);
      if Order(x) = h then
        S := Subgroup(G, [x]);
        if ForAll(reps, R -> not IsConjugate(G, R, S)) then Add(reps, S); fi;
      fi;
    od;
    return reps;
  fi;
  return List(Filtered(ConjugacyClassesSubgroups(G), c -> Size(Representative(c)) = h), Representative);
end;
ExportPairs := function(G, h, OUT)
  local Hs, gens, i, j, H, K, RA, RB, nA, nB, dcs, fn, out, s, D, g, base;
  Hs := SubsOfOrder(G, h);
  # a subgroup with a nontrivial core gives a graph of the smaller group G/core (normal H: a Haar graph of G/H)
  Hs := Filtered(Hs, H -> Size(Core(G, H)) = 1);
  # optional: drop H with a normal complement (a normal subgroup of index h meeting H trivially acts regularly on the
  # cosets, so the coset graph is a Haar graph of it)
  if IsBound(SKIPHAAR) and SKIPHAAR then
    Hs := Filtered(Hs, H -> ForAll(NormalSubgroups(G), N -> Index(G, N) <> h or Size(Intersection(N, H)) > 1));
  fi;
  gens := SmallGeneratingSet(G);
  for i in [1..Length(Hs)] do for j in [i..Length(Hs)] do
    H := Hs[i]; K := Hs[j];
    RA := RightTransversal(G, H); RB := RightTransversal(G, K);
    nA := Length(RA); nB := Length(RB);
    dcs := DoubleCosets(G, H, K);
    fn := Concatenation(OUT, "_", String(i), "_", String(j), ".dc2");
    out := OutputTextFile(fn, false); SetPrintFormattingStatus(out, false);
    AppendTo(out, nA, " ", nB, " ", Length(gens), " ", Length(dcs), "\n");
    for s in gens do
      AppendTo(out, JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * s) - 1)), " "), "\n");
      AppendTo(out, JoinStringsWithSeparator(List([1..nB], b -> String(PositionCanonical(RB, RB[b] * s) - 1)), " "), "\n");
    od;
    if PositionCanonical(RA, One(G)) <> 1 then Error("A-point of H is not 0"); fi;
    for D in dcs do
      g := Representative(D);
      base := Set(List(Elements(H), hh -> PositionCanonical(RB, g^-1 * hh) - 1));
      AppendTo(out, Length(base), " ", JoinStringsWithSeparator(List(base, String), " "), "\n");
    od;
    CloseStream(out);
  od; od;
end;
AffGrp := function(n, q, special)
  local F, V, gens, mats, perms, vecs, M, act;
  F := GF(q); vecs := Elements(F^n);
  if special then mats := GeneratorsOfGroup(SL(n, q)); else mats := GeneratorsOfGroup(GL(n, q)); fi;
  perms := List(mats, M -> PermList(List(vecs, v -> Position(vecs, v * M))));
  Add(perms, PermList(List(vecs, v -> Position(vecs, v + One(F) * Concatenation([1], List([2..n], i -> 0))))));
  return Group(perms);
end;
AffSub := function(q, k)   # F_q : C_k (x -> a x + b, a in the subgroup of order k of F_q^*), as permutations of F_q
  local F, el, w;
  F := GF(q); el := Elements(F); w := PrimitiveRoot(F)^((q - 1) / k);
  return Group(PermList(List(el, x -> Position(el, x + One(F)))), PermList(List(el, x -> Position(el, w * x))));
end;
