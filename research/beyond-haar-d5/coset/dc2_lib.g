SubsOfOrder := function(G, h)
  local reps, x, S, c;
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
