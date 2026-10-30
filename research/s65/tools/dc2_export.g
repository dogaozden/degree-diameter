# Compact export of bi-coset graph data (format v2) for every pair of conjugacy classes of subgroups of order H_ORDER
# (H_ORDER prime: subgroups = <x> for x of that order; else ConjugacyClassesSubgroups). For each pair (H, K), H <= K:
#   "nA nB ngens ndc", then per generator s: nA images of A-points (cosets H x -> H x s), nB images of B-points,
#   then per double coset H g K: "c b_1 .. b_c" = B-points K y adjacent to the A-point 0 (= H) when S = HgK.
# Usage: gap -q -c 'G:=...; H_ORDER:=3; OUT:="out/x";' dc2_export.g   -> OUT_<i>_<j>.dc2
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
Hs := SubsOfOrder(G, H_ORDER);
gens := GeneratorsOfGroup(G);
if Length(gens) > 4 then gens := SmallGeneratingSet(G); fi;
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
  e1 := PositionCanonical(RA, One(G));
  if e1 <> 1 then Error("A-point of H is not 0"); fi;
  for D in dcs do
    g := Representative(D);
    base := Set(List(Elements(H), hh -> PositionCanonical(RB, g^-1 * hh) - 1));
    AppendTo(out, Length(base), " ", JoinStringsWithSeparator(List(base, String), " "), "\n");
  od;
  CloseStream(out);
od; od;
Print("classes ", Length(Hs), "\n");
QUIT;
