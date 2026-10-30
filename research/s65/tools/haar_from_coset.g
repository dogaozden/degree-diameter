# G = SmallGroup(ORD, ID) with the order-3 subgroup class 1 (core-free); export dc2 for (H,H), and separately the
# index-3 normal subgroup R (if it meets H trivially) with its table, so that a union S of double cosets gives the
# Haar graph of R with connection set S n R (vl dipole base).  Writes OUT.dc2, OUT_R.txt, OUT_map.g (for step 2).
Read("dc2_lib.g");
G := SmallGroup(ORD, ID); G := Image(IsomorphismPermGroup(G));
H := Filtered(SubsOfOrder(G, 3), X -> Size(Core(G, X)) = 1)[1];
RA := RightTransversal(G, H); nA := Length(RA);
dcs := DoubleCosets(G, H, H); gens := SmallGeneratingSet(G);
out := OutputTextFile(Concatenation(OUT, ".dc2"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, nA, " ", nA, " ", Length(gens), " ", Length(dcs), "\n");
for s in gens do
  AppendTo(out, JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * s) - 1)), " "), "\n");
  AppendTo(out, JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * s) - 1)), " "), "\n");
od;
for D in dcs do
  g := Representative(D);
  base := Set(List(Elements(H), hh -> PositionCanonical(RA, g^-1 * hh) - 1));
  AppendTo(out, Length(base), " ", JoinStringsWithSeparator(List(base, String), " "), "\n");
od;
CloseStream(out);
Rs := Filtered(NormalSubgroups(G), N -> Index(G, N) = 3 and Size(Intersection(N, H)) = 1);
Print("normal index-3 complements of H: ", Length(Rs), "\n");
if Length(Rs) > 0 then
  R := Rs[1]; el := Elements(R); e := Position(el, One(R)); el := Concatenation([el[e]], el{Difference([1..Size(R)], [e])});
  out := OutputTextFile(Concatenation(OUT, "_R.txt"), false); SetPrintFormattingStatus(out, false);
  AppendTo(out, Size(R), "\n");
  for x in el do AppendTo(out, JoinStringsWithSeparator(List(el, y -> String(Position(el, x*y) - 1)), " "), "\n"); od;
  CloseStream(out);
  SaveS := function(ids, fn) local S, o; S := Union(List(ids, i -> AsList(dcs[i + 1])));
    o := OutputTextFile(fn, false); SetPrintFormattingStatus(o, false);
    AppendTo(o, JoinStringsWithSeparator(List(Filtered(S, x -> x in R), x -> String(Position(el, x) - 1)), " "), "\n"); CloseStream(o); end;
fi;
