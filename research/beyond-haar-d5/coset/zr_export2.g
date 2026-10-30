# Same session: dc2 file for (G, class HI, class KI) and the action of an element of order R_ORDER on A/B points.
Read("dc2_lib.g");
Hs := SubsOfOrder(G, H_ORDER); H := Hs[HI]; K := Hs[KI];
RA := RightTransversal(G, H); RB := RightTransversal(G, K); nA := Length(RA); nB := Length(RB);
dcs := DoubleCosets(G, H, K);
gens := SmallGeneratingSet(G);
out := OutputTextFile(Concatenation(OUT, ".dc2"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, nA, " ", nB, " ", Length(gens), " ", Length(dcs), "\n");
for s in gens do
  AppendTo(out, JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * s) - 1)), " "), "\n");
  AppendTo(out, JoinStringsWithSeparator(List([1..nB], b -> String(PositionCanonical(RB, RB[b] * s) - 1)), " "), "\n");
od;
for D in dcs do
  g := Representative(D);
  base := Set(List(Elements(H), hh -> PositionCanonical(RB, g^-1 * hh) - 1));
  AppendTo(out, Length(base), " ", JoinStringsWithSeparator(List(base, String), " "), "\n");
od;
CloseStream(out);
r := First(Elements(G), x -> Order(x) = R_ORDER);
out := OutputTextFile(Concatenation(OUT, ".r"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * r) - 1)), " "), "\n");
AppendTo(out, JoinStringsWithSeparator(List([1..nB], b -> String(PositionCanonical(RB, RB[b] * r) - 1)), " "), "\n");
CloseStream(out);
QUIT;
