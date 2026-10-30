# Export the bi-coset graph (G, H=K class HI, union SET of double cosets) together with the action of an element r
# of order R_ORDER on the A- and B-points. Output OUT: "nA nB", edges "a b", then "r" + nA images + nB images.
Read("dc2_lib.g");
Hs := SubsOfOrder(G, H_ORDER); H := Hs[HI]; K := Hs[KI];
RA := RightTransversal(G, H); RB := RightTransversal(G, K); nA := Length(RA); nB := Length(RB);
dcs := DoubleCosets(G, H, K);
out := OutputTextFile(OUT, false); SetPrintFormattingStatus(out, false);
AppendTo(out, nA, " ", nB, "\n");
for d in SET do
  D := dcs[d + 1]; g := Representative(D);
  base := Set(List(Elements(H), hh -> PositionCanonical(RB, g^-1 * hh)));
  for a in [1..nA] do for bb in base do
    AppendTo(out, a - 1, " ", PositionCanonical(RB, RB[bb] * RA[a]) - 1, "\n");
  od; od;
od;
r := First(Elements(G), x -> Order(x) = R_ORDER);
AppendTo(out, "r\n", JoinStringsWithSeparator(List([1..nA], a -> String(PositionCanonical(RA, RA[a] * r) - 1)), " "), "\n");
AppendTo(out, JoinStringsWithSeparator(List([1..nB], b -> String(PositionCanonical(RB, RB[b] * r) - 1)), " "), "\n");
CloseStream(out);
QUIT;
