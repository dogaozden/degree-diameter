# Batch export of SmallGroup(ORD, id) for id in IDS, in the haarex2/haarex4/qfeas format (identity = element 0, then
# Aut generators as permutations of element indices), to DIR/hx_<ORD>_<id>.txt.
# usage: gap -q -A -c 'ORD:=64;; IDS:=[1..267];; DIR:="q64";;' hx_export_any.g
for id in IDS do
  K := SmallGroup(ORD, id);
  srt := AsSSortedList(K);
  e := One(K);
  elms := Concatenation([e], Filtered(srt, x -> x <> e));
  n := Length(elms);
  pos := List(srt, x -> Position(elms, x));
  idx := x -> pos[PositionSorted(srt, x)] - 1;
  A := AutomorphismGroup(K);
  gens := GeneratorsOfGroup(A);
  FN := Concatenation(DIR, Concatenation("/hx_", String(ORD), "_"), String(id), ".txt");
  out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, n, "\n");
  for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(idx(a * b))), " "), "\n"); od;
  AppendTo(out, Length(gens), "\n");
  for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(Image(g, x)))), " "), "\n"); od;
  CloseStream(out);
  Print("EXPORTED ", id, " |Aut|=", Size(A), "\n");
od;
QUIT;
