# Batch export for haarex3/haarex4: for each id in IDS (a list), write DIR/hx_384_<id>.txt (multiplication table,
# identity = element 0, then Aut generators as permutations of element indices; format of research/s65/tools/haarex2.g).
# usage: gap -q -A -c 'IDS:=[1,2,3];; DIR:="exp";;' hx_export_batch.g
for id in IDS do
  K := SmallGroup(384, id);
  srt := AsSSortedList(K);
  e := One(K);
  elms := Concatenation([e], Filtered(srt, x -> x <> e));
  n := Length(elms);
  pos := List(srt, x -> Position(elms, x));
  idx := x -> pos[PositionSorted(srt, x)] - 1;
  A := AutomorphismGroup(K);
  gens := GeneratorsOfGroup(A);
  FN := Concatenation(DIR, "/hx_384_", String(id), ".txt");
  out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, n, "\n");
  for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(idx(a * b))), " "), "\n"); od;
  AppendTo(out, Length(gens), "\n");
  for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(Image(g, x)))), " "), "\n"); od;
  CloseStream(out);
  Print("EXPORTED ", id, " |Aut|=", Size(A), "\n");
od;
QUIT;
