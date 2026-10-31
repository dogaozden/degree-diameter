# Compact export for hxexpand.c (job six-five-384): for each id in IDS, DIR/pc_384_<id>.txt holds
#   N k ; k lines: right multiplication by the pc generator g_i as a permutation of element indices ;
#   N lines: the exponent vector of each element (x = g_1^e_1 ... g_k^e_k) ; m ; m lines: Aut generators.
# Element order as in hx_export_batch.g (identity first, then AsSSortedList order), so hxexpand reproduces the
# same haarex input file. Each file is written to DIR/tmp_<id> and renamed when complete.
# usage: gap -q -A -c 'IDS:=[1,2];; DIR:="q";;' hx_export_pc.g
for id in IDS do
  K := SmallGroup(384, id);
  pcgs := Pcgs(K);
  srt := AsSSortedList(K);
  e := One(K);
  elms := Concatenation([e], Filtered(srt, x -> x <> e));
  pos := List(srt, x -> Position(elms, x));
  idx := x -> pos[PositionSorted(srt, x)] - 1;
  A := AutomorphismGroup(K);
  gens := GeneratorsOfGroup(A);
  tmp := Concatenation(DIR, "/tmp_", String(id));
  out := OutputTextFile(tmp, false); SetPrintFormattingStatus(out, false);
  AppendTo(out, Length(elms), " ", Length(pcgs), "\n");
  for g in pcgs do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(x * g))), " "), "\n"); od;
  for x in elms do AppendTo(out, JoinStringsWithSeparator(List(ExponentsOfPcElement(pcgs, x), String), " "), "\n"); od;
  AppendTo(out, Length(gens), "\n");
  for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(Image(g, x)))), " "), "\n"); od;
  CloseStream(out);
  Exec(Concatenation("mv ", tmp, " ", DIR, "/pc_384_", String(id), ".txt"));
od;
QUIT;
