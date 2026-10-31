# card c4: export multiplication tables of chosen non-abelian groups (format as tools/gap_tables.g)
# input: LIST = [[N, i], ...]; OUTDIR = "groups"
for pr in LIST do
  N := pr[1]; i := pr[2];
  G := SmallGroup(N, i);
  el := Elements(G);
  e := Position(el, One(G));
  el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
  fn := Concatenation(OUTDIR, "/sg_", String(N), "_", String(i), ".txt");
  out := OutputTextFile(fn, false);
  SetPrintFormattingStatus(out, false);
  AppendTo(out, String(N), "\n");
  for g in el do
    AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n");
  od;
  CloseStream(out);
  PrintTo(Concatenation(OUTDIR, "/sg_", String(N), "_", String(i), ".name"),
          StructureDescription(G), "\n");
od;
QUIT;
